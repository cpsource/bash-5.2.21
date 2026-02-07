# sbash -- Secure Bash

sbash is a security-policy-enforcing variant of bash. Like `rbash` (restricted
bash), it is activated by invoking the shell under a special name. When bash is
invoked as `sbash`, it reads a policy file and gates execution of external
commands against that policy.

A combined mode, `srbash`, enables both secure and restricted modes
simultaneously.

## Invocation

sbash is not a separate binary. It is the same `bash` executable invoked via a
symlink:

    ln -s bash sbash       # secure shell
    ln -s bash srbash      # secure + restricted shell

The name is checked against `argv[0]`, following the same mechanism as rbash.
A leading `-` (login shell) is stripped before comparison, so `-sbash` also
activates secure mode.

    ./sbash                 # interactive secure shell
    ./sbash -c 'ls /tmp'   # run a command under secure policy
    ./sbash script.sh       # run a script under secure policy

When no policy file exists (`/etc/sbash.secure`), sbash operates identically to
normal bash -- all commands are allowed.

## What is gated

Only `execve()` of external binaries is subject to policy checks. The following
are **not** gated:

- Shell builtins (`cd`, `echo`, `read`, `type`, `test`, etc.)
- Shell functions
- Sourced files (`. file` / `source file`)
- Variable assignments, redirections, pipes, and other shell syntax

## Policy file format

The policy file is `/etc/sbash.secure`. It is a plain text file with one
directive per line. Lines starting with `#` are comments. The path is hardcoded
and cannot be overridden by environment variables.

### Directives

    mode <off|audit|enforce>

Sets the enforcement mode:
- `off` -- no enforcement (default when directive is absent)
- `audit` -- log policy violations to stderr and syslog, but allow execution
- `enforce` -- block execution of commands that violate policy

---

    allow-path <glob>

Allow execution of commands whose resolved path matches the glob pattern.
Only `*` is supported as a wildcard.

    allow-path /usr/bin/*
    allow-path /usr/sbin/*
    allow-path /bin/*

---

    deny-path <glob>

Deny execution of commands whose resolved path matches the glob pattern.
Deny rules take precedence over all other rules (including hash whitelist).

    deny-path /tmp/*
    deny-path /home/*/.*

---

    require-sig <glob>

Require a valid HMAC-SHA256 signature (embedded as an ELF `.note.dl-secure`
section) for commands matching the glob. Use with `hmac-key`.

    require-sig /usr/local/bin/*

---

    hmac-key <64 hex characters>

Set the 256-bit HMAC key used to verify signatures. Required for `require-sig`
rules to function.

    hmac-key 0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef

---

    allow-hash sha256:<64 hex chars> [<path>]

Whitelist a specific binary by the SHA-256 hash of its ELF PT_LOAD segments.
The optional path is a hint for documentation; matching is by hash only.

    allow-hash sha256:abcdef0123456789... /usr/bin/special-tool

### Example policy

    # /etc/sbash.secure
    mode enforce

    # Standard system paths
    allow-path /usr/bin/*
    allow-path /usr/sbin/*
    allow-path /bin/*
    allow-path /sbin/*

    # Block execution from writable locations
    deny-path /tmp/*
    deny-path /var/tmp/*
    deny-path /home/*/.*
    deny-path /dev/shm/*

    # Require signed binaries in /usr/local
    hmac-key 0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
    require-sig /usr/local/bin/*

## Policy evaluation order

When a command is about to be executed, the resolved path is checked as follows:

1. **deny-path** -- if any deny-path glob matches, the command is denied
   (enforce) or logged (audit). Deny rules are absolute and override everything.
2. **allow-hash** -- if the SHA-256 hash of the binary's PT_LOAD segments
   matches a whitelist entry, the command is allowed.
3. **require-sig** -- if a require-sig glob matches, the binary must contain a
   valid `.note.dl-secure` ELF note with an HMAC-SHA256 signature. If
   verification fails, the command is denied (enforce) or logged (audit).
4. **allow-path** -- if any allow-path glob matches, the command is allowed.
5. **No rule matched** -- in enforce mode, the command is denied. In audit mode,
   it is logged and allowed.

## Interception points

Policy checks occur at two points in the execution path:

- **`execute_disk_command()`** -- after path resolution, before fork+exec. This
  is the primary check for normal command execution.
- **`shell_execve()`** -- defense-in-depth check that catches the `exec` builtin
  and `#!` script fallback paths.

## srbash -- secure + restricted

When invoked as `srbash`, both secure shell mode and restricted shell mode are
activated. This combines the security policy enforcement of sbash with the
restrictions of rbash:

- All rbash restrictions apply (no `cd`, no setting `PATH`, no `/` in command
  names, no redirecting output, etc.)
- All sbash policy checks apply on top of that

## ELF signature format

sbash uses the same signature format as the glibc dl-secure module. Signatures
are embedded as an ELF note section named `.note.dl-secure` with:

- Note name: `DL-Secure`
- Note type: `0x53454300`
- Descriptor: 32-byte HMAC-SHA256 over the SHA-256 hash of all PT_LOAD segments

The `elf-sign.py` tool from the glibc dl-secure project can be used to sign
binaries and compute hashes:

    elf-sign.py --sign --key <keyfile> /usr/local/bin/mytool
    elf-sign.py --hash /usr/bin/ls

## Build

Configure with `--enable-secure-shell`:

    mkdir build && cd build
    ../configure --enable-secure-shell
    make

The `sbash` and `srbash` symlinks are created automatically by `make install`.

To disable at build time:

    ../configure --disable-secure-shell
