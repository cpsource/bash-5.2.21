# rbash -- Restricted Bash

rbash is a restricted mode of bash that provides a more controlled execution
environment than the standard shell. It is activated by invoking bash under
the name `rbash`, or by supplying the `--restricted` or `-r` option at
invocation.

## Invocation

rbash is not a separate binary. It is the same `bash` executable invoked via
a symlink or renamed copy:

    ln -s bash rbash

    ./rbash                   # interactive restricted shell
    ./rbash -c 'echo hello'   # run command in restricted mode
    bash -r                   # same effect via flag
    bash --restricted          # same effect via long option

## Restrictions

When running in restricted mode, the following operations are disallowed:

- **Changing directories** with the `cd` builtin.

- **Setting or unsetting** the `SHELL`, `PATH`, `HISTFILE`, `ENV`, or
  `BASH_ENV` variables. These are made read-only.

- **Specifying commands containing slashes.** Command names with `/` are
  rejected, preventing direct execution of binaries by path (e.g.,
  `/usr/bin/vim` is denied, but `vim` works if it is in `PATH`).

- **Specifying filenames containing slashes** as arguments to the `.` (`source`),
  `history -r`, or `hash -p` builtins.

- **Importing function definitions** from the shell environment at startup.

- **Parsing the value of `SHELLOPTS`** from the shell environment at startup.

- **Redirecting output** using the `>`, `>|`, `<>`, `>&`, `&>`, or `>>`
  redirection operators.

- **Using the `exec` builtin** to replace the shell with another command.

- **Adding or deleting builtin commands** with the `-f` and `-d` options to
  the `enable` builtin.

- **Using the `-p` option** to the `command` builtin.

- **Turning off restricted mode** with `set +r` or `set +o restricted`.

## Startup behavior

Restrictions are enforced **after** the startup files (`.bash_profile`,
`.bashrc`, etc.) have been read and executed. This allows the administrator to
set up the restricted environment (e.g., setting `PATH` to a controlled value)
in the startup files before the restrictions take effect.

When a command that is found to be a shell script is executed, rbash turns off
any restrictions in the child shell spawned to execute the script.

## Security considerations

The restricted shell mode is only one component of a useful restricted
environment. It should be accompanied by:

- Setting `PATH` to a directory containing only a small set of approved
  commands.
- Changing the current directory to a non-writable directory after login.
- Preventing the restricted shell from executing shell scripts (since scripts
  run in an unrestricted child shell).
- Cleaning the environment of variables that cause programs to modify their
  behavior (e.g., `EDITOR`, `PAGER`, `LD_PRELOAD`).
- Ensuring that no command available via `PATH` provides a shell escape
  (e.g., `vi`, `more`, `less`, `man`, `awk`, `python`, `perl`, etc.).

rbash is not a security sandbox. A knowledgeable user can break out of the
restricted environment if any available command offers a shell escape, an editor
with `!command` support, or the ability to write arbitrary files. It is a
policy-enforcement convenience, not a confinement mechanism.

## Build

rbash support is enabled by default. To disable it at build time:

    ../configure --disable-restricted

## See also

- `bash(1)` manual, section "RESTRICTED SHELL"
- [GNU Bash Manual: The Restricted Shell](https://www.gnu.org/software/bash/manual/html_node/The-Restricted-Shell.html)
