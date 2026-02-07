/* Secure shell module for sbash -- header.
   Adapted from the glibc dl-secure module.

   Copyright (C) 2024 Free Software Foundation, Inc.

   This file is part of GNU Bash, the Bourne Again SHell.

   Bash is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   Bash is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with Bash.  If not, see <http://www.gnu.org/licenses/>.  */

#ifndef _SBASH_SECURE_H
#define _SBASH_SECURE_H

#include <stdint.h>
#include <stddef.h>

/* ELF types -- use the native pointer size to select 32/64.  */
#include <elf.h>

/* Policy enforcement modes.  */
enum sbash_secure_mode
{
  SBASH_SECURE_OFF     = 0,   /* No enforcement.  */
  SBASH_SECURE_AUDIT   = 1,   /* Log violations but allow.  */
  SBASH_SECURE_ENFORCE = 2    /* Block violations.  */
};

/* Maximum number of policy rules.  */
#define SBASH_SECURE_MAX_RULES 256

/* Maximum number of hash whitelist entries.  */
#define SBASH_SECURE_MAX_HASHES 256

/* SHA-256 digest size in bytes.  */
#define SBASH_SECURE_HASH_SIZE 32

/* HMAC key size in bytes.  */
#define SBASH_SECURE_KEY_SIZE 32

/* ELF note name for embedded signatures.  */
#define SBASH_SECURE_NOTE_NAME "DL-Secure"

/* ELF note type for HMAC-SHA256 signature.  */
#define SBASH_SECURE_NOTE_TYPE 0x53454300  /* "SEC\0" */

/* Rule types for path matching.  */
enum sbash_secure_rule_type
{
  SBASH_SECURE_ALLOW_PATH  = 0,
  SBASH_SECURE_DENY_PATH   = 1,
  SBASH_SECURE_REQUIRE_SIG = 2
};

/* A single path-matching rule.  */
struct sbash_secure_rule
{
  enum sbash_secure_rule_type type;
  const char *pattern;          /* Glob pattern (points into mmap'd config).  */
};

/* A SHA-256 hash whitelist entry.  */
struct sbash_secure_hash_entry
{
  uint8_t hash[SBASH_SECURE_HASH_SIZE];
  const char *path;             /* Optional path hint (points into config).  */
};

/* Global policy state.  */
struct sbash_secure_policy
{
  enum sbash_secure_mode mode;
  int initialized;

  /* HMAC key for signature verification.  */
  uint8_t hmac_key[SBASH_SECURE_KEY_SIZE];
  int has_hmac_key;

  /* Path-based rules (processed in order, deny takes precedence).  */
  struct sbash_secure_rule rules[SBASH_SECURE_MAX_RULES];
  int nrules;

  /* SHA-256 hash whitelist.  */
  struct sbash_secure_hash_entry hashes[SBASH_SECURE_MAX_HASHES];
  int nhashes;

  /* Pointer to mmap'd config file (kept alive for string references).  */
  void *config_data;
  size_t config_size;
};

/* Initialize the secure shell policy by parsing /etc/sbash.secure.
   Called once from main() when the shell is invoked as sbash.  */
void sbash_secure_init (void);

/* Check whether an external command is allowed to be executed.
   PATH is the resolved file path.
   Returns 0 if allowed, -1 if denied.  */
int sbash_secure_check (const char *path);

/* Return nonzero if secure shell policy is loaded and mode != OFF.  */
int sbash_secure_active (void);

#endif /* _SBASH_SECURE_H */
