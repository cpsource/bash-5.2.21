/* variables_dynamic.c -- dynamic shell variables, extracted from variables.c */
/* Copyright (C) 1987-2022 Free Software Foundation, Inc.

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
   along with Bash.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "config.h"

#include "bashtypes.h"
#include "posixstat.h"
#include "posixtime.h"

#if defined (HAVE_UNISTD_H)
#  include <unistd.h>
#endif

#include <stdio.h>
#include "chartypes.h"
#include "bashansi.h"
#include "bashintl.h"
#include "filecntl.h"

#include "shell.h"
#include "parser.h"
#include "flags.h"
#include "execute_cmd.h"
#include "findcmd.h"
#include "mailcheck.h"
#include "input.h"
#include "hashcmd.h"
#include "pathexp.h"
#include "alias.h"
#include "jobs.h"

#include "version.h"

#include "builtins/getopt.h"
#include "builtins/common.h"
#include "builtins/builtext.h"

#if defined (READLINE)
#  include "bashline.h"
#  include <readline/readline.h>
#else
#  include <tilde/tilde.h>
#endif

#if defined (HISTORY)
#  include "bashhist.h"
#  include <readline/history.h>
#endif /* HISTORY */

#if defined (PROGRAMMABLE_COMPLETION)
#  include "pcomplete.h"
#endif

#include "variables.h"

extern time_t shell_start_time;
extern struct timeval shellstart;
#include "variables_dynamic.h"

/* Forward declarations for static functions in this module */
static SHELL_VAR *null_assign PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
#if defined (ARRAY_VARS)
static SHELL_VAR *null_array_assign PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
#endif
static SHELL_VAR *get_self PARAMS((SHELL_VAR *));

#if defined (ARRAY_VARS)
static SHELL_VAR *init_dynamic_array_var PARAMS((char *, sh_var_value_func_t *, sh_var_assign_func_t *, int));
static SHELL_VAR *init_dynamic_assoc_var PARAMS((char *, sh_var_value_func_t *, sh_var_assign_func_t *, int));
#endif

static inline SHELL_VAR *set_int_value (SHELL_VAR *, intmax_t, int);
static inline SHELL_VAR *set_string_value (SHELL_VAR *, const char *, int);

static SHELL_VAR *assign_seconds PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
static SHELL_VAR *get_seconds PARAMS((SHELL_VAR *));
static SHELL_VAR *init_seconds_var PARAMS((void));

static SHELL_VAR *assign_random PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
static SHELL_VAR *get_random PARAMS((SHELL_VAR *));

static SHELL_VAR *get_urandom PARAMS((SHELL_VAR *));

static SHELL_VAR *assign_lineno PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
static SHELL_VAR *get_lineno PARAMS((SHELL_VAR *));

static SHELL_VAR *assign_subshell PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
static SHELL_VAR *get_subshell PARAMS((SHELL_VAR *));

static SHELL_VAR *get_epochseconds PARAMS((SHELL_VAR *));
static SHELL_VAR *get_epochrealtime PARAMS((SHELL_VAR *));

static SHELL_VAR *get_bashpid PARAMS((SHELL_VAR *));

static SHELL_VAR *get_bash_argv0 PARAMS((SHELL_VAR *));
static SHELL_VAR *assign_bash_argv0 PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
void set_argv0 PARAMS((void));

static SHELL_VAR *get_bash_command PARAMS((SHELL_VAR *));

#if defined (HISTORY)
static SHELL_VAR *get_histcmd PARAMS((SHELL_VAR *));
#endif

#if defined (READLINE)
static SHELL_VAR *get_comp_wordbreaks PARAMS((SHELL_VAR *));
static SHELL_VAR *assign_comp_wordbreaks PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
#endif

#if defined (PUSHD_AND_POPD) && defined (ARRAY_VARS)
static SHELL_VAR *assign_dirstack PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
static SHELL_VAR *get_dirstack PARAMS((SHELL_VAR *));
#endif

#if defined (ARRAY_VARS)
static SHELL_VAR *get_groupset PARAMS((SHELL_VAR *));
#  if defined (DEBUGGER)
static SHELL_VAR *get_bashargcv PARAMS((SHELL_VAR *));
#  endif
static SHELL_VAR *build_hashcmd PARAMS((SHELL_VAR *));
static SHELL_VAR *get_hashcmd PARAMS((SHELL_VAR *));
static SHELL_VAR *assign_hashcmd PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
#  if defined (ALIAS)
static SHELL_VAR *build_aliasvar PARAMS((SHELL_VAR *));
static SHELL_VAR *get_aliasvar PARAMS((SHELL_VAR *));
static SHELL_VAR *assign_aliasvar PARAMS((SHELL_VAR *, char *, arrayind_t, char *));
#  endif
#endif

static SHELL_VAR *get_funcname PARAMS((SHELL_VAR *));
static SHELL_VAR *init_funcname_var PARAMS((void));

/* **************************************************************** */
/*								    */
/*		 	Dynamic Variables			    */
/*								    */
/* **************************************************************** */

/* DYNAMIC VARIABLES

   These are variables whose values are generated anew each time they are
   referenced.  These are implemented using a pair of function pointers
   in the struct variable: assign_func, which is called from bind_variable
   and, if arrays are compiled into the shell, some of the functions in
   arrayfunc.c, and dynamic_value, which is called from find_variable.

   assign_func is called from bind_variable_internal, if
   bind_variable_internal discovers that the variable being assigned to
   has such a function.  The function is called as
	SHELL_VAR *temp = (*(entry->assign_func)) (entry, value, ind)
   and the (SHELL_VAR *)temp is returned as the value of bind_variable.  It
   is usually ENTRY (self).  IND is an index for an array variable, and
   unused otherwise.

   dynamic_value is called from find_variable_internal to return a `new'
   value for the specified dynamic variable.  If this function is NULL,
   the variable is treated as a `normal' shell variable.  If it is not,
   however, then this function is called like this:
	tempvar = (*(var->dynamic_value)) (var);

   Sometimes `tempvar' will replace the value of `var'.  Other times, the
   shell will simply use the string value.  Pretty object-oriented, huh?

   Be warned, though: if you `unset' a special variable, it loses its
   special meaning, even if you subsequently set it.

   The special assignment code would probably have been better put in
   subst.c: do_assignment_internal, in the same style as
   stupidly_hack_special_variables, but I wanted the changes as
   localized as possible.  */

#define INIT_DYNAMIC_VAR(var, val, gfunc, afunc) \
  do \
    { \
      v = bind_variable (var, (val), 0); \
      v->dynamic_value = gfunc; \
      v->assign_func = afunc; \
    } \
  while (0)

#define INIT_DYNAMIC_ARRAY_VAR(var, gfunc, afunc) \
  do \
    { \
      v = make_new_array_variable (var); \
      v->dynamic_value = gfunc; \
      v->assign_func = afunc; \
    } \
  while (0)

#define INIT_DYNAMIC_ASSOC_VAR(var, gfunc, afunc) \
  do \
    { \
      v = make_new_assoc_variable (var); \
      v->dynamic_value = gfunc; \
      v->assign_func = afunc; \
    } \
  while (0)

static SHELL_VAR *
null_assign (SHELL_VAR *self, char *value, arrayind_t unused, char *key)
{
  return (self);
}

#if defined (ARRAY_VARS)
static SHELL_VAR *
null_array_assign (SHELL_VAR *self, char *value, arrayind_t ind, char *key)
{
  return (self);
}
#endif

/* Degenerate `dynamic_value' function; just returns what's passed without
   manipulation. */
static SHELL_VAR *
get_self (SHELL_VAR *self)
{
  return (self);
}

#if defined (ARRAY_VARS)
/* A generic dynamic array variable initializer.  Initialize array variable
   NAME with dynamic value function GETFUNC and assignment function SETFUNC. */
static SHELL_VAR *
init_dynamic_array_var (char *name, sh_var_value_func_t *getfunc, sh_var_assign_func_t *setfunc, int attrs)
{
  SHELL_VAR *v;

  v = find_variable (name);
  if (v)
    return (v);
  INIT_DYNAMIC_ARRAY_VAR (name, getfunc, setfunc);
  if (attrs)
    VSETATTR (v, attrs);
  return v;
}

static SHELL_VAR *
init_dynamic_assoc_var (char *name, sh_var_value_func_t *getfunc, sh_var_assign_func_t *setfunc, int attrs)
{
  SHELL_VAR *v;

  v = find_variable (name);
  if (v)
    return (v);
  INIT_DYNAMIC_ASSOC_VAR (name, getfunc, setfunc);
  if (attrs)
    VSETATTR (v, attrs);
  return v;
}
#endif

/* Set the string value of VAR to the string representation of VALUE.
   Right now this takes an INTMAX_T because that's what itos needs. If
   FLAGS&1, we force the integer attribute on. */
static inline SHELL_VAR *
set_int_value (SHELL_VAR *var, intmax_t value, int flags)
{
  char *p;

  p = itos (value);
  FREE (value_cell (var));
  var_setvalue (var, p);
  if (flags & 1)
    VSETATTR (var, att_integer);
  return (var);
}

static inline SHELL_VAR *
set_string_value (SHELL_VAR *var, const char *value, int flags)
{
  char *p;

  if (value && *value)
    p = savestring (value);
  else
    {
      p = (char *)xmalloc (1);
      p[0] = '\0';
    }
  FREE (value_cell (var));
  var_setvalue (var, p);
  return (var);
}

/* The value of $SECONDS.  This is the number of seconds since shell
   invocation, or, the number of seconds since the last assignment + the
   value of the last assignment. */
static intmax_t seconds_value_assigned;

static SHELL_VAR *
assign_seconds (SHELL_VAR *self, char *value, arrayind_t unused, char *key)
{
  intmax_t nval;
  int expok;

  if (integer_p (self))
    nval = evalexp (value, 0, &expok);
  else
    expok = legal_number (value, &nval);
  seconds_value_assigned = expok ? nval : 0;
  gettimeofday (&shellstart, NULL);
  shell_start_time = shellstart.tv_sec;
  return (set_int_value (self, nval, integer_p (self) != 0));
}

static SHELL_VAR *
get_seconds (SHELL_VAR *var)
{
  time_t time_since_start;
  struct timeval tv;

  gettimeofday(&tv, NULL);
  time_since_start = tv.tv_sec - shell_start_time;
  return (set_int_value (var, seconds_value_assigned + time_since_start, 1));
}

static SHELL_VAR *
init_seconds_var ()
{
  SHELL_VAR *v;

  v = find_variable ("SECONDS");
  if (v)
    {
      if (legal_number (value_cell(v), &seconds_value_assigned) == 0)
	seconds_value_assigned = 0;
    }
  INIT_DYNAMIC_VAR ("SECONDS", (v ? value_cell (v) : (char *)NULL), get_seconds, assign_seconds);
  return v;      
}

/* Functions for $RANDOM and $SRANDOM */

int last_random_value;
static int seeded_subshell = 0;

static SHELL_VAR *
assign_random (SHELL_VAR *self, char *value, arrayind_t unused, char *key)
{
  intmax_t seedval;
  int expok;

  if (integer_p (self))
    seedval = evalexp (value, 0, &expok);
  else
    expok = legal_number (value, &seedval);
  if (expok == 0)
    return (self);
  sbrand (seedval);
  if (subshell_environment)
    seeded_subshell = getpid ();
  return (set_int_value (self, seedval, integer_p (self) != 0));
}

int
get_random_number ()
{
  int rv, pid;

  /* Reset for command and process substitution. */
  pid = getpid ();
  if (subshell_environment && seeded_subshell != pid)
    {
      seedrand ();
      seeded_subshell = pid;
    }

  do
    rv = brand ();
  while (rv == last_random_value);

  return (last_random_value = rv);
}

static SHELL_VAR *
get_random (SHELL_VAR *var)
{
  int rv;

  rv = get_random_number ();
  return (set_int_value (var, rv, 1));
}

static SHELL_VAR *
get_urandom (SHELL_VAR *var)
{
  u_bits32_t rv;

  rv = get_urandom32 ();
  return (set_int_value (var, rv, 1));
}

static SHELL_VAR *
assign_lineno (SHELL_VAR *var, char *value, arrayind_t unused, char *key)
{
  intmax_t new_value;

  if (value == 0 || *value == '\0' || legal_number (value, &new_value) == 0)
    new_value = 0;
  line_number = line_number_base = new_value;
  return (set_int_value (var, line_number, integer_p (var) != 0));
}

/* Function which returns the current line number. */
static SHELL_VAR *
get_lineno (SHELL_VAR *var)
{
  int ln;

  ln = executing_line_number ();
  return (set_int_value (var, ln, 0));
}

static SHELL_VAR *
assign_subshell (SHELL_VAR *var, char *value, arrayind_t unused, char *key)
{
  intmax_t new_value;

  if (value == 0 || *value == '\0' || legal_number (value, &new_value) == 0)
    new_value = 0;
  subshell_level = new_value;
  return var;
}

static SHELL_VAR *
get_subshell (SHELL_VAR *var)
{
  return (set_int_value (var, subshell_level, 0));
}

static SHELL_VAR *
get_epochseconds (SHELL_VAR *var)
{
  intmax_t now;

  now = NOW;
  return (set_int_value (var, now, 0));
}

static SHELL_VAR *
get_epochrealtime (SHELL_VAR *var)
{
  char buf[32];
  struct timeval tv;

  gettimeofday (&tv, NULL);
  snprintf (buf, sizeof (buf), "%u%c%06u", (unsigned)tv.tv_sec,
					   locale_decpoint (),
					   (unsigned)tv.tv_usec);

  return (set_string_value (var, buf, 0));
}

static SHELL_VAR *
get_bashpid (SHELL_VAR *var)
{
  int pid;

  pid = getpid ();
  return (set_int_value (var, pid, 1));
}

static SHELL_VAR *
get_bash_argv0 (SHELL_VAR *var)
{
  return (set_string_value (var, dollar_vars[0], 0));
}

static char *static_shell_name = 0;

static SHELL_VAR *
assign_bash_argv0 (SHELL_VAR *var, char *value, arrayind_t unused, char *key)
{
  size_t vlen;

  if (value == 0)
    return var;

  FREE (dollar_vars[0]);
  dollar_vars[0] = savestring (value);

  /* Need these gyrations because shell_name isn't dynamically allocated */
  vlen = STRLEN (value);
  static_shell_name = xrealloc (static_shell_name, vlen + 1);
  strcpy (static_shell_name, value);
  
  shell_name = static_shell_name;
  return var;
}

void
set_argv0 ()
{
  SHELL_VAR *v;

  v = find_variable ("BASH_ARGV0");
  if (v && imported_p (v))
    assign_bash_argv0 (v, value_cell (v), 0, 0);
}
  
static SHELL_VAR *
get_bash_command (SHELL_VAR *var)
{
  char *p;

  p = the_printed_command_except_trap ? the_printed_command_except_trap : "";
  return (set_string_value (var, p, 0));
}

#if defined (HISTORY)
static SHELL_VAR *
get_histcmd (SHELL_VAR *var)
{
  int n;

  /* Do the same adjustment here we do in parse.y:prompt_history_number,
     assuming that we are in one of two states: decoding this as part of
     the prompt string, in which case we do not want to assume that the
     command has been saved to the history and the history number incremented,
     or the expansion is part of the current command being executed and has
     already been saved to history and the history number incremented.
     Right now we use EXECUTING as the determinant. */
  n = history_number () - executing;
  return (set_int_value (var, n, 0));
}
#endif

#if defined (READLINE)
/* When this function returns, VAR->value points to malloced memory. */
static SHELL_VAR *
get_comp_wordbreaks (SHELL_VAR *var)
{
  /* If we don't have anything yet, assign a default value. */
  if (rl_completer_word_break_characters == 0 && bash_readline_initialized == 0)
    enable_hostname_completion (perform_hostname_completion);

  return (set_string_value (var, rl_completer_word_break_characters, 0));
}

/* When this function returns, rl_completer_word_break_characters points to
   malloced memory. */
static SHELL_VAR *
assign_comp_wordbreaks (SHELL_VAR *self, char *value, arrayind_t unused, char *key)
{
  if (rl_completer_word_break_characters &&
      rl_completer_word_break_characters != rl_basic_word_break_characters)
    free ((void *)rl_completer_word_break_characters);

  rl_completer_word_break_characters = savestring (value);
  return self;
}
#endif /* READLINE */

#if defined (PUSHD_AND_POPD) && defined (ARRAY_VARS)
static SHELL_VAR *
assign_dirstack (SHELL_VAR *self, char *value, arrayind_t ind, char *key)
{
  set_dirstack_element (ind, 1, value);
  return self;
}

static SHELL_VAR *
get_dirstack (SHELL_VAR *self)
{
  ARRAY *a;
  WORD_LIST *l;

  l = get_directory_stack (0);
  a = array_from_word_list (l);
  array_dispose (array_cell (self));
  dispose_words (l);
  var_setarray (self, a);
  return self;
}
#endif /* PUSHD AND POPD && ARRAY_VARS */

#if defined (ARRAY_VARS)
/* We don't want to initialize the group set with a call to getgroups()
   unless we're asked to, but we only want to do it once. */
static SHELL_VAR *
get_groupset (SHELL_VAR *self)
{
  register int i;
  int ng;
  ARRAY *a;
  static char **group_set = (char **)NULL;

  if (group_set == 0)
    {
      group_set = get_group_list (&ng);
      a = array_cell (self);
      for (i = 0; i < ng; i++)
	array_insert (a, i, group_set[i]);
    }
  return (self);
}

#  if defined (DEBUGGER)
static SHELL_VAR *
get_bashargcv (SHELL_VAR *self)
{
  static int self_semaphore = 0;

  /* Backwards compatibility: if we refer to BASH_ARGV or BASH_ARGC at the
     top level without enabling debug mode, and we don't have an instance
     of the variable set, initialize the arg arrays.
     This will already have been done if debugging_mode != 0. */
  if (self_semaphore == 0 && variable_context == 0 && debugging_mode == 0)	/* don't do it for shell functions */
    {
      self_semaphore = 1;
      init_bash_argv ();
      self_semaphore = 0;
    }
  return self;
}
#  endif

static SHELL_VAR *
build_hashcmd (SHELL_VAR *self)
{
  HASH_TABLE *h;
  int i;
  char *k, *v;
  BUCKET_CONTENTS *item;

  h = assoc_cell (self);
  if (h)
    assoc_dispose (h);

  if (hashed_filenames == 0 || HASH_ENTRIES (hashed_filenames) == 0)
    {
      var_setvalue (self, (char *)NULL);
      return self;
    }

  h = assoc_create (hashed_filenames->nbuckets);
  for (i = 0; i < hashed_filenames->nbuckets; i++)
    {
      for (item = hash_items (i, hashed_filenames); item; item = item->next)
	{
	  k = savestring (item->key);
	  v = pathdata(item)->path;
	  assoc_insert (h, k, v);
	}
    }

  var_setvalue (self, (char *)h);
  return self;
}

static SHELL_VAR *
get_hashcmd (SHELL_VAR *self)
{
  build_hashcmd (self);
  return (self);
}

static SHELL_VAR *
assign_hashcmd (SHELL_VAR *self, char *value, arrayind_t ind, char *key)
{
#if defined (RESTRICTED_SHELL)
  char *full_path;

  if (restricted)
    {
      if (strchr (value, '/'))
	{
	  sh_restricted (value);
	  return (SHELL_VAR *)NULL;
	}
      /* If we are changing the hash table in a restricted shell, make sure the
	 target pathname can be found using a $PATH search. */
      full_path = find_user_command (value);
      if (full_path == 0 || *full_path == 0 || executable_file (full_path) == 0)
	{
	  sh_notfound (value);
	  free (full_path);
	  return ((SHELL_VAR *)NULL);
	}
      free (full_path);
    }
#endif
  phash_insert (key, value, 0, 0);
  return (build_hashcmd (self));
}

#if defined (ALIAS)
static SHELL_VAR *
build_aliasvar (SHELL_VAR *self)
{
  HASH_TABLE *h;
  int i;
  char *k, *v;
  BUCKET_CONTENTS *item;

  h = assoc_cell (self);
  if (h)
    assoc_dispose (h);

  if (aliases == 0 || HASH_ENTRIES (aliases) == 0)
    {
      var_setvalue (self, (char *)NULL);
      return self;
    }

  h = assoc_create (aliases->nbuckets);
  for (i = 0; i < aliases->nbuckets; i++)
    {
      for (item = hash_items (i, aliases); item; item = item->next)
	{
	  k = savestring (item->key);
	  v = ((alias_t *)(item->data))->value;
	  assoc_insert (h, k, v);
	}
    }

  var_setvalue (self, (char *)h);
  return self;
}

static SHELL_VAR *
get_aliasvar (SHELL_VAR *self)
{
  build_aliasvar (self);
  return (self);
}

static SHELL_VAR *
assign_aliasvar (SHELL_VAR *self, char *value, arrayind_t ind, char *key)
{
  if (legal_alias_name (key, 0) == 0)
    {
       report_error (_("`%s': invalid alias name"), key);
       return (self);
    }
  add_alias (key, value);
  return (build_aliasvar (self));
}
#endif /* ALIAS */

#endif /* ARRAY_VARS */

/* If ARRAY_VARS is not defined, this just returns the name of any
   currently-executing function.  If we have arrays, it's a call stack. */
static SHELL_VAR *
get_funcname (SHELL_VAR *self)
{
#if ! defined (ARRAY_VARS)
  if (variable_context && this_shell_function)
    return (set_string_value (self, this_shell_function->name, 0));
#endif
  return (self);
}

void
make_funcname_visible (int on_or_off)
{
  SHELL_VAR *v;

  v = find_variable ("FUNCNAME");
  if (v == 0 || v->dynamic_value == 0)
    return;

  if (on_or_off)
    VUNSETATTR (v, att_invisible);
  else
    VSETATTR (v, att_invisible);
}

static SHELL_VAR *
init_funcname_var ()
{
  SHELL_VAR *v;

  v = find_variable ("FUNCNAME");
  if (v)
    return v;
#if defined (ARRAY_VARS)
  INIT_DYNAMIC_ARRAY_VAR ("FUNCNAME", get_funcname, null_array_assign);
#else
  INIT_DYNAMIC_VAR ("FUNCNAME", (char *)NULL, get_funcname, null_assign);
#endif
  VSETATTR (v, att_invisible|att_noassign);
  return v;
}

void
initialize_dynamic_variables ()
{
  SHELL_VAR *v;

  v = init_seconds_var ();

  INIT_DYNAMIC_VAR ("BASH_ARGV0", (char *)NULL, get_bash_argv0, assign_bash_argv0);

  INIT_DYNAMIC_VAR ("BASH_COMMAND", (char *)NULL, get_bash_command, (sh_var_assign_func_t *)NULL);
  INIT_DYNAMIC_VAR ("BASH_SUBSHELL", (char *)NULL, get_subshell, assign_subshell);

  INIT_DYNAMIC_VAR ("RANDOM", (char *)NULL, get_random, assign_random);
  VSETATTR (v, att_integer);
  INIT_DYNAMIC_VAR ("SRANDOM", (char *)NULL, get_urandom, (sh_var_assign_func_t *)NULL);
  VSETATTR (v, att_integer);  
  INIT_DYNAMIC_VAR ("LINENO", (char *)NULL, get_lineno, assign_lineno);
  VSETATTR (v, att_regenerate);

  INIT_DYNAMIC_VAR ("BASHPID", (char *)NULL, get_bashpid, null_assign);
  VSETATTR (v, att_integer);

  INIT_DYNAMIC_VAR ("EPOCHSECONDS", (char *)NULL, get_epochseconds, null_assign);
  VSETATTR (v, att_regenerate);
  INIT_DYNAMIC_VAR ("EPOCHREALTIME", (char *)NULL, get_epochrealtime, null_assign);
  VSETATTR (v, att_regenerate);

#if defined (HISTORY)
  INIT_DYNAMIC_VAR ("HISTCMD", (char *)NULL, get_histcmd, (sh_var_assign_func_t *)NULL);
  VSETATTR (v, att_integer);
#endif

#if defined (READLINE)
  INIT_DYNAMIC_VAR ("COMP_WORDBREAKS", (char *)NULL, get_comp_wordbreaks, assign_comp_wordbreaks);
#endif

#if defined (PUSHD_AND_POPD) && defined (ARRAY_VARS)
  v = init_dynamic_array_var ("DIRSTACK", get_dirstack, assign_dirstack, 0);
#endif /* PUSHD_AND_POPD && ARRAY_VARS */

#if defined (ARRAY_VARS)
  v = init_dynamic_array_var ("GROUPS", get_groupset, null_array_assign, att_noassign);

#  if defined (DEBUGGER)
  v = init_dynamic_array_var ("BASH_ARGC", get_bashargcv, null_array_assign, att_noassign|att_nounset);
  v = init_dynamic_array_var ("BASH_ARGV", get_bashargcv, null_array_assign, att_noassign|att_nounset);
#  endif /* DEBUGGER */
  v = init_dynamic_array_var ("BASH_SOURCE", get_self, null_array_assign, att_noassign|att_nounset);
  v = init_dynamic_array_var ("BASH_LINENO", get_self, null_array_assign, att_noassign|att_nounset);

  v = init_dynamic_assoc_var ("BASH_CMDS", get_hashcmd, assign_hashcmd, att_nofree);
#  if defined (ALIAS)
  v = init_dynamic_assoc_var ("BASH_ALIASES", get_aliasvar, assign_aliasvar, att_nofree);
#  endif
#endif

  v = init_funcname_var ();
}

