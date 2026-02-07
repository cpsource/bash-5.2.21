/* variables.c -- Functions for hacking shell variables. */

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

#if defined (__QNX__)
#  if defined (__QNXNTO__)
#    include <sys/netmgr.h>
#  else
#    include <sys/vc.h>
#  endif /* !__QNXNTO__ */
#endif /* __QNX__ */

#if defined (HAVE_UNISTD_H)
#  include <unistd.h>
#endif

#include <stdio.h>
#include "chartypes.h"
#if defined (HAVE_PWD_H)
#  include <pwd.h>
#endif
#include "bashansi.h"
#include "bashintl.h"
#include "filecntl.h"

#define NEED_XTRACE_SET_DECL

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


#include "variables_init.h"
#include "variables_dynamic.h"
#include "variables_export.h"
#include "variables_scope.h"
#include "variables_special.h"

#define VARIABLES_HASH_BUCKETS	1024	/* must be power of two */
#define FUNCTIONS_HASH_BUCKETS	512
#define TEMPENV_HASH_BUCKETS	4	/* must be power of two */

#define BASHFUNC_PREFIX		"BASH_FUNC_"
#define BASHFUNC_PREFLEN	10	/* == strlen(BASHFUNC_PREFIX */
#define BASHFUNC_SUFFIX		"%%"
#define BASHFUNC_SUFFLEN	2	/* == strlen(BASHFUNC_SUFFIX) */

#if ARRAY_EXPORT
#define BASHARRAY_PREFIX	"BASH_ARRAY_"
#define BASHARRAY_PREFLEN	11
#define BASHARRAY_SUFFIX	"%%"
#define BASHARRAY_SUFFLEN	2

#define BASHASSOC_PREFIX	"BASH_ASSOC_"
#define BASHASSOC_PREFLEN	11
#define BASHASSOC_SUFFIX	"%%"	/* needs to be the same as BASHARRAY_SUFFIX */
#define BASHASSOC_SUFFLEN	2
#endif

/* flags for find_variable_internal */

#define FV_FORCETEMPENV		0x01
#define FV_SKIPINVISIBLE	0x02
#define FV_NODYNAMIC		0x04

extern char **environ;

/* Variables used here and defined in other files. */
extern time_t shell_start_time;
extern struct timeval shellstart;

/* The list of shell variables that the user has created at the global
   scope, or that came from the environment. */
VAR_CONTEXT *global_variables = (VAR_CONTEXT *)NULL;

/* The current list of shell variables, including function scopes */
VAR_CONTEXT *shell_variables = (VAR_CONTEXT *)NULL;

/* The list of shell functions that the user has created, or that came from
   the environment. */
HASH_TABLE *shell_functions = (HASH_TABLE *)NULL;

HASH_TABLE *invalid_env = (HASH_TABLE *)NULL;

#if defined (DEBUGGER)
/* The table of shell function definitions that the user defined or that
   came from the environment. */
HASH_TABLE *shell_function_defs = (HASH_TABLE *)NULL;
#endif

/* The current variable context.  This is really a count of how deep into
   executing functions we are. */
int variable_context = 0;

/* If non-zero, local variables inherit values and attributes from a variable
   with the same name at a previous scope. */
int localvar_inherit = 0;

/* If non-zero, calling `unset' on local variables in previous scopes marks
   them as invisible so lookups find them unset. This is the same behavior
   as local variables in the current local scope. */
int localvar_unset = 0;

/* The set of shell assignments which are made only in the environment
   for a single command. */
HASH_TABLE *temporary_env = (HASH_TABLE *)NULL;

/* Set to non-zero if an assignment error occurs while putting variables
   into the temporary environment. */
int tempenv_assign_error;

/* Some funky variables which are known about specially.  Here is where
   "$*", "$1", and all the cruft is kept. */
char *dollar_vars[10];
WORD_LIST *rest_of_args = (WORD_LIST *)NULL;
int posparam_count = 0;

/* The value of $$. */
pid_t dollar_dollar_pid;

/* Non-zero means that we have to remake EXPORT_ENV. */
int array_needs_making = 1;

/* The number of times BASH has been executed.  This is set
   by initialize_variables (). */
int shell_level = 0;

/* An array which is passed to commands as their environment.  It is
   manufactured from the union of the initial environment and the
   shell variables that are marked for export. */
char **export_env = (char **)NULL;


SHELL_VAR nameref_invalid_value;
static SHELL_VAR nameref_maxloop_value;

static HASH_TABLE *last_table_searched;	/* hash_lookup sets this */
static VAR_CONTEXT *last_context_searched;


/* Some forward declarations. */
SHELL_VAR *bind_invalid_envvar PARAMS((const char *, char *, int));

static int var_sametype PARAMS((SHELL_VAR *, SHELL_VAR *));

SHELL_VAR *hash_lookup PARAMS((const char *, HASH_TABLE *));
static SHELL_VAR *new_shell_variable PARAMS((const char *));
static SHELL_VAR *make_new_variable PARAMS((const char *, HASH_TABLE *));
SHELL_VAR *bind_variable_internal PARAMS((const char *, char *, HASH_TABLE *, int, int));

static void dispose_variable_value PARAMS((SHELL_VAR *));
void free_variable_hash_data PARAMS((PTR_T));

static VARLIST *vlist_alloc PARAMS((int));
static VARLIST *vlist_realloc PARAMS((VARLIST *, int));
static void vlist_add PARAMS((VARLIST *, SHELL_VAR *, int));

void flatten PARAMS((HASH_TABLE *, sh_var_map_func_t *, VARLIST *, int));

static int qsort_var_comp PARAMS((SHELL_VAR **, SHELL_VAR **));

static SHELL_VAR **vapply PARAMS((sh_var_map_func_t *));
static SHELL_VAR **fapply PARAMS((sh_var_map_func_t *));

static int visible_var PARAMS((SHELL_VAR *));
int visible_and_exported PARAMS((SHELL_VAR *));
int export_environment_candidate PARAMS((SHELL_VAR *));
static int local_and_exported PARAMS((SHELL_VAR *));
static int visible_variable_in_context PARAMS((SHELL_VAR *));
static int variable_in_context PARAMS((SHELL_VAR *));
#if defined (ARRAY_VARS)
static int visible_array_vars PARAMS((SHELL_VAR *));
#endif

SHELL_VAR *find_variable_internal PARAMS((const char *, int));

static SHELL_VAR *find_nameref_at_context PARAMS((SHELL_VAR *, VAR_CONTEXT *));
static SHELL_VAR *find_variable_nameref_context PARAMS((SHELL_VAR *, VAR_CONTEXT *, VAR_CONTEXT **));
static SHELL_VAR *find_variable_last_nameref_context PARAMS((SHELL_VAR *, VAR_CONTEXT *, VAR_CONTEXT **));

/* Set $HOME to the information in the password file if we didn't get
   it from the environment. */

/* This function is not static so the tilde and readline libraries can
   use it. */
char *
sh_get_home_dir ()
{
  if (current_user.home_dir == 0)
    get_current_user_info ();
  return current_user.home_dir;
}


/* **************************************************************** */
/*								    */
/*		Retrieving variables and values			    */
/*								    */
/* **************************************************************** */

#if 0	/* not yet */
int
var_isset (SHELL_VAR *var)
{
  return (var->value != 0);
}

int
var_isunset (SHELL_VAR *var)
{
  return (var->value == 0);
}
#endif

/* How to get a pointer to the shell variable or function named NAME.
   HASHED_VARS is a pointer to the hash table containing the list
   of interest (either variables or functions). */

SHELL_VAR *
hash_lookup (const char *name, HASH_TABLE *hashed_vars)
{
  BUCKET_CONTENTS *bucket;

  bucket = hash_search (name, hashed_vars, 0);
  /* If we find the name in HASHED_VARS, set LAST_TABLE_SEARCHED to that
     table. */
  if (bucket)
    last_table_searched = hashed_vars;
  return (bucket ? (SHELL_VAR *)bucket->data : (SHELL_VAR *)NULL);
}

SHELL_VAR *
var_lookup (const char *name, VAR_CONTEXT *vcontext)
{
  VAR_CONTEXT *vc;
  SHELL_VAR *v;

  v = (SHELL_VAR *)NULL;
  for (vc = vcontext; vc; vc = vc->down)
    if (v = hash_lookup (name, vc->table))
      break;

  return v;
}

/* Look up the variable entry named NAME.  If SEARCH_TEMPENV is non-zero,
   then also search the temporarily built list of exported variables.
   The lookup order is:
	temporary_env
	shell_variables list
*/

SHELL_VAR *
find_variable_internal (const char *name, int flags)
{
  SHELL_VAR *var;
  int search_tempenv, force_tempenv;
  VAR_CONTEXT *vc;

  var = (SHELL_VAR *)NULL;

  force_tempenv = (flags & FV_FORCETEMPENV);

  /* If explicitly requested, first look in the temporary environment for
     the variable.  This allows constructs such as "foo=x eval 'echo $foo'"
     to get the `exported' value of $foo.  This happens if we are executing
     a function or builtin, or if we are looking up a variable in a
     "subshell environment". */
  search_tempenv = force_tempenv || (expanding_redir == 0 && subshell_environment);

  if (search_tempenv && temporary_env)		
    var = hash_lookup (name, temporary_env);

  if (var == 0)
    {
      if ((flags & FV_SKIPINVISIBLE) == 0)
	var = var_lookup (name, shell_variables);
      else
	{
	  /* essentially var_lookup expanded inline so we can check for
	     att_invisible */
	  for (vc = shell_variables; vc; vc = vc->down)
	    {
	      var = hash_lookup (name, vc->table);
	      if (var && invisible_p (var))
		var = 0;
	      if (var)
		break;
	    }
	}
    }

  if (var == 0)
    return ((SHELL_VAR *)NULL);

  return (var->dynamic_value ? (*(var->dynamic_value)) (var) : var);
}

/* Look up and resolve the chain of nameref variables starting at V all the
   way to NULL or non-nameref. */
SHELL_VAR *
find_variable_nameref (SHELL_VAR *v)
{
  int level, flags;
  char *newname;
  SHELL_VAR *orig, *oldv;

  level = 0;
  orig = v;
  while (v && nameref_p (v))
    {
      level++;
      if (level > NAMEREF_MAX)
	return ((SHELL_VAR *)0);	/* error message here? */
      newname = nameref_cell (v);
      if (newname == 0 || *newname == '\0')
	return ((SHELL_VAR *)0);
      oldv = v;
      flags = 0;
      if (expanding_redir == 0 && (assigning_in_environment || executing_builtin))
	flags |= FV_FORCETEMPENV;
      /* We don't handle array subscripts here. */
      v = find_variable_internal (newname, flags);
      if (v == orig || v == oldv)
	{
	  internal_warning (_("%s: circular name reference"), orig->name);
#if 1
	  /* XXX - provisional change - circular refs go to
	     global scope for resolution, without namerefs. */
	  if (variable_context && v->context)
	    return (find_global_variable_noref (v->name));
	  else
#endif
	  return ((SHELL_VAR *)0);
	}
    }
  return v;
}

/* Resolve the chain of nameref variables for NAME.  XXX - could change later */
SHELL_VAR *
find_variable_last_nameref (const char *name, int vflags)
{
  SHELL_VAR *v, *nv;
  char *newname;
  int level, flags;

  nv = v = find_variable_noref (name);
  level = 0;
  while (v && nameref_p (v))
    {
      level++;
      if (level > NAMEREF_MAX)
        return ((SHELL_VAR *)0);	/* error message here? */
      newname = nameref_cell (v);
      if (newname == 0 || *newname == '\0')
	return ((vflags && invisible_p (v)) ? v : (SHELL_VAR *)0);
      nv = v;
      flags = 0;
      if (expanding_redir == 0 && (assigning_in_environment || executing_builtin))
	flags |= FV_FORCETEMPENV;
      /* We don't accommodate array subscripts here. */
      v = find_variable_internal (newname, flags);
    }
  return nv;
}

/* Resolve the chain of nameref variables for NAME.  XXX - could change later */
SHELL_VAR *
find_global_variable_last_nameref (const char *name, int vflags)
{
  SHELL_VAR *v, *nv;
  char *newname;
  int level;

  nv = v = find_global_variable_noref (name);
  level = 0;
  while (v && nameref_p (v))
    {
      level++;
      if (level > NAMEREF_MAX)
        return ((SHELL_VAR *)0);	/* error message here? */
      newname = nameref_cell (v);
      if (newname == 0 || *newname == '\0')
	return ((vflags && invisible_p (v)) ? v : (SHELL_VAR *)0);
      nv = v;
      /* We don't accommodate array subscripts here. */
      v = find_global_variable_noref (newname);
    }
  return nv;
}

static SHELL_VAR *
find_nameref_at_context (SHELL_VAR *v, VAR_CONTEXT *vc)
{
  SHELL_VAR *nv, *nv2;
  char *newname;
  int level;

  nv = v;
  level = 1;
  while (nv && nameref_p (nv))
    {
      level++;
      if (level > NAMEREF_MAX)
        return (&nameref_maxloop_value);
      newname = nameref_cell (nv);
      if (newname == 0 || *newname == '\0')
        return ((SHELL_VAR *)NULL);      
      nv2 = hash_lookup (newname, vc->table);
      if (nv2 == 0)
        break;
      nv = nv2;
    }
  return nv;
}

/* Do nameref resolution from the VC, which is the local context for some
   function or builtin, `up' the chain to the global variables context.  If
   NVCP is not NULL, return the variable context where we finally ended the
   nameref resolution (so the bind_variable_internal can use the correct
   variable context and hash table). */
static SHELL_VAR *
find_variable_nameref_context (SHELL_VAR *v, VAR_CONTEXT *vc, VAR_CONTEXT **nvcp)
{
  SHELL_VAR *nv, *nv2;
  VAR_CONTEXT *nvc;

  /* Look starting at the current context all the way `up' */
  for (nv = v, nvc = vc; nvc; nvc = nvc->down)
    {
      nv2 = find_nameref_at_context (nv, nvc);
      if (nv2 == &nameref_maxloop_value)
	return (nv2);			/* XXX */
      if (nv2 == 0)
        continue;
      nv = nv2;
      if (*nvcp)
        *nvcp = nvc;
      if (nameref_p (nv) == 0)
        break;
    }
  return (nameref_p (nv) ? (SHELL_VAR *)NULL : nv);
}

/* Do nameref resolution from the VC, which is the local context for some
   function or builtin, `up' the chain to the global variables context.  If
   NVCP is not NULL, return the variable context where we finally ended the
   nameref resolution (so the bind_variable_internal can use the correct
   variable context and hash table). */
static SHELL_VAR *
find_variable_last_nameref_context (SHELL_VAR *v, VAR_CONTEXT *vc, VAR_CONTEXT **nvcp)
{
  SHELL_VAR *nv, *nv2;
  VAR_CONTEXT *nvc;

  /* Look starting at the current context all the way `up' */
  for (nv = v, nvc = vc; nvc; nvc = nvc->down)
    {
      nv2 = find_nameref_at_context (nv, nvc);
      if (nv2 == &nameref_maxloop_value)
	return (nv2);			/* XXX */
      if (nv2 == 0)
	continue;
      nv = nv2;
      if (*nvcp)
        *nvcp = nvc;
    }
  return (nameref_p (nv) ? nv : (SHELL_VAR *)NULL);
}

SHELL_VAR *
find_variable_nameref_for_create (const char *name, int flags)
{
  SHELL_VAR *var;

  /* See if we have a nameref pointing to a variable that hasn't been
     created yet. */
  var = find_variable_last_nameref (name, 1);
  if ((flags&1) && var && nameref_p (var) && invisible_p (var))
    {
      internal_warning (_("%s: removing nameref attribute"), name);
      VUNSETATTR (var, att_nameref);
    }
  if (var && nameref_p (var))
    {
      if (legal_identifier (nameref_cell (var)) == 0)
	{
	  sh_invalidid (nameref_cell (var) ? nameref_cell (var) : "");
	  return ((SHELL_VAR *)INVALID_NAMEREF_VALUE);
	}
    }
  return (var);
}

SHELL_VAR *
find_variable_nameref_for_assignment (const char *name, int flags)
{
  SHELL_VAR *var;

  /* See if we have a nameref pointing to a variable that hasn't been
     created yet. */
  var = find_variable_last_nameref (name, 1);
  if (var && nameref_p (var) && invisible_p (var))	/* XXX - flags */
    {
      internal_warning (_("%s: removing nameref attribute"), name);
      VUNSETATTR (var, att_nameref);
    }
  if (var && nameref_p (var))
    {
      if (valid_nameref_value (nameref_cell (var), 1) == 0)
	{
	  sh_invalidid (nameref_cell (var) ? nameref_cell (var) : "");
	  return ((SHELL_VAR *)INVALID_NAMEREF_VALUE);
	}
    }
  return (var);
}

/* If find_variable (name) returns NULL, check that it's not a nameref
   referencing a variable that doesn't exist. If it is, return the new
   name. If not, return the original name. Kind of like the previous
   function, but dealing strictly with names. This takes assignment flags
   so it can deal with the various assignment modes used by `declare'. */
char *
nameref_transform_name (char *name, int flags)
{
  SHELL_VAR *v;
  char *newname;

  v = 0;
  if (flags & ASS_MKLOCAL)
    {
      v = find_variable_last_nameref (name, 1);
      /* If we're making local variables, only follow namerefs that point to
	 non-existent variables at the same variable context. */
      if (v && v->context != variable_context)
	v = 0;
    }
  else if (flags & ASS_MKGLOBAL)
    v = (flags & ASS_CHKLOCAL) ? find_variable_last_nameref (name, 1)
			       : find_global_variable_last_nameref (name, 1);
  if (v && nameref_p (v) && valid_nameref_value (nameref_cell (v), 1))
    return nameref_cell (v);
  return name;
}

/* Find a variable, forcing a search of the temporary environment first */
SHELL_VAR *
find_variable_tempenv (const char *name)
{
  SHELL_VAR *var;

  var = find_variable_internal (name, FV_FORCETEMPENV);
  if (var && nameref_p (var))
    var = find_variable_nameref (var);
  return (var);
}

/* Find a variable, not forcing a search of the temporary environment first */
SHELL_VAR *
find_variable_notempenv (const char *name)
{
  SHELL_VAR *var;

  var = find_variable_internal (name, 0);
  if (var && nameref_p (var))
    var = find_variable_nameref (var);
  return (var);
}

SHELL_VAR *
find_global_variable (const char *name)
{
  SHELL_VAR *var;

  var = var_lookup (name, global_variables);
  if (var && nameref_p (var))
    var = find_variable_nameref (var);	/* XXX - find_global_variable_noref? */

  if (var == 0)
    return ((SHELL_VAR *)NULL);

  return (var->dynamic_value ? (*(var->dynamic_value)) (var) : var);
}

SHELL_VAR *
find_global_variable_noref (const char *name)
{
  SHELL_VAR *var;

  var = var_lookup (name, global_variables);

  if (var == 0)
    return ((SHELL_VAR *)NULL);

  return (var->dynamic_value ? (*(var->dynamic_value)) (var) : var);
}

SHELL_VAR *
find_shell_variable (const char *name)
{
  SHELL_VAR *var;

  var = var_lookup (name, shell_variables);
  if (var && nameref_p (var))
    var = find_variable_nameref (var);

  if (var == 0)
    return ((SHELL_VAR *)NULL);

  return (var->dynamic_value ? (*(var->dynamic_value)) (var) : var);
}

/* Look up the variable entry named NAME.  Returns the entry or NULL. */
SHELL_VAR *
find_variable (const char *name)
{
  SHELL_VAR *v;
  int flags;

  last_table_searched = 0;
  flags = 0;
  if (expanding_redir == 0 && (assigning_in_environment || executing_builtin))
    flags |= FV_FORCETEMPENV;
  v = find_variable_internal (name, flags);
  if (v && nameref_p (v))
    v = find_variable_nameref (v);
  return v;
}

/* Find the first instance of NAME in the variable context chain; return first
   one found without att_invisible set; return 0 if no non-invisible instances
   found. */
SHELL_VAR *
find_variable_no_invisible (const char *name)
{
  SHELL_VAR *v;
  int flags;

  last_table_searched = 0;
  flags = FV_SKIPINVISIBLE;
  if (expanding_redir == 0 && (assigning_in_environment || executing_builtin))
    flags |= FV_FORCETEMPENV;
  v = find_variable_internal (name, flags);
  if (v && nameref_p (v))
    v = find_variable_nameref (v);
  return v;
}

/* Find the first instance of NAME in the variable context chain; return first
   one found even if att_invisible set. */
SHELL_VAR *
find_variable_for_assignment (const char *name)
{
  SHELL_VAR *v;
  int flags;

  last_table_searched = 0;
  flags = 0;
  if (expanding_redir == 0 && (assigning_in_environment || executing_builtin))
    flags |= FV_FORCETEMPENV;
  v = find_variable_internal (name, flags);
  if (v && nameref_p (v))
    v = find_variable_nameref (v);
  return v;
}

SHELL_VAR *
find_variable_noref (const char *name)
{
  SHELL_VAR *v;
  int flags;

  flags = 0;
  if (expanding_redir == 0 && (assigning_in_environment || executing_builtin))
    flags |= FV_FORCETEMPENV;
  v = find_variable_internal (name, flags);
  return v;
}

/* Look up the function entry whose name matches STRING.
   Returns the entry or NULL. */
SHELL_VAR *
find_function (const char *name)
{
  return (hash_lookup (name, shell_functions));
}

/* Find the function definition for the shell function named NAME.  Returns
   the entry or NULL. */
FUNCTION_DEF *
find_function_def (name)
     const char *name;
{
#if defined (DEBUGGER)
  return ((FUNCTION_DEF *)hash_lookup (name, shell_function_defs));
#else
  return ((FUNCTION_DEF *)0);
#endif
}

/* Return the value of VAR.  VAR is assumed to have been the result of a
   lookup without any subscript, if arrays are compiled into the shell. */
char *
get_variable_value (SHELL_VAR *var)
{
  if (var == 0)
    return ((char *)NULL);
#if defined (ARRAY_VARS)
  else if (array_p (var))
    return (array_reference (array_cell (var), 0));
  else if (assoc_p (var))
    return (assoc_reference (assoc_cell (var), "0"));
#endif
  else
    return (value_cell (var));
}

/* Return the string value of a variable.  Return NULL if the variable
   doesn't exist.  Don't cons a new string.  This is a potential memory
   leak if the variable is found in the temporary environment, but doesn't
   leak in practice.  Since functions and variables have separate name
   spaces, returns NULL if var_name is a shell function only. */
char *
get_string_value (const char *var_name)
{
  SHELL_VAR *var;

  var = find_variable (var_name);
  return ((var) ? get_variable_value (var) : (char *)NULL);
}

/* This is present for use by the tilde and readline libraries. */
char *
sh_get_env_value (const char *v)
{
  return get_string_value (v);
}

/* **************************************************************** */
/*								    */
/*		  Creating and setting variables		    */
/*								    */
/* **************************************************************** */

static int
var_sametype (SHELL_VAR *v1, SHELL_VAR *v2)
{
  if (v1 == 0 || v2 == 0)
    return 0;
#if defined (ARRAY_VARS)
  else if (assoc_p (v1) && assoc_p (v2))
    return 1;
  else if (array_p (v1) && array_p (v2))
    return 1;
  else if (array_p (v1) || array_p (v2))
    return 0;
  else if (assoc_p (v1) || assoc_p (v2))
    return 0;
#endif
  else
    return 1;
}

int
validate_inherited_value (SHELL_VAR *var, int type)
{
#if defined (ARRAY_VARS)
  if (type == att_array && assoc_p (var))
    return 0;
  else if (type == att_assoc && array_p (var))
    return 0;
  else
#endif
  return 1;	/* should we run convert_var_to_array here or let the caller? */
}

/* Set NAME to VALUE if NAME has no value. */
SHELL_VAR *
set_if_not (char *name, char *value)
{
  SHELL_VAR *v;

  if (shell_variables == 0)
    create_variable_tables ();

  v = find_variable (name);
  if (v == 0)
    v = bind_variable_internal (name, value, global_variables->table, HASH_NOSRCH, 0);
  return (v);
}

/* Create a local variable referenced by NAME. */
SHELL_VAR *
make_local_variable (const char *name, int flags)
{
  SHELL_VAR *new_var, *old_var, *old_ref;
  VAR_CONTEXT *vc;
  int was_tmpvar;
  char *old_value;

  /* We don't want to follow the nameref chain when making local variables; we
     just want to create them. */
  old_ref = find_variable_noref (name);
  if (old_ref && nameref_p (old_ref) == 0)
    old_ref = 0;
  /* local foo; local foo;  is a no-op. */
  old_var = find_variable (name);
  if (old_ref == 0 && old_var && local_p (old_var) && old_var->context == variable_context)
    return (old_var);

  /* local -n foo; local -n foo;  is a no-op. */
  if (old_ref && local_p (old_ref) && old_ref->context == variable_context)
    return (old_ref);

  /* From here on, we want to use the refvar, not the variable it references */
  if (old_ref)
    old_var = old_ref;

  was_tmpvar = old_var && tempvar_p (old_var);
  /* If we're making a local variable in a shell function, the temporary env
     has already been merged into the function's variable context stack.  We
     can assume that a temporary var in the same context appears in the same
     VAR_CONTEXT and can safely be returned without creating a new variable
     (which results in duplicate names in the same VAR_CONTEXT->table */
  /* We can't just test tmpvar_p because variables in the temporary env given
     to a shell function appear in the function's local variable VAR_CONTEXT
     but retain their tempvar attribute.  We want temporary variables that are
     found in temporary_env, hence the test for last_table_searched, which is
     set in hash_lookup and only (so far) checked here. */
  if (was_tmpvar && old_var->context == variable_context && last_table_searched != temporary_env)
    {
      VUNSETATTR (old_var, att_invisible);	/* XXX */
      /* We still want to flag this variable as local, though, and set things
         up so that it gets treated as a local variable. */
      new_var = old_var;
      /* Since we found the variable in a temporary environment, this will
	 succeed. */
      for (vc = shell_variables; vc; vc = vc->down)
	if (vc_isfuncenv (vc) && vc->scope == variable_context)
	  break;
      goto set_local_var_flags;

      return (old_var);
    }

  /* If we want to change to "inherit the old variable's value" semantics,
     here is where to save the old value. */
  old_value = was_tmpvar ? value_cell (old_var) : (char *)NULL;

  for (vc = shell_variables; vc; vc = vc->down)
    if (vc_isfuncenv (vc) && vc->scope == variable_context)
      break;

  if (vc == 0)
    {
      internal_error (_("make_local_variable: no function context at current scope"));
      return ((SHELL_VAR *)NULL);
    }
  else if (vc->table == 0)
    vc->table = hash_create (TEMPENV_HASH_BUCKETS);

  /* Since this is called only from the local/declare/typeset code, we can
     call builtin_error here without worry (of course, it will also work
     for anything that sets this_command_name).  Variables with the `noassign'
     attribute may not be made local.  The test against old_var's context
     level is to disallow local copies of readonly global variables (since I
     believe that this could be a security hole).  Readonly copies of calling
     function local variables are OK. */
  if (old_var && (noassign_p (old_var) ||
		 (readonly_p (old_var) && old_var->context == 0)))
    {
      if (readonly_p (old_var))
	sh_readonly (name);
      else if (noassign_p (old_var))
	builtin_error (_("%s: variable may not be assigned value"), name);
#if 0
      /* Let noassign variables through with a warning */
      if (readonly_p (old_var))
#endif
	return ((SHELL_VAR *)NULL);
    }

  if (old_var == 0)
    new_var = make_new_variable (name, vc->table);
  else
    {
      new_var = make_new_variable (name, vc->table);

      /* If we found this variable in one of the temporary environments,
	 inherit its value.  Watch to see if this causes problems with
	 things like `x=4 local x'. XXX - see above for temporary env
	 variables with the same context level as variable_context */
      /* XXX - we should only do this if the variable is not an array. */
      /* If we want to change the local variable semantics to "inherit
	 the old variable's value" here is where to set it.  And we would
	 need to use copy_variable (currently unused) to do it for all
	 possible variable values. */
      if (was_tmpvar)
	var_setvalue (new_var, savestring (old_value));
      else if (localvar_inherit || (flags & MKLOC_INHERIT))
	{
	  /* This may not make sense for nameref variables that are shadowing
	     variables with the same name, but we don't know that yet. */
#if defined (ARRAY_VARS)
	  if (assoc_p (old_var))
	    var_setassoc (new_var, assoc_copy (assoc_cell (old_var)));
	  else if (array_p (old_var))
	    var_setarray (new_var, array_copy (array_cell (old_var)));
	  else if (value_cell (old_var))
#else
	  if (value_cell (old_var))
#endif
	    var_setvalue (new_var, savestring (value_cell (old_var)));
	  else
	    var_setvalue (new_var, (char *)NULL);
	}

      if (localvar_inherit || (flags & MKLOC_INHERIT))
	{
	  /* It doesn't make sense to inherit the nameref attribute */
	  new_var->attributes = old_var->attributes & ~att_nameref;
	  new_var->dynamic_value = old_var->dynamic_value;
	  new_var->assign_func = old_var->assign_func;
	}
      else
	/* We inherit the export attribute, but no others. */
	new_var->attributes = exported_p (old_var) ? att_exported : 0;
    }

set_local_var_flags:
  vc->flags |= VC_HASLOCAL;

  new_var->context = variable_context;
  VSETATTR (new_var, att_local);

  if (ifsname (name))
    setifs (new_var);

  /* value_cell will be 0 if localvar_inherit == 0 or there was no old variable
     with the same name or the old variable was invisible */
  if (was_tmpvar == 0 && value_cell (new_var) == 0)
    VSETATTR (new_var, att_invisible);	/* XXX */
  return (new_var);
}

/* Create a new shell variable with name NAME. */
static SHELL_VAR *
new_shell_variable (const char *name)
{
  SHELL_VAR *entry;

  entry = (SHELL_VAR *)xmalloc (sizeof (SHELL_VAR));

  entry->name = savestring (name);
  var_setvalue (entry, (char *)NULL);
  CLEAR_EXPORTSTR (entry);

  entry->dynamic_value = (sh_var_value_func_t *)NULL;
  entry->assign_func = (sh_var_assign_func_t *)NULL;

  entry->attributes = 0;

  /* Always assume variables are to be made at toplevel!
     make_local_variable has the responsibility of changing the
     variable context. */
  entry->context = 0;

  return (entry);
}

/* Create a new shell variable with name NAME and add it to the hash table
   TABLE. */
static SHELL_VAR *
make_new_variable (const char *name, HASH_TABLE *table)
{
  SHELL_VAR *entry;
  BUCKET_CONTENTS *elt;

  entry = new_shell_variable (name);

  /* Make sure we have a shell_variables hash table to add to. */
  if (shell_variables == 0)
    create_variable_tables ();

  elt = hash_insert (savestring (name), table, HASH_NOSRCH);
  elt->data = (PTR_T)entry;

  return entry;
}

#if defined (ARRAY_VARS)
SHELL_VAR *
make_new_array_variable (char *name)
{
  SHELL_VAR *entry;
  ARRAY *array;

  entry = make_new_variable (name, global_variables->table);
  array = array_create ();

  var_setarray (entry, array);
  VSETATTR (entry, att_array);
  return entry;
}

SHELL_VAR *
make_local_array_variable (char *name, int flags)
{
  SHELL_VAR *var;
  ARRAY *array;
  int assoc_ok;

  assoc_ok = flags & MKLOC_ASSOCOK;

  var = make_local_variable (name, flags & MKLOC_INHERIT);	/* XXX for now */
  /* If ASSOC_OK is non-zero, assume that we are ok with letting an assoc
     variable return to the caller without converting it. The caller will
     either flag an error or do the conversion itself. */
  if (var == 0 || array_p (var) || (assoc_ok && assoc_p (var)))
    return var;

  /* Validate any value we inherited from a variable instance at a previous
     scope and discard anything that's invalid. */
  if (localvar_inherit && assoc_p (var))
    {
      internal_warning (_("%s: cannot inherit value from incompatible type"), name);
      VUNSETATTR (var, att_assoc);
      dispose_variable_value (var);
      array = array_create ();
      var_setarray (var, array);
    }
  else if (localvar_inherit)
    var = convert_var_to_array (var);		/* XXX */
  else
    {
      dispose_variable_value (var);
      array = array_create ();
      var_setarray (var, array);
    }

  VSETATTR (var, att_array);
  return var;
}

SHELL_VAR *
make_new_assoc_variable (char *name)
{
  SHELL_VAR *entry;
  HASH_TABLE *hash;

  entry = make_new_variable (name, global_variables->table);
  hash = assoc_create (ASSOC_HASH_BUCKETS);

  var_setassoc (entry, hash);
  VSETATTR (entry, att_assoc);
  return entry;
}

SHELL_VAR *
make_local_assoc_variable (char *name, int flags)
{
  SHELL_VAR *var;
  HASH_TABLE *hash;
  int array_ok;

  array_ok = flags & MKLOC_ARRAYOK;

  var = make_local_variable (name, flags & MKLOC_INHERIT);	/* XXX for now */
  /* If ARRAY_OK is non-zero, assume that we are ok with letting an array
     variable return to the caller without converting it. The caller will
     either flag an error or do the conversion itself. */
  if (var == 0 || assoc_p (var) || (array_ok && array_p (var)))
    return var;

  /* Validate any value we inherited from a variable instance at a previous
     scope and discard anything that's invalid. */
  if (localvar_inherit && array_p (var))
    {
      internal_warning (_("%s: cannot inherit value from incompatible type"), name);
      VUNSETATTR (var, att_array);
      dispose_variable_value (var);
      hash = assoc_create (ASSOC_HASH_BUCKETS);
      var_setassoc (var, hash);
    }
  else if (localvar_inherit)
    var = convert_var_to_assoc (var);		/* XXX */
  else
    {
      dispose_variable_value (var);
      hash = assoc_create (ASSOC_HASH_BUCKETS);
      var_setassoc (var, hash);
    }

  VSETATTR (var, att_assoc);
  return var;
}
#endif

char *
make_variable_value (SHELL_VAR *var, char *value, int flags)
{
  char *retval, *oval;
  intmax_t lval, rval;
  int expok, olen, op;

  /* If this variable has had its type set to integer (via `declare -i'),
     then do expression evaluation on it and store the result.  The
     functions in expr.c (evalexp()) and bind_int_variable() are responsible
     for turning off the integer flag if they don't want further
     evaluation done.  Callers that find it inconvenient to do this can set
     the ASS_NOEVAL flag.  For the special case of arithmetic expression
     evaluation, the caller can set ASS_NOLONGJMP to avoid jumping out to
     top_level. */
  if ((flags & ASS_NOEVAL) == 0 && integer_p (var))
    {
      if (flags & ASS_APPEND)
	{
	  oval = value_cell (var);
	  lval = evalexp (oval, 0, &expok);	/* ksh93 seems to do this */
	  if (expok == 0)
	    {
	      if (flags & ASS_NOLONGJMP)
		goto make_value;
	      else
		{
		  top_level_cleanup ();
		  jump_to_top_level (DISCARD);
		}
	    }
	}
      rval = evalexp (value, 0, &expok);
      if (expok == 0)
	{
	  if (flags & ASS_NOLONGJMP)
	    goto make_value;
	  else
	    {
	      top_level_cleanup ();
	      jump_to_top_level (DISCARD);
	    }
	}
      /* This can be fooled if the variable's value changes while evaluating
	 `rval'.  We can change it if we move the evaluation of lval to here. */
      if (flags & ASS_APPEND)
	rval += lval;
      retval = itos (rval);
    }
#if defined (CASEMOD_ATTRS)
  else if ((flags & ASS_NOEVAL) == 0 && (capcase_p (var) || uppercase_p (var) || lowercase_p (var)))
    {
      if (flags & ASS_APPEND)
	{
	  oval = get_variable_value (var);
	  if (oval == 0)	/* paranoia */
	    oval = "";
	  olen = STRLEN (oval);
	  retval = (char *)xmalloc (olen + (value ? STRLEN (value) : 0) + 1);
	  strcpy (retval, oval);
	  if (value)
	    strcpy (retval+olen, value);
	}
      else if (*value)
	retval = savestring (value);
      else
	{
	  retval = (char *)xmalloc (1);
	  retval[0] = '\0';
	}
      op = capcase_p (var) ? CASE_CAPITALIZE
			 : (uppercase_p (var) ? CASE_UPPER : CASE_LOWER);
      oval = sh_modcase (retval, (char *)0, op);
      free (retval);
      retval = oval;
    }
#endif /* CASEMOD_ATTRS */
  else if (value)
    {
make_value:
      if (flags & ASS_APPEND)
	{
	  oval = get_variable_value (var);
	  if (oval == 0)	/* paranoia */
	    oval = "";
	  olen = STRLEN (oval);
	  retval = (char *)xmalloc (olen + (value ? STRLEN (value) : 0) + 1);
	  strcpy (retval, oval);
	  if (value)
	    strcpy (retval+olen, value);
	}
      else if (*value)
	retval = savestring (value);
      else
	{
	  retval = (char *)xmalloc (1);
	  retval[0] = '\0';
	}
    }
  else
    retval = (char *)NULL;

  return retval;
}

/* If we can optimize appending to string variables, say so */
static int
can_optimize_assignment (SHELL_VAR *entry, char *value, int aflags)
{
  if ((aflags & ASS_APPEND) == 0)
    return 0;
#if defined (ARRAY_VARS)
  if (array_p (entry) || assoc_p (entry))
    return 0;
#endif
  if (integer_p (entry) || uppercase_p (entry) || lowercase_p (entry) || capcase_p (entry))
    return 0;
  if (readonly_p (entry) || noassign_p (entry))
    return 0;
  return 1;
}

/* right now we optimize appends to string variables */
static SHELL_VAR *
optimized_assignment (SHELL_VAR *entry, char *value, int aflags)
{
  size_t len, vlen;
  char *v, *new;

  v = value_cell (entry);
  len = STRLEN (v);
  vlen = STRLEN (value);

  new = (char *)xrealloc (v, len + vlen + 8);	/* for now */
  if (vlen == 1)
    {
      new[len] = *value;
      new[len+1] = '\0';
    }
  else
    strcpy (new + len, value);
  var_setvalue (entry, new);
  return entry;
}

/* Bind a variable NAME to VALUE in the HASH_TABLE TABLE, which may be the
   temporary environment (but usually is not).  HFLAGS controls how NAME
   is looked up in TABLE; AFLAGS controls how VALUE is assigned */
SHELL_VAR *
bind_variable_internal (const char *name, char *value, HASH_TABLE *table, int hflags, int aflags)
{
  char *newval, *tname;
  SHELL_VAR *entry, *tentry;

  entry = (hflags & HASH_NOSRCH) ? (SHELL_VAR *)NULL : hash_lookup (name, table);
  /* Follow the nameref chain here if this is the global variables table */
  if (entry && nameref_p (entry) && (invisible_p (entry) == 0) && table == global_variables->table)
    {
      entry = find_global_variable (entry->name);
      /* Let's see if we have a nameref referencing a variable that hasn't yet
	 been created. */
      if (entry == 0)
	entry = find_variable_last_nameref (name, 0);	/* XXX */
      if (entry == 0)					/* just in case */
        return (entry);
    }

  /* The first clause handles `declare -n ref; ref=x;' or `declare -n ref;
     declare -n ref' */
  if (entry && invisible_p (entry) && nameref_p (entry))
    {
      if ((aflags & ASS_FORCE) == 0 && value && valid_nameref_value (value, 0) == 0)
	{
	  sh_invalidid (value);
	  return ((SHELL_VAR *)NULL);
	}
      goto assign_value;
    }
  else if (entry && nameref_p (entry))
    {
      newval = nameref_cell (entry);	/* XXX - newval can't be NULL here */
      if (valid_nameref_value (newval, 0) == 0)
	{
	  sh_invalidid (newval);
	  return ((SHELL_VAR *)NULL);
	}
#if defined (ARRAY_VARS)
      /* declare -n foo=x[2] ; foo=bar */
      if (valid_array_reference (newval, 0))
	{
	  tname = array_variable_name (newval, 0, (char **)0, (int *)0);
	  if (tname && (tentry = find_variable_noref (tname)) && nameref_p (tentry))
	    {
	      /* nameref variables can't be arrays */
	      internal_warning (_("%s: removing nameref attribute"), name_cell (tentry));
	      FREE (value_cell (tentry));		/* XXX - bash-4.3 compat */
	      var_setvalue (tentry, (char *)NULL);
	      VUNSETATTR (tentry, att_nameref);
	    }
	  free (tname);

	  /* entry == nameref variable; tentry == array variable;
	     newval == x[2]; value = bar
	     We don't need to call make_variable_value here, since
	     assign_array_element will eventually do it itself based on
	     newval and aflags. */

	  entry = assign_array_element (newval, value, aflags|ASS_NAMEREF, (array_eltstate_t *)0);
	  if (entry == 0)
	    return entry;
	}
      else
#endif
	{
	  entry = make_new_variable (newval, table);
	  var_setvalue (entry, make_variable_value (entry, value, aflags));
	}
    }
  else if (entry == 0)
    {
      entry = make_new_variable (name, table);
      var_setvalue (entry, make_variable_value (entry, value, aflags)); /* XXX */
    }
  else if (entry->assign_func)	/* array vars have assign functions now */
    {
      if ((readonly_p (entry) && (aflags & ASS_FORCE) == 0) || noassign_p (entry))
	{
	  if (readonly_p (entry))
	    err_readonly (name_cell (entry));
	  return (entry);
	}

      INVALIDATE_EXPORTSTR (entry);
      newval = (aflags & ASS_APPEND) ? make_variable_value (entry, value, aflags) : value;
      if (assoc_p (entry))
	entry = (*(entry->assign_func)) (entry, newval, -1, savestring ("0"));
      else if (array_p (entry))
	entry = (*(entry->assign_func)) (entry, newval, 0, 0);
      else
	entry = (*(entry->assign_func)) (entry, newval, -1, 0);
      if (newval != value)
	free (newval);
      return (entry);
    }
  else
    {
assign_value:
      if ((readonly_p (entry) && (aflags & ASS_FORCE) == 0) || noassign_p (entry))
	{
	  if (readonly_p (entry))
	    err_readonly (name_cell (entry));
	  return (entry);
	}

      /* Variables which are bound are visible. */
      VUNSETATTR (entry, att_invisible);

      /* If we can optimize the assignment, do so and return.  Right now, we
	 optimize appends to string variables. */
      if (can_optimize_assignment (entry, value, aflags))
	{
	  INVALIDATE_EXPORTSTR (entry);
	  optimized_assignment (entry, value, aflags);

	  if (mark_modified_vars)
	    VSETATTR (entry, att_exported);

	  if (exported_p (entry))
	    array_needs_making = 1;

	  return (entry);
	}

#if defined (ARRAY_VARS)
      if (assoc_p (entry) || array_p (entry))
        newval = make_array_variable_value (entry, 0, "0", value, aflags);
      else
#endif
      newval = make_variable_value (entry, value, aflags);	/* XXX */

      /* Invalidate any cached export string */
      INVALIDATE_EXPORTSTR (entry);

#if defined (ARRAY_VARS)
      /* XXX -- this bears looking at again -- XXX */
      /* If an existing array variable x is being assigned to with x=b or
	 `read x' or something of that nature, silently convert it to
	 x[0]=b or `read x[0]'. */
      if (assoc_p (entry))
	{
	  assoc_insert (assoc_cell (entry), savestring ("0"), newval);
	  free (newval);
	}
      else if (array_p (entry))
	{
	  array_insert (array_cell (entry), 0, newval);
	  free (newval);
	}
      else
#endif
	{
	  FREE (value_cell (entry));
	  var_setvalue (entry, newval);
	}
    }

  if (mark_modified_vars)
    VSETATTR (entry, att_exported);

  if (exported_p (entry))
    array_needs_making = 1;

  return (entry);
}
	
/* Bind a variable NAME to VALUE.  This conses up the name
   and value strings.  If we have a temporary environment, we bind there
   first, then we bind into shell_variables. */

SHELL_VAR *
bind_variable (const char *name, char *value, int flags)
{
  SHELL_VAR *v, *nv;
  VAR_CONTEXT *vc, *nvc;

  if (shell_variables == 0)
    create_variable_tables ();

  /* If we have a temporary environment, look there first for the variable,
     and, if found, modify the value there before modifying it in the
     shell_variables table.  This allows sourced scripts to modify values
     given to them in a temporary environment while modifying the variable
     value that the caller sees. */
  if (temporary_env && value)		/* XXX - can value be null here? */
    bind_tempenv_variable (name, value);

  /* XXX -- handle local variables here. */
  for (vc = shell_variables; vc; vc = vc->down)
    {
      if (vc_isfuncenv (vc) || vc_isbltnenv (vc))
	{
	  v = hash_lookup (name, vc->table);
	  nvc = vc;
	  if (v && nameref_p (v))
	    {
	      /* This starts at the context where we found the nameref. If we
		 want to start the name resolution over again at the original
		 context, this is where we need to change it */
	      nv = find_variable_nameref_context (v, vc, &nvc);
	      if (nv == 0)
		{
		  nv = find_variable_last_nameref_context (v, vc, &nvc);
		  if (nv && nameref_p (nv))
		    {
		      /* If this nameref variable doesn't have a value yet,
			 set the value.  Otherwise, assign using the value as
			 normal. */
		      if (nameref_cell (nv) == 0)
			return (bind_variable_internal (nv->name, value, nvc->table, 0, flags));
#if defined (ARRAY_VARS)
		      else if (valid_array_reference (nameref_cell (nv), 0))
			return (assign_array_element (nameref_cell (nv), value, flags, (array_eltstate_t *)0));
		      else
#endif
		      return (bind_variable_internal (nameref_cell (nv), value, nvc->table, 0, flags));
		    }
		  else if (nv == &nameref_maxloop_value)
		    {
		      internal_warning (_("%s: circular name reference"), v->name);
		      return (bind_global_variable (v->name, value, flags));
		    }
		  else
		    v = nv;
		}
	      else if (nv == &nameref_maxloop_value)
		{
		  internal_warning (_("%s: circular name reference"), v->name);
		  return (bind_global_variable (v->name, value, flags));
		}
	      else
	        v = nv;
	    }
	  if (v)
	    return (bind_variable_internal (v->name, value, nvc->table, 0, flags));
	}
    }
  /* bind_variable_internal will handle nameref resolution in this case */
  return (bind_variable_internal (name, value, global_variables->table, 0, flags));
}

SHELL_VAR *
bind_global_variable (const char *name, char *value, int flags)
{
  if (shell_variables == 0)
    create_variable_tables ();

  /* bind_variable_internal will handle nameref resolution in this case */
  return (bind_variable_internal (name, value, global_variables->table, 0, flags));
}

SHELL_VAR *
bind_invalid_envvar (const char *name, char *value, int flags)
{
  if (invalid_env == 0)
    invalid_env = hash_create (64);	/* XXX */
  return (bind_variable_internal (name, value, invalid_env, HASH_NOSRCH, flags));
}

/* Make VAR, a simple shell variable, have value VALUE.  Once assigned a
   value, variables are no longer invisible.  This is a duplicate of part
   of the internals of bind_variable.  If the variable is exported, or
   all modified variables should be exported, mark the variable for export
   and note that the export environment needs to be recreated. */
SHELL_VAR *
bind_variable_value (SHELL_VAR *var, char *value, int aflags)
{
  char *t;
  int invis;

  invis = invisible_p (var);
  VUNSETATTR (var, att_invisible);

  if (var->assign_func)
    {
      /* If we're appending, we need the old value, so use
	 make_variable_value */
      t = (aflags & ASS_APPEND) ? make_variable_value (var, value, aflags) : value;
      (*(var->assign_func)) (var, t, -1, 0);
      if (t != value && t)
	free (t);      
    }
  else
    {
      t = make_variable_value (var, value, aflags);
      if ((aflags & (ASS_NAMEREF|ASS_FORCE)) == ASS_NAMEREF && check_selfref (name_cell (var), t, 0))
	{
	  if (variable_context)
	    internal_warning (_("%s: circular name reference"), name_cell (var));
	  else
	    {
	      internal_error (_("%s: nameref variable self references not allowed"), name_cell (var));
	      free (t);
	      if (invis)
		VSETATTR (var, att_invisible);	/* XXX */
	      return ((SHELL_VAR *)NULL);
	    }
	}
      if ((aflags & ASS_NAMEREF) && (valid_nameref_value (t, 0) == 0))
	{
	  free (t);
	  if (invis)
	    VSETATTR (var, att_invisible);	/* XXX */
	  return ((SHELL_VAR *)NULL);
	}
      FREE (value_cell (var));
      var_setvalue (var, t);
    }

  INVALIDATE_EXPORTSTR (var);

  if (mark_modified_vars)
    VSETATTR (var, att_exported);

  if (exported_p (var))
    array_needs_making = 1;

  return (var);
}

/* Bind/create a shell variable with the name LHS to the RHS.
   This creates or modifies a variable such that it is an integer.

   This used to be in expr.c, but it is here so that all of the
   variable binding stuff is localized.  Since we don't want any
   recursive evaluation from bind_variable() (possible without this code,
   since bind_variable() calls the evaluator for variables with the integer
   attribute set), we temporarily turn off the integer attribute for each
   variable we set here, then turn it back on after binding as necessary. */

SHELL_VAR *
bind_int_variable (char *lhs, char *rhs, int flags)
{
  register SHELL_VAR *v;
  int isint, isarr, implicitarray, vflags, avflags;

  isint = isarr = implicitarray = 0;
#if defined (ARRAY_VARS)
  /* Don't rely on VA_NOEXPAND being 1, set it explicitly */
  vflags = (flags & ASS_NOEXPAND) ? VA_NOEXPAND : 0;
  if (flags & ASS_ONEWORD)
    vflags |= VA_ONEWORD;
  if (valid_array_reference (lhs, vflags))
    {
      isarr = 1;
      avflags = 0;
      /* Common code to translate between assignment and reference flags. */
      if (flags & ASS_NOEXPAND)
	avflags |= AV_NOEXPAND;
      if (flags & ASS_ONEWORD)
	avflags |= AV_ONEWORD;
      v = array_variable_part (lhs, avflags, (char **)0, (int *)0);
    }
  else if (legal_identifier (lhs) == 0)
    {
      sh_invalidid (lhs);
      return ((SHELL_VAR *)NULL);      
    }
  else
#endif
    v = find_variable (lhs);

  if (v)
    {
      isint = integer_p (v);
      VUNSETATTR (v, att_integer);
#if defined (ARRAY_VARS)
      if (array_p (v) && isarr == 0)
	implicitarray = 1;
#endif
    }

#if defined (ARRAY_VARS)
  if (isarr)
    v = assign_array_element (lhs, rhs, flags, (array_eltstate_t *)0);
  else if (implicitarray)
    v = bind_array_variable (lhs, 0, rhs, 0);	/* XXX - check on flags */
  else
#endif
    v = bind_variable (lhs, rhs, 0);	/* why not use bind_variable_value? */

  if (v)
    {
      if (isint)
	VSETATTR (v, att_integer);
      VUNSETATTR (v, att_invisible);
    }

  if (v && nameref_p (v))
    internal_warning (_("%s: assigning integer to name reference"), lhs);
     
  return (v);
}

SHELL_VAR *
bind_var_to_int (char *var, intmax_t val, int flags)
{
  char ibuf[INT_STRLEN_BOUND (intmax_t) + 1], *p;

  p = fmtulong (val, 10, ibuf, sizeof (ibuf), 0);
  return (bind_int_variable (var, p, flags));
}

/* Do a function binding to a variable.  You pass the name and
   the command to bind to.  This conses the name and command. */
SHELL_VAR *
bind_function (const char *name, COMMAND *value)
{
  SHELL_VAR *entry;

  entry = find_function (name);
  if (entry == 0)
    {
      BUCKET_CONTENTS *elt;

      elt = hash_insert (savestring (name), shell_functions, HASH_NOSRCH);
      entry = new_shell_variable (name);
      elt->data = (PTR_T)entry;
    }
  else
    INVALIDATE_EXPORTSTR (entry);

  if (var_isset (entry))
    dispose_command (function_cell (entry));

  if (value)
    var_setfunc (entry, copy_command (value));
  else
    var_setfunc (entry, 0);

  VSETATTR (entry, att_function);

  if (mark_modified_vars)
    VSETATTR (entry, att_exported);

  VUNSETATTR (entry, att_invisible);		/* Just to be sure */

  if (exported_p (entry))
    array_needs_making = 1;

#if defined (PROGRAMMABLE_COMPLETION)
  set_itemlist_dirty (&it_functions);
#endif

  return (entry);
}

#if defined (DEBUGGER)
/* Bind a function definition, which includes source file and line number
   information in addition to the command, into the FUNCTION_DEF hash table.
   If (FLAGS & 1), overwrite any existing definition. If FLAGS == 0, leave
   any existing definition alone. */
void
bind_function_def (const char *name, FUNCTION_DEF *value, int flags)
{
  FUNCTION_DEF *entry;
  BUCKET_CONTENTS *elt;
  COMMAND *cmd;

  entry = find_function_def (name);
  if (entry && (flags & 1))
    {
      dispose_function_def_contents (entry);
      entry = copy_function_def_contents (value, entry);
    }
  else if (entry)
    return;
  else
    {
      cmd = value->command;
      value->command = 0;
      entry = copy_function_def (value);
      value->command = cmd;

      elt = hash_insert (savestring (name), shell_function_defs, HASH_NOSRCH);
      elt->data = (PTR_T *)entry;
    }
}
#endif /* DEBUGGER */

/* Add STRING, which is of the form foo=bar, to the temporary environment
   HASH_TABLE (temporary_env).  The functions in execute_cmd.c are
   responsible for moving the main temporary env to one of the other
   temporary environments.  The expansion code in subst.c calls this. */
int
assign_in_env (WORD_DESC *word, int flags)
{
  int offset, aflags;
  char *name, *temp, *value, *newname;
  SHELL_VAR *var;
  const char *string;

  string = word->word;

  aflags = 0;
  offset = assignment (string, 0);
  newname = name = savestring (string);
  value = (char *)NULL;

  if (name[offset] == '=')
    {
      name[offset] = 0;

      /* don't ignore the `+' when assigning temporary environment */
      if (name[offset - 1] == '+')
	{
	  name[offset - 1] = '\0';
	  aflags |= ASS_APPEND;
	}

      if (legal_identifier (name) == 0)
	{
	  sh_invalidid (name);
	  free (name);
	  return (0);
	}
  
      var = find_variable (name);
      if (var == 0)
	{
	  var = find_variable_last_nameref (name, 1);
	  /* If we're assigning a value to a nameref variable in the temp
	     environment, and the value of the nameref is valid for assignment,
	     but the variable does not already exist, assign to the nameref
	     target and add the target to the temporary environment.  This is
	     what ksh93 does */
	  /* We use 2 in the call to valid_nameref_value because we don't want
	     to allow array references here at all (newname will be used to
	     create a variable directly below) */
	  if (var && nameref_p (var) && valid_nameref_value (nameref_cell (var), 2))
	    {
	      newname = nameref_cell (var);
	      var = 0;		/* don't use it for append */
	    }
	}
      else
        newname = name_cell (var);	/* no-op if not nameref */
	  
      if (var && (readonly_p (var) || noassign_p (var)))
	{
	  if (readonly_p (var))
	    err_readonly (name);
	  free (name);
  	  return (0);
	}
      temp = name + offset + 1;

      value = expand_assignment_string_to_string (temp, 0);

      if (var && (aflags & ASS_APPEND))
	{
	  if (value == 0)
	    {
	      value = (char *)xmalloc (1);	/* like do_assignment_internal */
	      value[0] = '\0';
	    }
	  temp = make_variable_value (var, value, aflags);
	  FREE (value);
	  value = temp;
	}
    }

  if (temporary_env == 0)
    temporary_env = hash_create (TEMPENV_HASH_BUCKETS);

  var = hash_lookup (newname, temporary_env);
  if (var == 0)
    var = make_new_variable (newname, temporary_env);
  else
    FREE (value_cell (var));

  if (value == 0)
    {
      value = (char *)xmalloc (1);	/* see above */
      value[0] = '\0';
    }

  var_setvalue (var, value);
  var->attributes |= (att_exported|att_tempvar);
  var->context = variable_context;	/* XXX */

  INVALIDATE_EXPORTSTR (var);
  var->exportstr = mk_env_string (newname, value, 0);

  array_needs_making = 1;

  if (flags)
    {
      if (STREQ (newname, "POSIXLY_CORRECT") || STREQ (newname, "POSIX_PEDANDTIC"))
	save_posix_options ();		/* XXX one level of saving right now */
      stupidly_hack_special_variables (newname);
    }

  if (echo_command_at_execute)
    /* The Korn shell prints the `+ ' in front of assignment statements,
	so we do too. */
    xtrace_print_assignment (name, value, 0, 1);

  free (name);
  return 1;
}

/* **************************************************************** */
/*								    */
/*			Copying variables			    */
/*								    */
/* **************************************************************** */

#ifdef INCLUDE_UNUSED
/* Copy VAR to a new data structure and return that structure. */
SHELL_VAR *
copy_variable (SHELL_VAR *var)
{
  SHELL_VAR *copy = (SHELL_VAR *)NULL;

  if (var)
    {
      copy = (SHELL_VAR *)xmalloc (sizeof (SHELL_VAR));

      copy->attributes = var->attributes;
      copy->name = savestring (var->name);

      if (function_p (var))
	var_setfunc (copy, copy_command (function_cell (var)));
#if defined (ARRAY_VARS)
      else if (array_p (var))
	var_setarray (copy, array_copy (array_cell (var)));
      else if (assoc_p (var))
	var_setassoc (copy, assoc_copy (assoc_cell (var)));
#endif
      else if (nameref_cell (var))	/* XXX - nameref */
	var_setref (copy, savestring (nameref_cell (var)));
      else if (value_cell (var))	/* XXX - nameref */
	var_setvalue (copy, savestring (value_cell (var)));
      else
	var_setvalue (copy, (char *)NULL);

      copy->dynamic_value = var->dynamic_value;
      copy->assign_func = var->assign_func;

      copy->exportstr = COPY_EXPORTSTR (var);

      copy->context = var->context;
    }
  return (copy);
}
#endif

/* **************************************************************** */
/*								    */
/*		  Deleting and unsetting variables		    */
/*								    */
/* **************************************************************** */

/* Dispose of the information attached to VAR. */
static void
dispose_variable_value (SHELL_VAR *var)
{
  if (function_p (var))
    dispose_command (function_cell (var));
#if defined (ARRAY_VARS)
  else if (array_p (var))
    array_dispose (array_cell (var));
  else if (assoc_p (var))
    assoc_dispose (assoc_cell (var));
#endif
  else if (nameref_p (var))
    FREE (nameref_cell (var));
  else
    FREE (value_cell (var));
}

void
dispose_variable (SHELL_VAR *var)
{
  if (var == 0)
    return;

  if (nofree_p (var) == 0)
    dispose_variable_value (var);

  FREE_EXPORTSTR (var);

  free (var->name);

  if (exported_p (var))
    array_needs_making = 1;

  free (var);
}

/* Unset the shell variable referenced by NAME.  Unsetting a nameref variable
   unsets the variable it resolves to but leaves the nameref alone. */
int
unbind_variable (const char *name)
{
  SHELL_VAR *v, *nv;
  int r;

  v = var_lookup (name, shell_variables);
  nv = (v && nameref_p (v)) ? find_variable_nameref (v) : (SHELL_VAR *)NULL;

  r = nv ? makunbound (nv->name, shell_variables) : makunbound (name, shell_variables);
  return r;
}

/* Unbind NAME, where NAME is assumed to be a nameref variable */
int
unbind_nameref (const char *name)
{
  SHELL_VAR *v;

  v = var_lookup (name, shell_variables);
  if (v && nameref_p (v))
    return makunbound (name, shell_variables);
  return 0;
}

/* Unbind the first instance of NAME, whether it's a nameref or not */
int
unbind_variable_noref (const char *name)
{
  SHELL_VAR *v;

  v = var_lookup (name, shell_variables);
  if (v)
    return makunbound (name, shell_variables);
  return 0;
}

int
unbind_global_variable (const char *name)
{
  SHELL_VAR *v, *nv;
  int r;

  v = var_lookup (name, global_variables);
  /* This starts at the current scope, just like find_global_variable; should we
     use find_global_variable_nameref here? */
  nv = (v && nameref_p (v)) ? find_variable_nameref (v) : (SHELL_VAR *)NULL;

  r = nv ? makunbound (nv->name, shell_variables) : makunbound (name, global_variables);
  return r;
}

int
unbind_global_variable_noref (const char *name)
{
  SHELL_VAR *v;

  v = var_lookup (name, global_variables);
  if (v)
    return makunbound (name, global_variables);
  return 0;
}
 
int
check_unbind_variable (const char *name)
{
  SHELL_VAR *v;

  v = find_variable (name);
  if (v && readonly_p (v))
    {
      internal_error (_("%s: cannot unset: readonly %s"), name, "variable");
      return -2;
    }
  else if (v && non_unsettable_p (v))
    {
      internal_error (_("%s: cannot unset"), name);
      return -2;
    }
  return (unbind_variable (name));
}

/* Unset the shell function named NAME. */
int
unbind_func (const char *name)
{
  BUCKET_CONTENTS *elt;
  SHELL_VAR *func;

  elt = hash_remove (name, shell_functions, 0);

  if (elt == 0)
    return -1;

#if defined (PROGRAMMABLE_COMPLETION)
  set_itemlist_dirty (&it_functions);
#endif

  func = (SHELL_VAR *)elt->data;
  if (func)
    {
      if (exported_p (func))
	array_needs_making++;
      dispose_variable (func);
    }

  free (elt->key);
  free (elt);

  return 0;  
}

#if defined (DEBUGGER)
int
unbind_function_def (const char *name)
{
  BUCKET_CONTENTS *elt;
  FUNCTION_DEF *funcdef;

  elt = hash_remove (name, shell_function_defs, 0);

  if (elt == 0)
    return -1;

  funcdef = (FUNCTION_DEF *)elt->data;
  if (funcdef)
    dispose_function_def (funcdef);

  free (elt->key);
  free (elt);

  return 0;  
}
#endif /* DEBUGGER */

int
delete_var (const char *name, VAR_CONTEXT *vc)
{
  BUCKET_CONTENTS *elt;
  SHELL_VAR *old_var;
  VAR_CONTEXT *v;

  for (elt = (BUCKET_CONTENTS *)NULL, v = vc; v; v = v->down)
    if (elt = hash_remove (name, v->table, 0))
      break;

  if (elt == 0)
    return (-1);

  old_var = (SHELL_VAR *)elt->data;
  free (elt->key);
  free (elt);

  dispose_variable (old_var);
  return (0);
}

/* Make the variable associated with NAME go away.  HASH_LIST is the
   hash table from which this variable should be deleted (either
   shell_variables or shell_functions).
   Returns non-zero if the variable couldn't be found. */
int
makunbound (const char *name, VAR_CONTEXT *vc)
{
  BUCKET_CONTENTS *elt, *new_elt;
  SHELL_VAR *old_var;
  VAR_CONTEXT *v;
  char *t;

  for (elt = (BUCKET_CONTENTS *)NULL, v = vc; v; v = v->down)
    if (elt = hash_remove (name, v->table, 0))
      break;

  if (elt == 0)
    return (-1);

  old_var = (SHELL_VAR *)elt->data;

  if (old_var && exported_p (old_var))
    array_needs_making++;

  /* If we're unsetting a local variable and we're still executing inside
     the function, just mark the variable as invisible.  The function
     eventually called by pop_var_context() will clean it up later.  This
     must be done so that if the variable is subsequently assigned a new
     value inside the function, the `local' attribute is still present.
     We also need to add it back into the correct hash table. */
  if (old_var && local_p (old_var) &&
	(old_var->context == variable_context || (localvar_unset && old_var->context < variable_context)))
    {
      if (nofree_p (old_var))
	var_setvalue (old_var, (char *)NULL);
#if defined (ARRAY_VARS)
      else if (array_p (old_var))
	array_dispose (array_cell (old_var));
      else if (assoc_p (old_var))
	assoc_dispose (assoc_cell (old_var));
#endif
      else if (nameref_p (old_var))
	FREE (nameref_cell (old_var));
      else
	FREE (value_cell (old_var));
      /* Reset the attributes.  Preserve the export attribute if the variable
	 came from a temporary environment.  Make sure it stays local, and
	 make it invisible. */ 
      old_var->attributes = (exported_p (old_var) && tempvar_p (old_var)) ? att_exported : 0;
      VSETATTR (old_var, att_local);
      VSETATTR (old_var, att_invisible);
      var_setvalue (old_var, (char *)NULL);
      INVALIDATE_EXPORTSTR (old_var);

      new_elt = hash_insert (savestring (old_var->name), v->table, 0);
      new_elt->data = (PTR_T)old_var;
      stupidly_hack_special_variables (old_var->name);

      free (elt->key);
      free (elt);
      return (0);
    }

  /* Have to save a copy of name here, because it might refer to
     old_var->name.  If so, stupidly_hack_special_variables will
     reference freed memory. */
  t = savestring (name);

  free (elt->key);
  free (elt);

  dispose_variable (old_var);
  stupidly_hack_special_variables (t);
  free (t);

  return (0);
}

/* Get rid of all of the variables in the current context. */
void
kill_all_local_variables ()
{
  VAR_CONTEXT *vc;

  for (vc = shell_variables; vc; vc = vc->down)
    if (vc_isfuncenv (vc) && vc->scope == variable_context)
      break;
  if (vc == 0)
    return;		/* XXX */

  if (vc->table && vc_haslocals (vc))
    {
      delete_all_variables (vc->table);
      hash_dispose (vc->table);
    }
  vc->table = (HASH_TABLE *)NULL;
}

void
free_variable_hash_data (PTR_T data)
{
  SHELL_VAR *var;

  var = (SHELL_VAR *)data;
  dispose_variable (var);
}

/* Delete the entire contents of the hash table. */
void
delete_all_variables (HASH_TABLE *hashed_vars)
{
  hash_flush (hashed_vars, free_variable_hash_data);
}

/* **************************************************************** */
/*								    */
/*		     Setting variable attributes		    */
/*								    */
/* **************************************************************** */

#define FIND_OR_MAKE_VARIABLE(name, entry) \
  do \
    { \
      entry = find_variable (name); \
      if (!entry) \
	{ \
	  entry = bind_variable (name, "", 0); \
	  if (entry) entry->attributes |= att_invisible; \
	} \
    } \
  while (0)

/* Make the variable associated with NAME be readonly.
   If NAME does not exist yet, create it. */
void
set_var_read_only (char *name)
{
  SHELL_VAR *entry;

  FIND_OR_MAKE_VARIABLE (name, entry);
  VSETATTR (entry, att_readonly);
}

#ifdef INCLUDE_UNUSED
/* Make the function associated with NAME be readonly.
   If NAME does not exist, we just punt, like auto_export code below. */
void
set_func_read_only (const char *name)
{
  SHELL_VAR *entry;

  entry = find_function (name);
  if (entry)
    VSETATTR (entry, att_readonly);
}

/* Make the variable associated with NAME be auto-exported.
   If NAME does not exist yet, create it. */
void
set_var_auto_export (char *name)
{
  SHELL_VAR *entry;

  FIND_OR_MAKE_VARIABLE (name, entry);
  set_auto_export (entry);
}

/* Make the function associated with NAME be auto-exported. */
void
set_func_auto_export (const char *name)
{
  SHELL_VAR *entry;

  entry = find_function (name);
  if (entry)
    set_auto_export (entry);
}
#endif

/* **************************************************************** */
/*								    */
/*		     Creating lists of variables		    */
/*								    */
/* **************************************************************** */

static VARLIST *
vlist_alloc (int nentries)
{
  VARLIST  *vlist;

  vlist = (VARLIST *)xmalloc (sizeof (VARLIST));
  vlist->list = (SHELL_VAR **)xmalloc ((nentries + 1) * sizeof (SHELL_VAR *));
  vlist->list_size = nentries;
  vlist->list_len = 0;
  vlist->list[0] = (SHELL_VAR *)NULL;

  return vlist;
}

static VARLIST *
vlist_realloc (VARLIST *vlist, int n)
{
  if (vlist == 0)
    return (vlist = vlist_alloc (n));
  if (n > vlist->list_size)
    {
      vlist->list_size = n;
      vlist->list = (SHELL_VAR **)xrealloc (vlist->list, (vlist->list_size + 1) * sizeof (SHELL_VAR *));
    }
  return vlist;
}

static void
vlist_add (VARLIST *vlist, SHELL_VAR *var, int flags)
{
  register int i;

  for (i = 0; i < vlist->list_len; i++)
    if (STREQ (var->name, vlist->list[i]->name))
      break;
  if (i < vlist->list_len)
    return;

  if (i >= vlist->list_size)
    vlist = vlist_realloc (vlist, vlist->list_size + 16);

  vlist->list[vlist->list_len++] = var;
  vlist->list[vlist->list_len] = (SHELL_VAR *)NULL;
}

/* Map FUNCTION over the variables in VAR_HASH_TABLE.  Return an array of the
   variables for which FUNCTION returns a non-zero value.  A NULL value
   for FUNCTION means to use all variables. */
SHELL_VAR **
map_over (sh_var_map_func_t *function, VAR_CONTEXT *vc)
{
  VAR_CONTEXT *v;
  VARLIST *vlist;
  SHELL_VAR **ret;
  int nentries;

  for (nentries = 0, v = vc; v; v = v->down)
    nentries += HASH_ENTRIES (v->table);

  if (nentries == 0)
    return (SHELL_VAR **)NULL;

  vlist = vlist_alloc (nentries);

  for (v = vc; v; v = v->down)
    flatten (v->table, function, vlist, 0);

  ret = vlist->list;
  free (vlist);
  return ret;
}

SHELL_VAR **
map_over_funcs (sh_var_map_func_t *function)
{
  VARLIST *vlist;
  SHELL_VAR **ret;

  if (shell_functions == 0 || HASH_ENTRIES (shell_functions) == 0)
    return ((SHELL_VAR **)NULL);

  vlist = vlist_alloc (HASH_ENTRIES (shell_functions));

  flatten (shell_functions, function, vlist, 0);

  ret = vlist->list;
  free (vlist);
  return ret;
}

/* Flatten VAR_HASH_TABLE, applying FUNC to each member and adding those
   elements for which FUNC succeeds to VLIST->list.  FLAGS is reserved
   for future use.  Only unique names are added to VLIST.  If FUNC is
   NULL, each variable in VAR_HASH_TABLE is added to VLIST.  If VLIST is
   NULL, FUNC is applied to each SHELL_VAR in VAR_HASH_TABLE.  If VLIST
   and FUNC are both NULL, nothing happens. */
void
flatten (HASH_TABLE *var_hash_table, sh_var_map_func_t *func, VARLIST *vlist, int flags)
{
  register int i;
  register BUCKET_CONTENTS *tlist;
  int r;
  SHELL_VAR *var;

  if (var_hash_table == 0 || (HASH_ENTRIES (var_hash_table) == 0) || (vlist == 0 && func == 0))
    return;

  for (i = 0; i < var_hash_table->nbuckets; i++)
    {
      for (tlist = hash_items (i, var_hash_table); tlist; tlist = tlist->next)
	{
	  var = (SHELL_VAR *)tlist->data;

	  r = func ? (*func) (var) : 1;
	  if (r && vlist)
	    vlist_add (vlist, var, flags);
	}
    }
}

void
sort_variables (SHELL_VAR **array)
{
  qsort (array, strvec_len ((char **)array), sizeof (SHELL_VAR *), (QSFUNC *)qsort_var_comp);
}

static int
qsort_var_comp (SHELL_VAR **var1, SHELL_VAR **var2)
{
  int result;

  if ((result = (*var1)->name[0] - (*var2)->name[0]) == 0)
    result = strcmp ((*var1)->name, (*var2)->name);

  return (result);
}

/* Apply FUNC to each variable in SHELL_VARIABLES, adding each one for
   which FUNC succeeds to an array of SHELL_VAR *s.  Returns the array. */
static SHELL_VAR **
vapply (sh_var_map_func_t *func)
{
  SHELL_VAR **list;

  list = map_over (func, shell_variables);
  if (list /* && posixly_correct */)
    sort_variables (list);
  return (list);
}

/* Apply FUNC to each variable in SHELL_FUNCTIONS, adding each one for
   which FUNC succeeds to an array of SHELL_VAR *s.  Returns the array. */
static SHELL_VAR **
fapply (sh_var_map_func_t *func)
{
  SHELL_VAR **list;

  list = map_over_funcs (func);
  if (list /* && posixly_correct */)
    sort_variables (list);
  return (list);
}

/* Create a NULL terminated array of all the shell variables. */
SHELL_VAR **
all_shell_variables ()
{
  return (vapply ((sh_var_map_func_t *)NULL));
}

/* Create a NULL terminated array of all the shell functions. */
SHELL_VAR **
all_shell_functions ()
{
  return (fapply ((sh_var_map_func_t *)NULL));
}

static int
visible_var (SHELL_VAR *var)
{
  return (invisible_p (var) == 0);
}

SHELL_VAR **
all_visible_functions ()
{
  return (fapply (visible_var));
}

SHELL_VAR **
all_visible_variables ()
{
  return (vapply (visible_var));
}

/* Return non-zero if the variable VAR is visible and exported.  Array
   variables cannot be exported. */
int
visible_and_exported (SHELL_VAR *var)
{
  return (invisible_p (var) == 0 && exported_p (var));
}

/* Candidate variables for the export environment are either valid variables
   with the export attribute or invalid variables inherited from the initial
   environment and simply passed through. */
int
export_environment_candidate (SHELL_VAR *var)
{
  return (exported_p (var) && (invisible_p (var) == 0 || imported_p (var)));
}

/* Return non-zero if VAR is a local variable in the current context and
   is exported. */
static int
local_and_exported (SHELL_VAR *var)
{
  return (invisible_p (var) == 0 && local_p (var) && var->context == variable_context && exported_p (var));
}

SHELL_VAR **
all_exported_variables ()
{
  return (vapply (visible_and_exported));
}

SHELL_VAR **
local_exported_variables ()
{
  return (vapply (local_and_exported));
}

static int
variable_in_context (SHELL_VAR *var)
{
  return (local_p (var) && var->context == variable_context);
}

static int
visible_variable_in_context (SHELL_VAR *var)
{
  return (invisible_p (var) == 0 && local_p (var) && var->context == variable_context);
}

SHELL_VAR **
all_local_variables (int visible_only)
{
  VARLIST *vlist;
  SHELL_VAR **ret;
  VAR_CONTEXT *vc;

  vc = shell_variables;
  for (vc = shell_variables; vc; vc = vc->down)
    if (vc_isfuncenv (vc) && vc->scope == variable_context)
      break;

  if (vc == 0)
    {
      internal_error (_("all_local_variables: no function context at current scope"));
      return (SHELL_VAR **)NULL;
    }
  if (vc->table == 0 || HASH_ENTRIES (vc->table) == 0 || vc_haslocals (vc) == 0)
    return (SHELL_VAR **)NULL;
    
  vlist = vlist_alloc (HASH_ENTRIES (vc->table));

  if (visible_only)
    flatten (vc->table, visible_variable_in_context, vlist, 0);
  else
    flatten (vc->table, variable_in_context, vlist, 0);

  ret = vlist->list;
  free (vlist);
  if (ret)
    sort_variables (ret);
  return ret;
}

#if defined (ARRAY_VARS)
/* Return non-zero if the variable VAR is visible and an array. */
static int
visible_array_vars (SHELL_VAR *var)
{
  return (invisible_p (var) == 0 && (array_p (var) || assoc_p (var)));
}

SHELL_VAR **
all_array_variables ()
{
  return (vapply (visible_array_vars));
}
#endif /* ARRAY_VARS */

char **
all_variables_matching_prefix (const char *prefix)
{
  SHELL_VAR **varlist;
  char **rlist;
  int vind, rind, plen;

  plen = STRLEN (prefix);
  varlist = all_visible_variables ();
  for (vind = 0; varlist && varlist[vind]; vind++)
    ;
  if (varlist == 0 || vind == 0)
    return ((char **)NULL);
  rlist = strvec_create (vind + 1);
  for (vind = rind = 0; varlist[vind]; vind++)
    {
      if (plen == 0 || STREQN (prefix, varlist[vind]->name, plen))
	rlist[rind++] = savestring (varlist[vind]->name);
    }
  rlist[rind] = (char *)0;
  free (varlist);

  return rlist;
}

