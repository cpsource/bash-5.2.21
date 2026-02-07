/* variables_export.c -- export and environment management, extracted from variables.c */
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
#include "variables_export.h"
#include "variables_scope.h"
#include "variables_special.h"

#define VARIABLES_HASH_BUCKETS	1024	/* must be power of two */
#define TEMPENV_HASH_BUCKETS	4	/* must be power of two */

#define BASHFUNC_PREFIX		"BASH_FUNC_"
#define BASHFUNC_PREFLEN	10
#define BASHFUNC_SUFFIX		"%%"
#define BASHFUNC_SUFFLEN	2

#if ARRAY_EXPORT
#define BASHARRAY_PREFIX	"BASH_ARRAY_"
#define BASHARRAY_PREFLEN	11
#define BASHARRAY_SUFFIX	"%%"
#define BASHARRAY_SUFFLEN	2

#define BASHASSOC_PREFIX	"BASH_ASSOC_"
#define BASHASSOC_PREFLEN	11
#define BASHASSOC_SUFFIX	"%%"
#define BASHASSOC_SUFFLEN	2
#endif

/* Functions now extern from variables.c */
extern SHELL_VAR *hash_lookup PARAMS((const char *, HASH_TABLE *));
extern void free_variable_hash_data PARAMS((PTR_T));
extern SHELL_VAR *bind_variable_internal PARAMS((const char *, char *, HASH_TABLE *, int, int));

/* Moved from variables.c */
int export_env_index;
int export_env_size;

/* Forward declarations for static functions */
extern HASH_TABLE *invalid_env;
extern int visible_and_exported PARAMS((SHELL_VAR *));
extern int export_environment_candidate PARAMS((SHELL_VAR *));

SHELL_VAR *bind_tempenv_variable PARAMS((const char *, char *));
static void push_posix_temp_var PARAMS((PTR_T));
static void push_temp_var PARAMS((PTR_T));
static void propagate_temp_var PARAMS((PTR_T));
static void dispose_temporary_env PARAMS((sh_free_func_t *));
char *mk_env_string PARAMS((const char *, const char *, int));
static char **make_env_array_from_var_list PARAMS((SHELL_VAR **));
static char **make_var_export_array PARAMS((VAR_CONTEXT *));
static char **make_func_export_array PARAMS((void));
static void add_temp_array_to_env PARAMS((char **, int, int));
static int n_shell_variables PARAMS((void));

/* **************************************************************** */
/*								    */
/*		 Managing temporary variable scopes		    */
/*								    */
/* **************************************************************** */

/* Make variable NAME have VALUE in the temporary environment. */
SHELL_VAR *
bind_tempenv_variable (const char *name, char *value)
{
  SHELL_VAR *var;

  var = temporary_env ? hash_lookup (name, temporary_env) : (SHELL_VAR *)NULL;

  if (var)
    {
      FREE (value_cell (var));
      var_setvalue (var, savestring (value));
      INVALIDATE_EXPORTSTR (var);
    }

  return (var);
}

/* Find a variable in the temporary environment that is named NAME.
   Return the SHELL_VAR *, or NULL if not found. */
SHELL_VAR *
find_tempenv_variable (const char *name)
{
  return (temporary_env ? hash_lookup (name, temporary_env) : (SHELL_VAR *)NULL);
}

char **tempvar_list;
int tvlist_ind;

/* Take a variable from an assignment statement preceding a posix special
   builtin (including `return') and create a global variable from it. This
   is called from merge_temporary_env, which is only called when in posix
   mode. */
static void
push_posix_temp_var (PTR_T data)
{
  SHELL_VAR *var, *v;
  HASH_TABLE *binding_table;

  var = (SHELL_VAR *)data;

  /* Just like do_assignment_internal(). This makes assignments preceding
     special builtins act like standalone assignment statements when in
     posix mode, satisfying the posix requirement that this affect the
     "current execution environment." */
  v = bind_variable (var->name, value_cell (var), ASS_FORCE|ASS_NOLONGJMP);

  /* XXX - do we need to worry about array variables here? */

  /* If this modifies an existing local variable, v->context will be non-zero.
     If it comes back with v->context == 0, we bound at the global context.
     Set binding_table appropriately. It doesn't matter whether it's correct
     if the variable is local, only that it's not global_variables->table */
  binding_table = v->context ? shell_variables->table : global_variables->table;

  /* global variables are no longer temporary and don't need propagating. */
  if (v->context == 0)
    var->attributes &= ~(att_tempvar|att_propagate);

  if (v)
    {
      v->attributes |= var->attributes;		/* preserve tempvar attribute if appropriate */
      /* If we don't bind a local variable, propagate the value. If we bind a
	 local variable (the "current execution environment"), keep it as local
	 and don't propagate it to the calling environment. */
      if (v->context > 0 && local_p (v) == 0)
	v->attributes |= att_propagate;
      else
	v->attributes &= ~att_propagate;
    }

  if (find_special_var (var->name) >= 0)
    tempvar_list[tvlist_ind++] = savestring (var->name);

  dispose_variable (var);
}

/* Push the variable described by (SHELL_VAR *)DATA down to the next
   variable context from the temporary environment. This can be called
   from one context:
      1. propagate_temp_var: which is called to propagate variables in
	 assignments like `var=value declare -x var' to the surrounding
	 scope.

  In this case, the variable should have the att_propagate flag set and
  we can create variables in the current scope.
*/
static void
push_temp_var (PTR_T data)
{
  SHELL_VAR *var, *v;
  HASH_TABLE *binding_table;

  var = (SHELL_VAR *)data;

  binding_table = shell_variables->table;
  if (binding_table == 0)
    {
      if (shell_variables == global_variables)
	/* shouldn't happen */
	binding_table = shell_variables->table = global_variables->table = hash_create (VARIABLES_HASH_BUCKETS);
      else
	binding_table = shell_variables->table = hash_create (TEMPENV_HASH_BUCKETS);
    }

  v = bind_variable_internal (var->name, value_cell (var), binding_table, 0, ASS_FORCE|ASS_NOLONGJMP);

  /* XXX - should we set the context here?  It shouldn't matter because of how
     assign_in_env works, but we do it anyway. */
  if (v)
    v->context = shell_variables->scope;

  if (binding_table == global_variables->table)		/* XXX */
    var->attributes &= ~(att_tempvar|att_propagate);
  else
    {
      var->attributes |= att_propagate;			/* XXX - propagate more than once? */
      if  (binding_table == shell_variables->table)
	shell_variables->flags |= VC_HASTMPVAR;
    }
  if (v)
    v->attributes |= var->attributes;

  if (find_special_var (var->name) >= 0)
    tempvar_list[tvlist_ind++] = savestring (var->name);

  dispose_variable (var);
}

/* Take a variable described by DATA and push it to the surrounding scope if
   the PROPAGATE attribute is set. That gets set by push_temp_var if we are
   taking a variable like `var=value declare -x var' and propagating it to
   the enclosing scope. */
static void
propagate_temp_var (PTR_T data)
{
  SHELL_VAR *var;

  var = (SHELL_VAR *)data;
  if (tempvar_p (var) && (var->attributes & att_propagate))
    push_temp_var (data);
  else
    {
      if (find_special_var (var->name) >= 0)
	tempvar_list[tvlist_ind++] = savestring (var->name);
      dispose_variable (var);
    }
}

/* Free the storage used in the hash table for temporary
   environment variables.  PUSHF is a function to be called
   to free each hash table entry.  It takes care of pushing variables
   to previous scopes if appropriate.  PUSHF stores names of variables
   that require special handling (e.g., IFS) on tempvar_list, so this
   function can call stupidly_hack_special_variables on all the
   variables in the list when the temporary hash table is destroyed. */
static void
dispose_temporary_env (sh_free_func_t *pushf)
{
  int i;
  HASH_TABLE *disposer;

  tempvar_list = strvec_create (HASH_ENTRIES (temporary_env) + 1);
  tempvar_list[tvlist_ind = 0] = 0;

  disposer = temporary_env;
  temporary_env = (HASH_TABLE *)NULL;

  hash_flush (disposer, pushf);
  hash_dispose (disposer);

  tempvar_list[tvlist_ind] = 0;

  array_needs_making = 1;

  for (i = 0; i < tvlist_ind; i++)
    stupidly_hack_special_variables (tempvar_list[i]);

  strvec_dispose (tempvar_list);
  tempvar_list = 0;
  tvlist_ind = 0;
}

void
dispose_used_env_vars ()
{
  if (temporary_env)
    {
      dispose_temporary_env (propagate_temp_var);
      maybe_make_export_env ();
    }
}

/* Take all of the shell variables in the temporary environment HASH_TABLE
   and make shell variables from them at the current variable context.
   Right now, this is only called in Posix mode to implement the historical
   accident of creating global variables from assignment statements preceding
   special builtins, but we check in case this acquires another caller later. */
void
merge_temporary_env ()
{
  if (temporary_env)
    dispose_temporary_env (posixly_correct ? push_posix_temp_var : push_temp_var);
}

/* Temporary function to use if we want to separate function and special
   builtin behavior. */
void
merge_function_temporary_env ()
{
  if (temporary_env)
    dispose_temporary_env (push_temp_var);
}

void
flush_temporary_env ()
{
  if (temporary_env)
    {
      hash_flush (temporary_env, free_variable_hash_data);
      hash_dispose (temporary_env);
      temporary_env = (HASH_TABLE *)NULL;
    }
}

/* **************************************************************** */
/*								    */
/*	     Creating and manipulating the environment		    */
/*								    */
/* **************************************************************** */

char *
mk_env_string (const char *name, const char *value, int attributes)
{
  size_t name_len, value_len;
  char	*p, *q, *t;
  int isfunc, isarray;

  name_len = strlen (name);
  value_len = STRLEN (value);

  isfunc = attributes & att_function;
#if defined (ARRAY_VARS) && defined (ARRAY_EXPORT)
  isarray = attributes & (att_array|att_assoc);
#endif

  /* If we are exporting a shell function, construct the encoded function
     name. */
  if (isfunc && value)
    {
      p = (char *)xmalloc (BASHFUNC_PREFLEN + name_len + BASHFUNC_SUFFLEN + value_len + 2);
      q = p;
      memcpy (q, BASHFUNC_PREFIX, BASHFUNC_PREFLEN);
      q += BASHFUNC_PREFLEN;
      memcpy (q, name, name_len);
      q += name_len;
      memcpy (q, BASHFUNC_SUFFIX, BASHFUNC_SUFFLEN);
      q += BASHFUNC_SUFFLEN;
    }
#if defined (ARRAY_VARS) && defined (ARRAY_EXPORT)
  else if (isarray && value)
    {
      if (attributes & att_assoc)
	p = (char *)xmalloc (BASHASSOC_PREFLEN + name_len + BASHASSOC_SUFFLEN + value_len + 2);
      else
	p = (char *)xmalloc (BASHARRAY_PREFLEN + name_len + BASHARRAY_SUFFLEN + value_len + 2);
      q = p;
      if (attributes & att_assoc)
	{
	  memcpy (q, BASHASSOC_PREFIX, BASHASSOC_PREFLEN);
	  q += BASHASSOC_PREFLEN;
	}
      else
	{
	  memcpy (q, BASHARRAY_PREFIX, BASHARRAY_PREFLEN);
	  q += BASHARRAY_PREFLEN;
	}
      memcpy (q, name, name_len);
      q += name_len;
      /* These are actually the same currently */
      if (attributes & att_assoc)
        {
	  memcpy (q, BASHASSOC_SUFFIX, BASHASSOC_SUFFLEN);
	  q += BASHARRAY_SUFFLEN;
        }
      else
        {
	  memcpy (q, BASHARRAY_SUFFIX, BASHARRAY_SUFFLEN);
	  q += BASHARRAY_SUFFLEN;
        }
    }
#endif  
  else
    {
      p = (char *)xmalloc (2 + name_len + value_len);
      memcpy (p, name, name_len);
      q = p + name_len;
    }

  q[0] = '=';
  if (value && *value)
    {
      if (isfunc)
	{
	  t = dequote_escapes (value);
	  value_len = STRLEN (t);
	  memcpy (q + 1, t, value_len + 1);
	  free (t);
	}
      else
	memcpy (q + 1, value, value_len + 1);
    }
  else
    q[1] = '\0';

  return (p);
}

#ifdef DEBUG
/* Debugging */
static int
valid_exportstr (SHELL_VAR *v)
{
  char *s;

  s = v->exportstr;
  if (s == 0)
    {
      internal_error (_("%s has null exportstr"), v->name);
      return (0);
    }
  if (legal_variable_starter ((unsigned char)*s) == 0)
    {
      internal_error (_("invalid character %d in exportstr for %s"), *s, v->name);
      return (0);
    }
  for (s = v->exportstr + 1; s && *s; s++)
    {
      if (*s == '=')
	break;
      if (legal_variable_char ((unsigned char)*s) == 0)
	{
	  internal_error (_("invalid character %d in exportstr for %s"), *s, v->name);
	  return (0);
	}
    }
  if (*s != '=')
    {
      internal_error (_("no `=' in exportstr for %s"), v->name);
      return (0);
    }
  return (1);
}
#endif

#if defined (ARRAY_VARS)
#  define USE_EXPORTSTR (value == var->exportstr && array_p (var) == 0 && assoc_p (var) == 0)
#else
#  define USE_EXPORTSTR (value == var->exportstr)
#endif

static char **
make_env_array_from_var_list (SHELL_VAR **vars)
{
  register int i, list_index;
  register SHELL_VAR *var;
  char **list, *value;

  list = strvec_create ((1 + strvec_len ((char **)vars)));

  for (i = 0, list_index = 0; var = vars[i]; i++)
    {
#if defined (__CYGWIN__)
      /* We don't use the exportstr stuff on Cygwin at all. */
      INVALIDATE_EXPORTSTR (var);
#endif

      /* If the value is generated dynamically, generate it here. */
      if (regen_p (var) && var->dynamic_value)
	{
	  var = (*(var->dynamic_value)) (var);
	  INVALIDATE_EXPORTSTR (var);
	}

      if (var->exportstr)
	value = var->exportstr;
      else if (function_p (var))
	value = named_function_string ((char *)NULL, function_cell (var), 0);
#if defined (ARRAY_VARS)
      else if (array_p (var))
#  if ARRAY_EXPORT
	value = array_to_assign (array_cell (var), 0);
#  else
	continue;	/* XXX array vars cannot yet be exported */
#  endif /* ARRAY_EXPORT */
      else if (assoc_p (var))
#  if ARRAY_EXPORT
	value = assoc_to_assign (assoc_cell (var), 0);
#  else
	continue;	/* XXX associative array vars cannot yet be exported */
#  endif /* ARRAY_EXPORT */
#endif
      else
	value = value_cell (var);

      if (value)
	{
	  /* Gee, I'd like to get away with not using savestring() if we're
	     using the cached exportstr... */
	  list[list_index] = USE_EXPORTSTR ? savestring (value)
					   : mk_env_string (var->name, value, var->attributes);

	  if (USE_EXPORTSTR == 0)
	    SAVE_EXPORTSTR (var, list[list_index]);

	  list_index++;
#undef USE_EXPORTSTR

#if defined (ARRAY_VARS) && defined (ARRAY_EXPORT)
	  if (array_p (var) || assoc_p (var))
	    free (value);
#endif
	}
    }

  list[list_index] = (char *)NULL;
  return (list);
}

/* Make an array of assignment statements from the hash table
   HASHED_VARS which contains SHELL_VARs.  Only visible, exported
   variables are eligible. */
static char **
make_var_export_array (VAR_CONTEXT *vcxt)
{
  char **list;
  SHELL_VAR **vars;

#if 0
  vars = map_over (visible_and_exported, vcxt);
#else
  vars = map_over (export_environment_candidate, vcxt);
#endif

  if (vars == 0)
    return (char **)NULL;

  list = make_env_array_from_var_list (vars);

  free (vars);
  return (list);
}

static char **
make_func_export_array ()
{
  char **list;
  SHELL_VAR **vars;

  vars = map_over_funcs (visible_and_exported);
  if (vars == 0)
    return (char **)NULL;

  list = make_env_array_from_var_list (vars);

  free (vars);
  return (list);
}

/* Add ENVSTR to the end of the exported environment, EXPORT_ENV. */
#define add_to_export_env(envstr,do_alloc) \
do \
  { \
    if (export_env_index >= (export_env_size - 1)) \
      { \
	export_env_size += 16; \
	export_env = strvec_resize (export_env, export_env_size); \
	environ = export_env; \
      } \
    export_env[export_env_index++] = (do_alloc) ? savestring (envstr) : envstr; \
    export_env[export_env_index] = (char *)NULL; \
  } while (0)

/* Add ASSIGN to EXPORT_ENV, or supersede a previous assignment in the
   array with the same left-hand side.  Return the new EXPORT_ENV. */
char **
add_or_supercede_exported_var (char *assign, int do_alloc)
{
  register int i;
  int equal_offset;

  equal_offset = assignment (assign, 0);
  if (equal_offset == 0)
    return (export_env);

  /* If this is a function, then only supersede the function definition.
     We do this by including the `=() {' in the comparison, like
     initialize_shell_variables does. */
  if (assign[equal_offset + 1] == '(' &&
     strncmp (assign + equal_offset + 2, ") {", 3) == 0)		/* } */
    equal_offset += 4;

  for (i = 0; i < export_env_index; i++)
    {
      if (STREQN (assign, export_env[i], equal_offset + 1))
	{
	  free (export_env[i]);
	  export_env[i] = do_alloc ? savestring (assign) : assign;
	  return (export_env);
	}
    }
  add_to_export_env (assign, do_alloc);
  return (export_env);
}

static void
add_temp_array_to_env (char **temp_array, int do_alloc, int do_supercede)
{
  register int i;

  if (temp_array == 0)
    return;

  for (i = 0; temp_array[i]; i++)
    {
      if (do_supercede)
	export_env = add_or_supercede_exported_var (temp_array[i], do_alloc);
      else
	add_to_export_env (temp_array[i], do_alloc);
    }

  free (temp_array);
}

/* Make the environment array for the command about to be executed, if the
   array needs making.  Otherwise, do nothing.  If a shell action could
   change the array that commands receive for their environment, then the
   code should `array_needs_making++'.

   The order to add to the array is:
   	temporary_env
   	list of var contexts whose head is shell_variables
  	shell_functions

  This is the shell variable lookup order.  We add only new variable
  names at each step, which allows local variables and variables in
  the temporary environments to shadow variables in the global (or
  any previous) scope.
*/

static int
n_shell_variables ()
{
  VAR_CONTEXT *vc;
  int n;

  for (n = 0, vc = shell_variables; vc; vc = vc->down)
    n += HASH_ENTRIES (vc->table);
  return n;
}

int
chkexport (char *name)
{
  SHELL_VAR *v;

  v = find_variable (name);
  if (v && exported_p (v))
    {
      array_needs_making = 1;
      maybe_make_export_env ();
      return 1;
    }
  return 0;
}

void
maybe_make_export_env ()
{
  register char **temp_array;
  int new_size;
  VAR_CONTEXT *tcxt, *icxt;

  if (array_needs_making)
    {
      if (export_env)
	strvec_flush (export_env);

      /* Make a guess based on how many shell variables and functions we
	 have.  Since there will always be array variables, and array
	 variables are not (yet) exported, this will always be big enough
	 for the exported variables and functions. */
      new_size = n_shell_variables () + HASH_ENTRIES (shell_functions) + 1 +
		 HASH_ENTRIES (temporary_env) + HASH_ENTRIES (invalid_env);
      if (new_size > export_env_size)
	{
	  export_env_size = new_size;
	  export_env = strvec_resize (export_env, export_env_size);
	  environ = export_env;
	}
      export_env[export_env_index = 0] = (char *)NULL;

      /* Make a dummy variable context from the temporary_env, stick it on
	 the front of shell_variables, call make_var_export_array on the
	 whole thing to flatten it, and convert the list of SHELL_VAR *s
	 to the form needed by the environment. */
      if (temporary_env)
	{
	  tcxt = new_var_context ((char *)NULL, 0);
	  tcxt->table = temporary_env;
	  tcxt->down = shell_variables;
	}
      else
	tcxt = shell_variables;

      if (invalid_env)
	{
	  icxt = new_var_context ((char *)NULL, 0);
	  icxt->table = invalid_env;
	  icxt->down = tcxt;
	}
      else
	icxt = tcxt;
      
      temp_array = make_var_export_array (icxt);
      if (temp_array)
	add_temp_array_to_env (temp_array, 0, 0);

      if (icxt != tcxt)
	free (icxt);

      if (tcxt != shell_variables)
	free (tcxt);

#if defined (RESTRICTED_SHELL)
      /* Restricted shells may not export shell functions. */
      temp_array = restricted ? (char **)0 : make_func_export_array ();
#else
      temp_array = make_func_export_array ();
#endif
      if (temp_array)
	add_temp_array_to_env (temp_array, 0, 0);

      array_needs_making = 0;
    }
}

/* This is an efficiency hack.  PWD and OLDPWD are auto-exported, so
   we will need to remake the exported environment every time we
   change directories.  `_' is always put into the environment for
   every external command, so without special treatment it will always
   cause the environment to be remade.

   If there is no other reason to make the exported environment, we can
   just update the variables in place and mark the exported environment
   as no longer needing a remake. */
void
update_export_env_inplace (char *env_prefix, int preflen, char *value)
{
  char *evar;

  evar = (char *)xmalloc (STRLEN (value) + preflen + 1);
  strcpy (evar, env_prefix);
  if (value)
    strcpy (evar + preflen, value);
  export_env = add_or_supercede_exported_var (evar, 0);
}

/* We always put _ in the environment as the name of this command. */
void
put_command_name_into_env (char *command_name)
{
  update_export_env_inplace ("_=", 2, command_name);
}


