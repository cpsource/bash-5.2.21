/* variables_scope.c -- variable scope management, extracted from variables.c */
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
#include "variables_scope.h"
#include "variables_export.h"
#include "variables_special.h"

#define VARIABLES_HASH_BUCKETS	1024	/* must be power of two */
#define TEMPENV_HASH_BUCKETS	4	/* must be power of two */

/* Functions now extern from variables.c */
extern SHELL_VAR *bind_variable_internal PARAMS((const char *, char *, HASH_TABLE *, int, int));
extern void free_variable_hash_data PARAMS((PTR_T));
extern void flatten PARAMS((HASH_TABLE *, sh_var_map_func_t *, VARLIST *, int));

/* Forward declarations for static functions */
static int set_context PARAMS((SHELL_VAR *));
static void push_func_var PARAMS((PTR_T));
static void push_builtin_var PARAMS((PTR_T));
static void push_exported_var PARAMS((PTR_T));
static void delete_local_contexts PARAMS((VAR_CONTEXT *));
static inline void push_posix_tempvar_internal PARAMS((SHELL_VAR *, int));
static char **save_dollar_vars PARAMS((void));
static void restore_dollar_vars PARAMS((char **));
static void free_dollar_vars PARAMS((void));
static void free_saved_dollar_vars PARAMS((char **));

/* **************************************************************** */
/*								    */
/*		      Managing variable contexts		    */
/*								    */
/* **************************************************************** */

/* Allocate and return a new variable context with NAME and FLAGS.
   NAME can be NULL. */

VAR_CONTEXT *
new_var_context (char *name, int flags)
{
  VAR_CONTEXT *vc;

  vc = (VAR_CONTEXT *)xmalloc (sizeof (VAR_CONTEXT));
  vc->name = name ? savestring (name) : (char *)NULL;
  vc->scope = variable_context;
  vc->flags = flags;

  vc->up = vc->down = (VAR_CONTEXT *)NULL;
  vc->table = (HASH_TABLE *)NULL;

  return vc;
}

/* Free a variable context and its data, including the hash table.  Dispose
   all of the variables. */
void
dispose_var_context (VAR_CONTEXT *vc)
{
  FREE (vc->name);

  if (vc->table)
    {
      delete_all_variables (vc->table);
      hash_dispose (vc->table);
    }

  free (vc);
}

/* Set VAR's scope level to the current variable context. */
static int
set_context (SHELL_VAR *var)
{
  return (var->context = variable_context);
}

/* Make a new variable context with NAME and FLAGS and a HASH_TABLE of
   temporary variables, and push it onto shell_variables.  This is
   for shell functions. */
VAR_CONTEXT *
push_var_context (char *name, int flags, HASH_TABLE *tempvars)
{
  VAR_CONTEXT *vc;
  int posix_func_behavior;

  /* As of IEEE Std 1003.1-2017, assignment statements preceding shell
     functions no longer behave like assignment statements preceding
     special builtins, and do not persist in the current shell environment.
     This is austin group interp #654, though nobody implements it yet. */
  posix_func_behavior = 0;

  vc = new_var_context (name, flags);
  /* Posix interp 1009, temporary assignments preceding function calls modify
     the current environment *before* the command is executed. */
  if (posix_func_behavior && (flags & VC_FUNCENV) && tempvars == temporary_env)
    merge_temporary_env ();
  else if (tempvars)
    {
      vc->table = tempvars;
      /* Have to do this because the temp environment was created before
	 variable_context was incremented. */
      /* XXX - only need to do it if flags&VC_FUNCENV */
      flatten (tempvars, set_context, (VARLIST *)NULL, 0);
      vc->flags |= VC_HASTMPVAR;
    }
  vc->down = shell_variables;
  shell_variables->up = vc;

  return (shell_variables = vc);
}

/* This can be called from one of two code paths:
	1. pop_scope, which implements the posix rules for propagating variable
	   assignments preceding special builtins to the surrounding scope
	   (push_builtin_var -- isbltin == 1);
	2. pop_var_context, which is called from pop_context and implements the
	   posix rules for propagating variable assignments preceding function
	   calls to the surrounding scope (push_func_var -- isbltin == 0)

  It takes variables out of a temporary environment hash table. We take the
  variable in data.
*/

static inline void
push_posix_tempvar_internal (SHELL_VAR *var, int isbltin)
{
  SHELL_VAR *v;
  int posix_var_behavior;

  /* As of IEEE Std 1003.1-2017, assignment statements preceding shell
     functions no longer behave like assignment statements preceding
     special builtins, and do not persist in the current shell environment.
     This is austin group interp #654, though nobody implements it yet. */
  posix_var_behavior = posixly_correct && isbltin;
  v = 0;

  if (local_p (var) && STREQ (var->name, "-"))
    {
      set_current_options (value_cell (var));
      set_shellopts ();
    }
  /* This takes variable assignments preceding special builtins that can execute
     multiple commands (source, eval, etc.) and performs the equivalent of
     an assignment statement to modify the closest enclosing variable (the
     posix "current execution environment"). This makes the behavior the same
     as push_posix_temp_var; but the circumstances of calling are slightly
     different. */
  else if (tempvar_p (var) && posix_var_behavior)
    {
      /* similar to push_posix_temp_var */
      v = bind_variable (var->name, value_cell (var), ASS_FORCE|ASS_NOLONGJMP);
      if (v)
	{
	  v->attributes |= var->attributes;
	  if (v->context == 0)
	    v->attributes &= ~(att_tempvar|att_propagate);
	  /* XXX - set att_propagate here if v->context > 0? */
	}
    }
  else if (tempvar_p (var) && propagate_p (var))
    {
      /* Make sure we have a hash table to store the variable in while it is
	 being propagated down to the global variables table.  Create one if
	 we have to */
      if ((vc_isfuncenv (shell_variables) || vc_istempenv (shell_variables)) && shell_variables->table == 0)
	shell_variables->table = hash_create (VARIABLES_HASH_BUCKETS);
      v = bind_variable_internal (var->name, value_cell (var), shell_variables->table, 0, 0);
      /* XXX - should we set v->context here? */
      if (v)
	v->context = shell_variables->scope;
      if (shell_variables == global_variables)
	var->attributes &= ~(att_tempvar|att_propagate);
      else
	shell_variables->flags |= VC_HASTMPVAR;
      if (v)
	v->attributes |= var->attributes;
    }
  else
    stupidly_hack_special_variables (var->name);	/* XXX */

#if defined (ARRAY_VARS)
  if (v && (array_p (var) || assoc_p (var)))
    {
      FREE (value_cell (v));
      if (array_p (var))
	var_setarray (v, array_copy (array_cell (var)));
      else
	var_setassoc (v, assoc_copy (assoc_cell (var)));
    }
#endif	  

  dispose_variable (var);
}

static void
push_func_var (PTR_T data)
{
  SHELL_VAR *var;

  var = (SHELL_VAR *)data;
  push_posix_tempvar_internal (var, 0);
}

static void
push_builtin_var (PTR_T data)
{
  SHELL_VAR *var;

  var = (SHELL_VAR *)data;
  push_posix_tempvar_internal (var, 1);
}

/* Pop the top context off of VCXT and dispose of it, returning the rest of
   the stack. */
void
pop_var_context ()
{
  VAR_CONTEXT *ret, *vcxt;

  vcxt = shell_variables;
  if (vc_isfuncenv (vcxt) == 0)
    {
      internal_error (_("pop_var_context: head of shell_variables not a function context"));
      return;
    }

  if (ret = vcxt->down)
    {
      ret->up = (VAR_CONTEXT *)NULL;
      shell_variables = ret;
      if (vcxt->table)
	hash_flush (vcxt->table, push_func_var);
      dispose_var_context (vcxt);
    }
  else
    internal_error (_("pop_var_context: no global_variables context"));
}

static void
delete_local_contexts (VAR_CONTEXT *vcxt)
{
  VAR_CONTEXT *v, *t;

  for (v = vcxt; v != global_variables; v = t)
    {
      t = v->down;
      dispose_var_context (v);
    }
}

/* Delete the HASH_TABLEs for all variable contexts beginning at VCXT, and
   all of the VAR_CONTEXTs except GLOBAL_VARIABLES. */
void
delete_all_contexts (VAR_CONTEXT *vcxt)
{
  delete_local_contexts (vcxt);
  delete_all_variables (global_variables->table);
  shell_variables = global_variables;
}

/* Reset the context so we are not executing in a shell function. Only call
   this if you are getting ready to exit the shell. */
void
reset_local_contexts ()
{
  delete_local_contexts (shell_variables);
  shell_variables = global_variables;
  variable_context = 0;
}

/* **************************************************************** */
/*								    */
/*	   Pushing and Popping temporary variable scopes	    */
/*								    */
/* **************************************************************** */

VAR_CONTEXT *
push_scope (int flags, HASH_TABLE *tmpvars)
{
  return (push_var_context ((char *)NULL, flags, tmpvars));
}

static void
push_exported_var (PTR_T data)
{
  SHELL_VAR *var, *v;

  var = (SHELL_VAR *)data;

  /* If a temp var had its export attribute set, or it's marked to be
     propagated, bind it in the previous scope before disposing it. */
  /* XXX - This isn't exactly right, because all tempenv variables have the
    export attribute set. */
  if (tempvar_p (var) && exported_p (var) && (var->attributes & att_propagate))
    {
      var->attributes &= ~att_tempvar;		/* XXX */
      v = bind_variable_internal (var->name, value_cell (var), shell_variables->table, 0, 0);
      if (shell_variables == global_variables)
	var->attributes &= ~att_propagate;
      if (v)
	{
	  v->attributes |= var->attributes;
	  v->context = shell_variables->scope;
	}
    }
  else
    stupidly_hack_special_variables (var->name);	/* XXX */

  dispose_variable (var);
}

/* This is called to propagate variables in the temporary environment of a
   special builtin (if IS_SPECIAL != 0) or exported variables that are the
   result of a builtin like `source' or `command' that can operate on the
   variables in its temporary environment. In the first case, we call
   push_builtin_var, which does the right thing. */
void
pop_scope (int is_special)
{
  VAR_CONTEXT *vcxt, *ret;
  int is_bltinenv;

  vcxt = shell_variables;
  if (vc_istempscope (vcxt) == 0)
    {
      internal_error (_("pop_scope: head of shell_variables not a temporary environment scope"));
      return;
    }
  is_bltinenv = vc_isbltnenv (vcxt);	/* XXX - for later */

  ret = vcxt->down;
  if (ret)
    ret->up = (VAR_CONTEXT *)NULL;

  shell_variables = ret;

  /* Now we can take care of merging variables in VCXT into set of scopes
     whose head is RET (shell_variables). */
  FREE (vcxt->name);
  if (vcxt->table)
    {
      if (is_special)
	hash_flush (vcxt->table, push_builtin_var);
      else
	hash_flush (vcxt->table, push_exported_var);
      hash_dispose (vcxt->table);
    }
  free (vcxt);

  sv_ifs ("IFS");	/* XXX here for now */
}

/* **************************************************************** */
/*								    */
/*		 Pushing and Popping function contexts		    */
/*								    */
/* **************************************************************** */

struct saved_dollar_vars {
  char **first_ten;
  WORD_LIST *rest;
  int count;
};

static struct saved_dollar_vars *dollar_arg_stack = (struct saved_dollar_vars *)NULL;
static int dollar_arg_stack_slots;
static int dollar_arg_stack_index;

/* Functions to manipulate dollar_vars array. Need to keep these in sync with
   whatever remember_args() does. */
static char **
save_dollar_vars ()
{
  char **ret;
  int i;

  ret = strvec_create (10);
  for (i = 1; i < 10; i++)
    {
      ret[i] = dollar_vars[i];
      dollar_vars[i] = (char *)NULL;
    }
  return ret;
}

static void
restore_dollar_vars (char **args)
{
  int i;

  for (i = 1; i < 10; i++)
    dollar_vars[i] = args[i];
}

static void
free_dollar_vars ()
{
  int i;

  for (i = 1; i < 10; i++)
    {
      FREE (dollar_vars[i]);
      dollar_vars[i] = (char *)NULL;
    }
}

static void
free_saved_dollar_vars (char **args)
{
  int i;

  for (i = 1; i < 10; i++)
    FREE (args[i]);
}

/* Do what remember_args (xxx, 1) would have done. */
void
clear_dollar_vars ()
{
  free_dollar_vars ();
  dispose_words (rest_of_args);

  rest_of_args = (WORD_LIST *)NULL;
  posparam_count = 0;
}

/* XXX - should always be followed by remember_args () */
void
push_context (name, is_subshell, tempvars)
     char *name;	/* function name */
     int is_subshell;
     HASH_TABLE *tempvars;
{
  if (is_subshell == 0)
    push_dollar_vars ();
  variable_context++;
  push_var_context (name, VC_FUNCENV, tempvars);
}

/* Only called when subshell == 0, so we don't need to check, and can
   unconditionally pop the dollar vars off the stack. */
void
pop_context ()
{
  pop_dollar_vars ();
  variable_context--;
  pop_var_context ();

  sv_ifs ("IFS");		/* XXX here for now */
}

/* Save the existing positional parameters on a stack. */
void
push_dollar_vars ()
{
  if (dollar_arg_stack_index + 2 > dollar_arg_stack_slots)
    {
      dollar_arg_stack = (struct saved_dollar_vars *)
	xrealloc (dollar_arg_stack, (dollar_arg_stack_slots += 10)
		  * sizeof (struct saved_dollar_vars));
    }

  dollar_arg_stack[dollar_arg_stack_index].count = posparam_count;
  dollar_arg_stack[dollar_arg_stack_index].first_ten = save_dollar_vars ();
  dollar_arg_stack[dollar_arg_stack_index++].rest = rest_of_args;
  rest_of_args = (WORD_LIST *)NULL;
  posparam_count = 0;
  
  dollar_arg_stack[dollar_arg_stack_index].first_ten = (char **)NULL;
  dollar_arg_stack[dollar_arg_stack_index].rest = (WORD_LIST *)NULL;  
}

/* Restore the positional parameters from our stack. */
void
pop_dollar_vars ()
{
  if (dollar_arg_stack == 0 || dollar_arg_stack_index == 0)
    return;

  /* Wipe out current values */
  clear_dollar_vars ();

  rest_of_args = dollar_arg_stack[--dollar_arg_stack_index].rest;
  restore_dollar_vars (dollar_arg_stack[dollar_arg_stack_index].first_ten);
  free (dollar_arg_stack[dollar_arg_stack_index].first_ten);
  posparam_count = dollar_arg_stack[dollar_arg_stack_index].count;

  dollar_arg_stack[dollar_arg_stack_index].first_ten = (char **)NULL;
  dollar_arg_stack[dollar_arg_stack_index].rest = (WORD_LIST *)NULL;
  dollar_arg_stack[dollar_arg_stack_index].count = 0;

  set_dollar_vars_unchanged ();
  invalidate_cached_quoted_dollar_at ();
}

void
dispose_saved_dollar_vars ()
{
  if (dollar_arg_stack == 0 || dollar_arg_stack_index == 0)
    return;

  dispose_words (dollar_arg_stack[--dollar_arg_stack_index].rest);    
  free_saved_dollar_vars (dollar_arg_stack[dollar_arg_stack_index].first_ten);	
  free (dollar_arg_stack[dollar_arg_stack_index].first_ten);

  dollar_arg_stack[dollar_arg_stack_index].first_ten = (char **)NULL;  
  dollar_arg_stack[dollar_arg_stack_index].rest = (WORD_LIST *)NULL;
  dollar_arg_stack[dollar_arg_stack_index].count = 0;
}

/* Initialize BASH_ARGV and BASH_ARGC after turning on extdebug after the
   shell is initialized */
void
init_bash_argv ()
{
  if (bash_argv_initialized == 0)
    {
      save_bash_argv ();
      bash_argv_initialized = 1;
    }
}

void
save_bash_argv ()
{
  WORD_LIST *list;

  list = list_rest_of_args ();
  push_args (list);
  dispose_words (list);
}

/* Manipulate the special BASH_ARGV and BASH_ARGC variables. */

void
push_args (WORD_LIST *list)
{
#if defined (ARRAY_VARS) && defined (DEBUGGER)
  SHELL_VAR *bash_argv_v, *bash_argc_v;
  ARRAY *bash_argv_a, *bash_argc_a;
  WORD_LIST *l;
  arrayind_t i;
  char *t;

  GET_ARRAY_FROM_VAR ("BASH_ARGV", bash_argv_v, bash_argv_a);
  GET_ARRAY_FROM_VAR ("BASH_ARGC", bash_argc_v, bash_argc_a);

  for (l = list, i = 0; l; l = l->next, i++)
    array_push (bash_argv_a, l->word->word);

  t = itos (i);
  array_push (bash_argc_a, t);
  free (t);
#endif /* ARRAY_VARS && DEBUGGER */
}

/* Remove arguments from BASH_ARGV array.  Pop top element off BASH_ARGC
   array and use that value as the count of elements to remove from
   BASH_ARGV. */
void
pop_args ()
{
#if defined (ARRAY_VARS) && defined (DEBUGGER)
  SHELL_VAR *bash_argv_v, *bash_argc_v;
  ARRAY *bash_argv_a, *bash_argc_a;
  ARRAY_ELEMENT *ce;
  intmax_t i;

  GET_ARRAY_FROM_VAR ("BASH_ARGV", bash_argv_v, bash_argv_a);
  GET_ARRAY_FROM_VAR ("BASH_ARGC", bash_argc_v, bash_argc_a);

  ce = array_unshift_element (bash_argc_a);
  if (ce == 0 || legal_number (element_value (ce), &i) == 0)
    i = 0;

  for ( ; i > 0; i--)
    array_pop (bash_argv_a);
  array_dispose_element (ce);
#endif /* ARRAY_VARS && DEBUGGER */
}


