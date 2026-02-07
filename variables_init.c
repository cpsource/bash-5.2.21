/* variables_init.c -- shell variable initialization, extracted from variables.c */
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
#include "variables_init.h"
#include "variables_dynamic.h"
#include "variables_special.h"

#define VARIABLES_HASH_BUCKETS	1024	/* must be power of two */
#define FUNCTIONS_HASH_BUCKETS	512

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

/* Forward declarations for static functions */
static void set_machine_vars PARAMS((void));
static void set_home_var PARAMS((void));
static void set_shell_var PARAMS((void));
static char *get_bash_name PARAMS((void));
static void initialize_shell_level PARAMS((void));
static void uidset PARAMS((void));
#if defined (ARRAY_VARS)
static void make_vers_array PARAMS((void));
#endif

#if defined (READLINE)
int winsize_assignment;		/* currently assigning to LINES or COLUMNS */
#endif

void
create_variable_tables ()
{
  if (shell_variables == 0)
    {
      shell_variables = global_variables = new_var_context ((char *)NULL, 0);
      shell_variables->scope = 0;
      shell_variables->table = hash_create (VARIABLES_HASH_BUCKETS);
    }

  if (shell_functions == 0)
    shell_functions = hash_create (FUNCTIONS_HASH_BUCKETS);

#if defined (DEBUGGER)
  if (shell_function_defs == 0)
    shell_function_defs = hash_create (FUNCTIONS_HASH_BUCKETS);
#endif
}

/* Initialize the shell variables from the current environment.
   If PRIVMODE is nonzero, don't import functions from ENV or
   parse $SHELLOPTS. */
void
initialize_shell_variables (char **env, int privmode)
{
  char *name, *string, *temp_string;
  int c, char_index, string_index, string_length, ro;
  SHELL_VAR *temp_var;

  create_variable_tables ();

  for (string_index = 0; env && (string = env[string_index++]); )
    {
      char_index = 0;
      name = string;
      while ((c = *string++) && c != '=')
	;
      if (string[-1] == '=')
	char_index = string - name - 1;

      /* If there are weird things in the environment, like `=xxx' or a
	 string without an `=', just skip them. */
      if (char_index == 0)
	continue;

      /* ASSERT(name[char_index] == '=') */
      name[char_index] = '\0';
      /* Now, name = env variable name, string = env variable value, and
	 char_index == strlen (name) */

      temp_var = (SHELL_VAR *)NULL;

#if defined (FUNCTION_IMPORT)
      /* If exported function, define it now.  Don't import functions from
	 the environment in privileged mode. */
      if (privmode == 0 && read_but_dont_execute == 0 && 
          STREQN (BASHFUNC_PREFIX, name, BASHFUNC_PREFLEN) &&
          STREQ (BASHFUNC_SUFFIX, name + char_index - BASHFUNC_SUFFLEN) &&
	  STREQN ("() {", string, 4))
	{
	  size_t namelen;
	  char *tname;		/* desired imported function name */

	  namelen = char_index - BASHFUNC_PREFLEN - BASHFUNC_SUFFLEN;

	  tname = name + BASHFUNC_PREFLEN;	/* start of func name */
	  tname[namelen] = '\0';		/* now tname == func name */

	  string_length = strlen (string);
	  temp_string = (char *)xmalloc (namelen + string_length + 2);

	  memcpy (temp_string, tname, namelen);
	  temp_string[namelen] = ' ';
	  memcpy (temp_string + namelen + 1, string, string_length + 1);

	  /* Don't import function names that are invalid identifiers from the
	     environment in posix mode, though we still allow them to be defined as
	     shell variables. */
	  if (absolute_program (tname) == 0 && (posixly_correct == 0 || legal_identifier (tname)))
	    parse_and_execute (temp_string, tname, SEVAL_NONINT|SEVAL_NOHIST|SEVAL_FUNCDEF|SEVAL_ONECMD);
	  else
	    free (temp_string);		/* parse_and_execute does this */

	  if (temp_var = find_function (tname))
	    {
	      VSETATTR (temp_var, (att_exported|att_imported));
	      array_needs_making = 1;
	    }
	  else
	    {
	      if (temp_var = bind_invalid_envvar (name, string, 0))
		{
		  VSETATTR (temp_var, (att_exported | att_imported | att_invisible));
		  array_needs_making = 1;
		}
	      last_command_exit_value = EXECUTION_FAILURE;
	      report_error (_("error importing function definition for `%s'"), tname);
	    }

	  /* Restore original suffix */
	  tname[namelen] = BASHFUNC_SUFFIX[0];
	}
      else
#endif /* FUNCTION_IMPORT */
#if defined (ARRAY_VARS)
#  if ARRAY_EXPORT
      /* Array variables may not yet be exported. */
      if (STREQN (BASHARRAY_PREFIX, name, BASHARRAY_PREFLEN) &&
	  STREQN (BASHARRAY_SUFFIX, name + char_index - BASHARRAY_SUFFLEN, BASHARRAY_SUFFLEN) &&
	  *string == '(' && string[1] == '[' && string[strlen (string) - 1] == ')')
	{
	  size_t namelen;
	  char *tname;		/* desired imported array variable name */

	  namelen = char_index - BASHARRAY_PREFLEN - BASHARRAY_SUFFLEN;

	  tname = name + BASHARRAY_PREFLEN;	/* start of variable name */
	  tname[namelen] = '\0';		/* now tname == varname */
	  
	  string_length = 1;
	  temp_string = extract_array_assignment_list (string, &string_length);
	  temp_var = assign_array_from_string (tname, temp_string, 0);
	  FREE (temp_string);
	  if (temp_var)
	    {
	      VSETATTR (temp_var, (att_exported | att_imported));
	      array_needs_making = 1;
	    }
	}
      else if (STREQN (BASHASSOC_PREFIX, name, BASHASSOC_PREFLEN) &&
	  STREQN (BASHASSOC_SUFFIX, name + char_index - BASHASSOC_SUFFLEN, BASHASSOC_SUFFLEN) &&
	  *string == '(' && string[1] == '[' && string[strlen (string) - 1] == ')')
	{
	  size_t namelen;
	  char *tname;		/* desired imported assoc variable name */

	  namelen = char_index - BASHASSOC_PREFLEN - BASHASSOC_SUFFLEN;

	  tname = name + BASHASSOC_PREFLEN;	/* start of variable name */
	  tname[namelen] = '\0';		/* now tname == varname */

	  /* need to make sure it exists as an associative array first */
	  temp_var = find_or_make_array_variable (tname, 2);
	  if (temp_var)
	    {
	      string_length = 1;
	      temp_string = extract_array_assignment_list (string, &string_length);
	      temp_var = assign_array_var_from_string (temp_var, temp_string, 0);
	    }
	  FREE (temp_string);
	  if (temp_var)
	    {
	      VSETATTR (temp_var, (att_exported | att_imported));
	      array_needs_making = 1;
	    }
	}
      else
#  endif /* ARRAY_EXPORT */
#endif
	{
	  ro = 0;
	  /* If we processed a command-line option that caused SHELLOPTS to be
	     set, it may already be set (and read-only) by the time we process
	     the shell's environment. */
	  if (/* posixly_correct &&*/ STREQ (name, "SHELLOPTS"))
	    {
	      temp_var = find_variable ("SHELLOPTS");
	      ro = temp_var && readonly_p (temp_var);
	      if (temp_var)
		VUNSETATTR (temp_var, att_readonly);
	    }
	  if (legal_identifier (name))
	    {
	      temp_var = bind_variable (name, string, 0);
	      if (temp_var)
		{
		  VSETATTR (temp_var, (att_exported | att_imported));
		  if (ro)
		    VSETATTR (temp_var, att_readonly);
		}
	    }
	  else
	    {
	      temp_var = bind_invalid_envvar (name, string, 0);
	      if (temp_var)
		VSETATTR (temp_var, (att_exported | att_imported | att_invisible));
	    }
	  if (temp_var)
	    array_needs_making = 1;
	}

      name[char_index] = '=';
      /* temp_var can be NULL if it was an exported function with a syntax
	 error (a different bug, but it still shouldn't dump core). */
      if (temp_var && function_p (temp_var) == 0)	/* XXX not yet */
	{
	  CACHE_IMPORTSTR (temp_var, name);
	}
    }

  set_pwd ();

  /* Set up initial value of $_ */
  temp_var = set_if_not ("_", dollar_vars[0]);

  /* Remember this pid. */
  dollar_dollar_pid = getpid ();

  /* Now make our own defaults in case the vars that we think are
     important are missing. */
  temp_var = set_if_not ("PATH", DEFAULT_PATH_VALUE);
  temp_var = set_if_not ("TERM", "dumb");

#if defined (__QNX__)
  /* set node id -- don't import it from the environment */
  {
    char node_name[22];
#  if defined (__QNXNTO__)
    netmgr_ndtostr(ND2S_LOCAL_STR, ND_LOCAL_NODE, node_name, sizeof(node_name));
#  else
    qnx_nidtostr (getnid (), node_name, sizeof (node_name));
#  endif
    temp_var = bind_variable ("NODE", node_name, 0);
    if (temp_var)
      set_auto_export (temp_var);
  }
#endif

  /* set up the prompts. */
  if (interactive_shell)
    {
#if defined (PROMPT_STRING_DECODE)
      set_if_not ("PS1", primary_prompt);
#else
      if (current_user.uid == -1)
	get_current_user_info ();
      set_if_not ("PS1", current_user.euid == 0 ? "# " : primary_prompt);
#endif
      set_if_not ("PS2", secondary_prompt);
    }

  if (current_user.euid == 0)
    bind_variable ("PS4", "+ ", 0);
  else
    set_if_not ("PS4", "+ ");

  /* Don't allow IFS to be imported from the environment. */
  temp_var = bind_variable ("IFS", " \t\n", 0);
  setifs (temp_var);

  /* Magic machine types.  Pretty convenient. */
  set_machine_vars ();

  /* Default MAILCHECK for interactive shells.  Defer the creation of a
     default MAILPATH until the startup files are read, because MAIL
     names a mail file if MAILPATH is not set, and we should provide a
     default only if neither is set. */
  if (interactive_shell)
    {
      temp_var = set_if_not ("MAILCHECK", posixly_correct ? "600" : "60");
      VSETATTR (temp_var, att_integer);
    }

  /* Do some things with shell level. */
  initialize_shell_level ();

  set_ppid ();

  set_argv0 ();

  /* Initialize the `getopts' stuff. */
  temp_var = bind_variable ("OPTIND", "1", 0);
  VSETATTR (temp_var, att_integer);
  getopts_reset (0);
  bind_variable ("OPTERR", "1", 0);
  sh_opterr = 1;

  if (login_shell == 1 && posixly_correct == 0)
    set_home_var ();

  /* Get the full pathname to THIS shell, and set the BASH variable
     to it. */
  name = get_bash_name ();
  temp_var = bind_variable ("BASH", name, 0);
  free (name);

  /* Make the exported environment variable SHELL be the user's login
     shell.  Note that the `tset' command looks at this variable
     to determine what style of commands to output; if it ends in "csh",
     then C-shell commands are output, else Bourne shell commands. */
  set_shell_var ();

  /* Make a variable called BASH_VERSION which contains the version info. */
  bind_variable ("BASH_VERSION", shell_version_string (), 0);
#if defined (ARRAY_VARS)
  make_vers_array ();
#endif

  if (command_execution_string)
    bind_variable ("BASH_EXECUTION_STRING", command_execution_string, 0);

  /* Find out if we're supposed to be in Posix.2 mode via an
     environment variable. */
  temp_var = find_variable ("POSIXLY_CORRECT");
  if (!temp_var)
    temp_var = find_variable ("POSIX_PEDANTIC");
  if (temp_var && imported_p (temp_var))
    sv_strict_posix (temp_var->name);

#if defined (HISTORY)
  /* Set history variables to defaults, and then do whatever we would
     do if the variable had just been set.  Do this only in the case
     that we are remembering commands on the history list. */
  if (remember_on_history)
    {
      name = bash_tilde_expand (posixly_correct ? "~/.sh_history" : "~/.bash_history", 0);

      set_if_not ("HISTFILE", name);
      free (name);
    }
#endif /* HISTORY */

  /* Seed the random number generators. */
  seedrand ();
  seedrand32 ();

  /* Handle some "special" variables that we may have inherited from a
     parent shell. */
  if (interactive_shell)
    {
      temp_var = find_variable ("IGNOREEOF");
      if (!temp_var)
	temp_var = find_variable ("ignoreeof");
      if (temp_var && imported_p (temp_var))
	sv_ignoreeof (temp_var->name);
    }

#if defined (HISTORY)
  if (interactive_shell && remember_on_history)
    {
      sv_history_control ("HISTCONTROL");
      sv_histignore ("HISTIGNORE");
      sv_histtimefmt ("HISTTIMEFORMAT");
    }
#endif /* HISTORY */

#if defined (READLINE) && defined (STRICT_POSIX)
  /* POSIXLY_CORRECT will be 1 here if the shell was compiled
     -DSTRICT_POSIX or if POSIXLY_CORRECT was supplied in the shell's
     environment */
  if (interactive_shell && posixly_correct && no_line_editing == 0)
    rl_prefer_env_winsize = 1;
#endif /* READLINE && STRICT_POSIX */

  /* Get the user's real and effective user ids. */
  uidset ();

  temp_var = set_if_not ("BASH_LOADABLES_PATH", DEFAULT_LOADABLE_BUILTINS_PATH);

  temp_var = find_variable ("BASH_XTRACEFD");
  if (temp_var && imported_p (temp_var))
    sv_xtracefd (temp_var->name);

  sv_shcompat ("BASH_COMPAT");

  /* Allow FUNCNEST to be inherited from the environment. */
  sv_funcnest ("FUNCNEST");

  /* Initialize the dynamic variables, and seed their values. */
  initialize_dynamic_variables ();
}

/* **************************************************************** */
/*								    */
/*	     Setting values for special shell variables		    */
/*								    */
/* **************************************************************** */

static void
set_machine_vars ()
{
  SHELL_VAR *temp_var;

  temp_var = set_if_not ("HOSTTYPE", HOSTTYPE);
  temp_var = set_if_not ("OSTYPE", OSTYPE);
  temp_var = set_if_not ("MACHTYPE", MACHTYPE);

  temp_var = set_if_not ("HOSTNAME", current_host_name);
}

/* Set $HOME to the information in the password file if we didn't get
   it from the environment. */

/* This function is not static so the tilde and readline libraries can
   use it. */

static void
set_home_var ()
{
  SHELL_VAR *temp_var;

  temp_var = find_variable ("HOME");
  if (temp_var == 0)
    temp_var = bind_variable ("HOME", sh_get_home_dir (), 0);
#if 0
  VSETATTR (temp_var, att_exported);
#endif
}

/* Set $SHELL to the user's login shell if it is not already set.  Call
   get_current_user_info if we haven't already fetched the shell. */
static void
set_shell_var ()
{
  SHELL_VAR *temp_var;

  temp_var = find_variable ("SHELL");
  if (temp_var == 0)
    {
      if (current_user.shell == 0)
	get_current_user_info ();
      temp_var = bind_variable ("SHELL", current_user.shell, 0);
    }
#if 0
  VSETATTR (temp_var, att_exported);
#endif
}

static char *
get_bash_name ()
{
  char *name;

  if ((login_shell == 1) && RELPATH(shell_name))
    {
      if (current_user.shell == 0)
	get_current_user_info ();
      name = savestring (current_user.shell);
    }
  else if (ABSPATH(shell_name))
    name = savestring (shell_name);
  else if (shell_name[0] == '.' && shell_name[1] == '/')
    {
      /* Fast path for common case. */
      char *cdir;
      int len;

      cdir = get_string_value ("PWD");
      if (cdir)
	{
	  len = strlen (cdir);
	  name = (char *)xmalloc (len + strlen (shell_name) + 1);
	  strcpy (name, cdir);
	  strcpy (name + len, shell_name + 1);
	}
      else
	name = savestring (shell_name);
    }
  else
    {
      char *tname;
      int s;

      tname = find_user_command (shell_name);

      if (tname == 0)
	{
	  /* Try the current directory.  If there is not an executable
	     there, just punt and use the login shell. */
	  s = file_status (shell_name);
	  if (s & FS_EXECABLE)
	    {
	      tname = make_absolute (shell_name, get_string_value ("PWD"));
	      if (*shell_name == '.')
		{
		  name = sh_canonpath (tname, PATH_CHECKDOTDOT|PATH_CHECKEXISTS);
		  if (name == 0)
		    name = tname;
		  else
		    free (tname);
		}
	     else
		name = tname;
	    }
	  else
	    {
	      if (current_user.shell == 0)
		get_current_user_info ();
	      name = savestring (current_user.shell);
	    }
	}
      else
	{
	  name = full_pathname (tname);
	  free (tname);
	}
    }

  return (name);
}

void
adjust_shell_level (int change)
{
  char new_level[5], *old_SHLVL;
  intmax_t old_level;
  SHELL_VAR *temp_var;

  old_SHLVL = get_string_value ("SHLVL");
  if (old_SHLVL == 0 || *old_SHLVL == '\0' || legal_number (old_SHLVL, &old_level) == 0)
    old_level = 0;

  shell_level = old_level + change;
  if (shell_level < 0)
    shell_level = 0;
  else if (shell_level >= 1000)
    {
      internal_warning (_("shell level (%d) too high, resetting to 1"), shell_level);
      shell_level = 1;
    }

  /* We don't need the full generality of itos here. */
  if (shell_level < 10)
    {
      new_level[0] = shell_level + '0';
      new_level[1] = '\0';
    }
  else if (shell_level < 100)
    {
      new_level[0] = (shell_level / 10) + '0';
      new_level[1] = (shell_level % 10) + '0';
      new_level[2] = '\0';
    }
  else if (shell_level < 1000)
    {
      new_level[0] = (shell_level / 100) + '0';
      old_level = shell_level % 100;
      new_level[1] = (old_level / 10) + '0';
      new_level[2] = (old_level % 10) + '0';
      new_level[3] = '\0';
    }

  temp_var = bind_variable ("SHLVL", new_level, 0);
  set_auto_export (temp_var);
}

static void
initialize_shell_level ()
{
  adjust_shell_level (1);
}

/* If we got PWD from the environment, update our idea of the current
   working directory.  In any case, make sure that PWD exists before
   checking it.  It is possible for getcwd () to fail on shell startup,
   and in that case, PWD would be undefined.  If this is an interactive
   login shell, see if $HOME is the current working directory, and if
   that's not the same string as $PWD, set PWD=$HOME. */

void
set_pwd ()
{
  SHELL_VAR *temp_var, *home_var;
  char *temp_string, *home_string, *current_dir;

  home_var = find_variable ("HOME");
  home_string = home_var ? value_cell (home_var) : (char *)NULL;

  temp_var = find_variable ("PWD");
  /* Follow posix rules for importing PWD */
  if (temp_var && imported_p (temp_var) &&
      (temp_string = value_cell (temp_var)) &&
      temp_string[0] == '/' &&
      same_file (temp_string, ".", (struct stat *)NULL, (struct stat *)NULL))
    {
      current_dir = sh_canonpath (temp_string, PATH_CHECKDOTDOT|PATH_CHECKEXISTS);
      if (current_dir == 0)
	current_dir = get_working_directory ("shell_init");
      else
	set_working_directory (current_dir);
      if (posixly_correct && current_dir)
	{
	  temp_var = bind_variable ("PWD", current_dir, 0);
	  set_auto_export (temp_var);
	}  
      free (current_dir);
    }
  else if (home_string && interactive_shell && login_shell &&
	   same_file (home_string, ".", (struct stat *)NULL, (struct stat *)NULL))
    {
      set_working_directory (home_string);
      temp_var = bind_variable ("PWD", home_string, 0);
      set_auto_export (temp_var);
    }
  else
    {
      temp_string = get_working_directory ("shell-init");
      if (temp_string)
	{
	  temp_var = bind_variable ("PWD", temp_string, 0);
	  set_auto_export (temp_var);
	  free (temp_string);
	}
    }

  /* According to the Single Unix Specification, v2, $OLDPWD is an
     `environment variable' and therefore should be auto-exported.  If we
     don't find OLDPWD in the environment, or it doesn't name a directory,
     make a dummy invisible variable for OLDPWD, and mark it as exported. */
  temp_var = find_variable ("OLDPWD");
#if defined (OLDPWD_CHECK_DIRECTORY)
  if (temp_var == 0 || value_cell (temp_var) == 0 || file_isdir (value_cell (temp_var)) == 0)
#else
  if (temp_var == 0 || value_cell (temp_var) == 0)
#endif
    {
      temp_var = bind_variable ("OLDPWD", (char *)NULL, 0);
      VSETATTR (temp_var, (att_exported | att_invisible));
    }
}

/* Make a variable $PPID, which holds the pid of the shell's parent.  */
void
set_ppid ()
{
  char namebuf[INT_STRLEN_BOUND(pid_t) + 1], *name;
  SHELL_VAR *temp_var;

  name = inttostr (getppid (), namebuf, sizeof(namebuf));
  temp_var = find_variable ("PPID");
  if (temp_var)
    VUNSETATTR (temp_var, (att_readonly | att_exported));
  temp_var = bind_variable ("PPID", name, 0);
  VSETATTR (temp_var, (att_readonly | att_integer));
}

static void
uidset ()
{
  char buff[INT_STRLEN_BOUND(uid_t) + 1], *b;
  register SHELL_VAR *v;

  b = inttostr (current_user.uid, buff, sizeof (buff));
  v = find_variable ("UID");
  if (v == 0)
    {
      v = bind_variable ("UID", b, 0);
      VSETATTR (v, (att_readonly | att_integer));
    }

  if (current_user.euid != current_user.uid)
    b = inttostr (current_user.euid, buff, sizeof (buff));

  v = find_variable ("EUID");
  if (v == 0)
    {
      v = bind_variable ("EUID", b, 0);
      VSETATTR (v, (att_readonly | att_integer));
    }
}

#if defined (ARRAY_VARS)
static void
make_vers_array ()
{
  SHELL_VAR *vv;
  ARRAY *av;
  char *s, d[32], b[INT_STRLEN_BOUND(int) + 1];

  unbind_variable_noref ("BASH_VERSINFO");

  vv = make_new_array_variable ("BASH_VERSINFO");
  av = array_cell (vv);
  strcpy (d, dist_version);
  s = strchr (d, '.');
  if (s)
    *s++ = '\0';
  array_insert (av, 0, d);
  array_insert (av, 1, s);
  s = inttostr (patch_level, b, sizeof (b));
  array_insert (av, 2, s);
  s = inttostr (build_version, b, sizeof (b));
  array_insert (av, 3, s);
  array_insert (av, 4, release_status);
  array_insert (av, 5, MACHTYPE);

  VSETATTR (vv, att_readonly);
}
#endif /* ARRAY_VARS */

/* Set the environment variables $LINES and $COLUMNS in response to
   a window size change. */
void
sh_set_lines_and_columns (int lines, int cols)
{
  char val[INT_STRLEN_BOUND(int) + 1], *v;

#if defined (READLINE)
  /* If we are currently assigning to LINES or COLUMNS, don't do anything. */
  if (winsize_assignment)
    return;
#endif

  v = inttostr (lines, val, sizeof (val));
  bind_variable ("LINES", v, 0);

  v = inttostr (cols, val, sizeof (val));
  bind_variable ("COLUMNS", v, 0);
}

/* **************************************************************** */
/*								    */
/*		   Printing variables and values		    */
/*								    */
/* **************************************************************** */

/* Print LIST (a list of shell variables) to stdout in such a way that
   they can be read back in. */
void
print_var_list (register SHELL_VAR **list)
{
  register int i;
  register SHELL_VAR *var;

  for (i = 0; list && (var = list[i]); i++)
    if (invisible_p (var) == 0)
      print_assignment (var);
}

/* Print LIST (a list of shell functions) to stdout in such a way that
   they can be read back in. */
void
print_func_list (register SHELL_VAR **list)
{
  register int i;
  register SHELL_VAR *var;

  for (i = 0; list && (var = list[i]); i++)
    {
      printf ("%s ", var->name);
      print_var_function (var);
      printf ("\n");
    }
}
      
/* Print the value of a single SHELL_VAR.  No newline is
   output, but the variable is printed in such a way that
   it can be read back in. */
void
print_assignment (SHELL_VAR *var)
{
  if (var_isset (var) == 0)
    return;

  if (function_p (var))
    {
      printf ("%s", var->name);
      print_var_function (var);
      printf ("\n");
    }
#if defined (ARRAY_VARS)
  else if (array_p (var))
    print_array_assignment (var, 0);
  else if (assoc_p (var))
    print_assoc_assignment (var, 0);
#endif /* ARRAY_VARS */
  else
    {
      printf ("%s=", var->name);
      print_var_value (var, 1);
      printf ("\n");
    }
}

/* Print the value cell of VAR, a shell variable.  Do not print
   the name, nor leading/trailing newline.  If QUOTE is non-zero,
   and the value contains shell metacharacters, quote the value
   in such a way that it can be read back in. */
void
print_var_value (SHELL_VAR *var, int quote)
{
  char *t;

  if (var_isset (var) == 0)
    return;

  if (quote && posixly_correct == 0 && ansic_shouldquote (value_cell (var)))
    {
      t = ansic_quote (value_cell (var), 0, (int *)0);
      printf ("%s", t);
      free (t);
    }
  else if (quote && sh_contains_shell_metas (value_cell (var)))
    {
      t = sh_single_quote (value_cell (var));
      printf ("%s", t);
      free (t);
    }
  else
    printf ("%s", value_cell (var));
}

/* Print the function cell of VAR, a shell variable.  Do not
   print the name, nor leading/trailing newline. */
void
print_var_function (SHELL_VAR *var)
{
  char *x;

  if (function_p (var) && var_isset (var))
    {
      x = named_function_string ((char *)NULL, function_cell(var), FUNC_MULTILINE|FUNC_EXTERNAL);
      printf ("%s", x);
    }
}


