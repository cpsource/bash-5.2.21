/* variables_special.c -- special variable handlers, extracted from variables.c */

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

#include "variables.h"
#include "variables_special.h"

/*************************************************
 *						 *
 *	Functions to manage special variables	 *
 *						 *
 *************************************************/

/* Extern declarations for variables this code has to manage. */

/* An alist of name.function for each special variable.  Most of the
   functions don't do much, and in fact, this would be faster with a
   switch statement, but by the end of this file, I am sick of switch
   statements. */

#define SET_INT_VAR(name, intvar)  intvar = find_variable (name) != 0

/* This table will be sorted with qsort() the first time it's accessed. */
struct name_and_function {
  char *name;
  sh_sv_func_t *function;
};

static struct name_and_function special_vars[] = {
  { "BASH_COMPAT", sv_shcompat },
  { "BASH_XTRACEFD", sv_xtracefd },

#if defined (JOB_CONTROL)
  { "CHILD_MAX", sv_childmax },
#endif

#if defined (READLINE)
#  if defined (STRICT_POSIX)
  { "COLUMNS", sv_winsize },
#  endif
  { "COMP_WORDBREAKS", sv_comp_wordbreaks },
#endif

  { "EXECIGNORE", sv_execignore },

  { "FUNCNEST", sv_funcnest },

  { "GLOBIGNORE", sv_globignore },

#if defined (HISTORY)
  { "HISTCONTROL", sv_history_control },
  { "HISTFILESIZE", sv_histsize },
  { "HISTIGNORE", sv_histignore },
  { "HISTSIZE", sv_histsize },
  { "HISTTIMEFORMAT", sv_histtimefmt },
#endif

#if defined (__CYGWIN__)
  { "HOME", sv_home },
#endif

#if defined (READLINE)
  { "HOSTFILE", sv_hostfile },
#endif

  { "IFS", sv_ifs },
  { "IGNOREEOF", sv_ignoreeof },

  { "LANG", sv_locale },
  { "LC_ALL", sv_locale },
  { "LC_COLLATE", sv_locale },
  { "LC_CTYPE", sv_locale },
  { "LC_MESSAGES", sv_locale },
  { "LC_NUMERIC", sv_locale },
  { "LC_TIME", sv_locale },

#if defined (READLINE) && defined (STRICT_POSIX)
  { "LINES", sv_winsize },
#endif

  { "MAIL", sv_mail },
  { "MAILCHECK", sv_mail },
  { "MAILPATH", sv_mail },

  { "OPTERR", sv_opterr },
  { "OPTIND", sv_optind },

  { "PATH", sv_path },
  { "POSIXLY_CORRECT", sv_strict_posix },

#if defined (READLINE)
  { "TERM", sv_terminal },
  { "TERMCAP", sv_terminal },
  { "TERMINFO", sv_terminal },
#endif /* READLINE */

  { "TEXTDOMAIN", sv_locale },
  { "TEXTDOMAINDIR", sv_locale },

#if defined (HAVE_TZSET)
  { "TZ", sv_tz },
#endif

#if defined (HISTORY) && defined (BANG_HISTORY)
  { "histchars", sv_histchars },
#endif /* HISTORY && BANG_HISTORY */

  { "ignoreeof", sv_ignoreeof },

  { (char *)0, (sh_sv_func_t *)0 }
};

#define N_SPECIAL_VARS	(sizeof (special_vars) / sizeof (special_vars[0]) - 1)

static int
sv_compare (struct name_and_function *sv1, struct name_and_function *sv2)
{
  int r;

  if ((r = sv1->name[0] - sv2->name[0]) == 0)
    r = strcmp (sv1->name, sv2->name);
  return r;
}

int
find_special_var (const char *name)
{
  register int i, r;

  for (i = 0; special_vars[i].name; i++)
    {
      r = special_vars[i].name[0] - name[0];
      if (r == 0)
	r = strcmp (special_vars[i].name, name);
      if (r == 0)
	return i;
      else if (r > 0)
	/* Can't match any of rest of elements in sorted list.  Take this out
	   if it causes problems in certain environments. */
	break;
    }
  return -1;
}

/* The variable in NAME has just had its state changed.  Check to see if it
   is one of the special ones where something special happens. */
void
stupidly_hack_special_variables (char *name)
{
  static int sv_sorted = 0;
  int i;

  if (sv_sorted == 0)	/* shouldn't need, but it's fairly cheap. */
    {
      qsort (special_vars, N_SPECIAL_VARS, sizeof (special_vars[0]),
		(QSFUNC *)sv_compare);
      sv_sorted = 1;
    }

  i = find_special_var (name);
  if (i != -1)
    (*(special_vars[i].function)) (name);
}

/* Special variables that need hooks to be run when they are unset as part
   of shell reinitialization should have their sv_ functions run here. */
void
reinit_special_variables (void)
{
#if defined (READLINE)
  sv_comp_wordbreaks ("COMP_WORDBREAKS");
#endif
  sv_globignore ("GLOBIGNORE");
  sv_opterr ("OPTERR");
}

void
sv_ifs (char *name)
{
  SHELL_VAR *v;

  v = find_variable ("IFS");
  setifs (v);
}

/* What to do just after the PATH variable has changed. */
void
sv_path (char *name)
{
  /* hash -r */
  phash_flush ();
}

/* What to do just after one of the MAILxxxx variables has changed.  NAME
   is the name of the variable.  This is called with NAME set to one of
   MAIL, MAILCHECK, or MAILPATH.  */
void
sv_mail (char *name)
{
  /* If the time interval for checking the files has changed, then
     reset the mail timer.  Otherwise, one of the pathname vars
     to the users mailbox has changed, so rebuild the array of
     filenames. */
  if (name[4] == 'C')  /* if (strcmp (name, "MAILCHECK") == 0) */
    reset_mail_timer ();
  else
    {
      free_mail_files ();
      remember_mail_dates ();
    }
}

void
sv_funcnest (char *name)
{
  SHELL_VAR *v;
  intmax_t num;

  v = find_variable (name);
  if (v == 0)
    funcnest_max = 0;
  else if (legal_number (value_cell (v), &num) == 0)
    funcnest_max = 0;
  else
    funcnest_max = num;
}

/* What to do when EXECIGNORE changes. */
void
sv_execignore (char *name)
{
  setup_exec_ignore (name);
}

/* What to do when GLOBIGNORE changes. */
void
sv_globignore (char *name)
{
  if (privileged_mode == 0)
    setup_glob_ignore (name);
}

#if defined (READLINE)
void
sv_comp_wordbreaks (char *name)
{
  SHELL_VAR *sv;

  sv = find_variable (name);
  if (sv == 0)
    reset_completer_word_break_chars ();
}

/* What to do just after one of the TERMxxx variables has changed.
   If we are an interactive shell, then try to reset the terminal
   information in readline. */
void
sv_terminal (char *name)
{
  if (interactive_shell && no_line_editing == 0)
    rl_reset_terminal (get_string_value ("TERM"));
}

void
sv_hostfile (char *name)
{
  SHELL_VAR *v;

  v = find_variable (name);
  if (v == 0)
    clear_hostname_list ();
  else
    hostname_list_initialized = 0;
}

#if defined (STRICT_POSIX)
/* In strict posix mode, we allow assignments to LINES and COLUMNS (and values
   found in the initial environment) to override the terminal size reported by
   the kernel. */
void
sv_winsize (char *name)
{
  SHELL_VAR *v;
  intmax_t xd;
  int d;

  if (posixly_correct == 0 || interactive_shell == 0 || no_line_editing)
    return;

  v = find_variable (name);
  if (v == 0 || var_isset (v) == 0)
    rl_reset_screen_size ();
  else
    {
      if (legal_number (value_cell (v), &xd) == 0)
	return;
      winsize_assignment = 1;
      d = xd;			/* truncate */
      if (name[0] == 'L')	/* LINES */
	rl_set_screen_size (d, -1);
      else			/* COLUMNS */
	rl_set_screen_size (-1, d);
      winsize_assignment = 0;
    }
}
#endif /* STRICT_POSIX */
#endif /* READLINE */

/* Update the value of HOME in the export environment so tilde expansion will
   work on cygwin. */
#if defined (__CYGWIN__)
void
sv_home (char *name)
{
  array_needs_making = 1;
  maybe_make_export_env ();
}
#endif

#if defined (HISTORY)
/* What to do after the HISTSIZE or HISTFILESIZE variables change.
   If there is a value for this HISTSIZE (and it is numeric), then stifle
   the history.  Otherwise, if there is NO value for this variable,
   unstifle the history.  If name is HISTFILESIZE, and its value is
   numeric, truncate the history file to hold no more than that many
   lines. */
void
sv_histsize (char *name)
{
  char *temp;
  intmax_t num;
  int hmax;

  temp = get_string_value (name);

  if (temp && *temp)
    {
      if (legal_number (temp, &num))
	{
	  hmax = num;
	  if (hmax < 0 && name[4] == 'S')
	    unstifle_history ();	/* unstifle history if HISTSIZE < 0 */
	  else if (name[4] == 'S')
	    {
	      stifle_history (hmax);
	      hmax = where_history ();
	      if (history_lines_this_session > hmax)
		history_lines_this_session = hmax;
	    }
	  else if (hmax >= 0)	/* truncate HISTFILE if HISTFILESIZE >= 0 */
	    {
	      history_truncate_file (get_string_value ("HISTFILE"), hmax);
	      /* If we just shrank the history file to fewer lines than we've
		 already read, make sure we adjust our idea of how many lines
		 we have read from the file. */
	      if (hmax < history_lines_in_file)
		history_lines_in_file = hmax;
	    }
	}
    }
  else if (name[4] == 'S')
    unstifle_history ();
}

/* What to do after the HISTIGNORE variable changes. */
void
sv_histignore (char *name)
{
  setup_history_ignore (name);
}

/* What to do after the HISTCONTROL variable changes. */
void
sv_history_control (char *name)
{
  char *temp;
  char *val;
  int tptr;

  history_control = 0;
  temp = get_string_value (name);

  if (temp == 0 || *temp == 0)
    return;

  tptr = 0;
  while (val = extract_colon_unit (temp, &tptr))
    {
      if (STREQ (val, "ignorespace"))
	history_control |= HC_IGNSPACE;
      else if (STREQ (val, "ignoredups"))
	history_control |= HC_IGNDUPS;
      else if (STREQ (val, "ignoreboth"))
	history_control |= HC_IGNBOTH;
      else if (STREQ (val, "erasedups"))
	history_control |= HC_ERASEDUPS;

      free (val);
    }
}

#if defined (BANG_HISTORY)
/* Setting/unsetting of the history expansion character. */
void
sv_histchars (char *name)
{
  char *temp;

  temp = get_string_value (name);
  if (temp)
    {
      history_expansion_char = *temp;
      if (temp[0] && temp[1])
	{
	  history_subst_char = temp[1];
	  if (temp[2])
	      history_comment_char = temp[2];
	}
    }
  else
    {
      history_expansion_char = '!';
      history_subst_char = '^';
      history_comment_char = '#';
    }
}
#endif /* BANG_HISTORY */

void
sv_histtimefmt (char *name)
{
  SHELL_VAR *v;

  if (v = find_variable (name))
    {
      if (history_comment_char == 0)
	history_comment_char = '#';
    }
  history_write_timestamps = (v != 0);
}
#endif /* HISTORY */

#if defined (HAVE_TZSET)
void
sv_tz (char *name)
{
  SHELL_VAR *v;

  v = find_variable (name);
  if (v && exported_p (v))
    array_needs_making = 1;
  else if (v == 0)
    array_needs_making = 1;

  if (array_needs_making)
    {
      maybe_make_export_env ();
      tzset ();
    }
}
#endif

/* If the variable exists, then the value of it can be the number
   of times we actually ignore the EOF.  The default is small,
   (smaller than csh, anyway). */
void
sv_ignoreeof (char *name)
{
  SHELL_VAR *tmp_var;
  char *temp;

  eof_encountered = 0;

  tmp_var = find_variable (name);
  ignoreeof = tmp_var && var_isset (tmp_var);
  temp = tmp_var ? value_cell (tmp_var) : (char *)NULL;
  if (temp)
    eof_encountered_limit = (*temp && all_digits (temp)) ? atoi (temp) : 10;
  set_shellopts ();	/* make sure `ignoreeof' is/is not in $SHELLOPTS */
}

void
sv_optind (char *name)
{
  SHELL_VAR *var;
  char *tt;
  int s;

  var = find_variable ("OPTIND");
  tt = var ? get_variable_value (var) : (char *)NULL;

  /* Assume that if var->context < variable_context and variable_context > 0
     then we are restoring the variables's previous state while returning
     from a function. */
  if (tt && *tt)
    {
      s = atoi (tt);

      /* According to POSIX, setting OPTIND=1 resets the internal state
	 of getopt (). */
      if (s < 0 || s == 1)
	s = 0;
    }
  else
    s = 0;
  getopts_reset (s);
}

void
sv_opterr (char *name)
{
  char *tt;

  tt = get_string_value ("OPTERR");
  sh_opterr = (tt && *tt) ? atoi (tt) : 1;
}

void
sv_strict_posix (char *name)
{
  SHELL_VAR *var;

  var = find_variable (name);
  posixly_correct = var && var_isset (var);
  posix_initialize (posixly_correct);
#if defined (READLINE)
  if (interactive_shell)
    posix_readline_initialize (posixly_correct);
#endif /* READLINE */
  set_shellopts ();	/* make sure `posix' is/is not in $SHELLOPTS */
}

void
sv_locale (char *name)
{
  char *v;
  int r;

  v = get_string_value (name);
  if (name[0] == 'L' && name[1] == 'A')	/* LANG */
    r = set_lang (name, v);
  else
    r = set_locale_var (name, v);		/* LC_*, TEXTDOMAIN* */

#if 1
  if (r == 0 && posixly_correct)
    set_exit_status (EXECUTION_FAILURE);
#endif
}

#if defined (ARRAY_VARS)
void
set_pipestatus_array (int *ps, int nproc)
{
  SHELL_VAR *v;
  ARRAY *a;
  ARRAY_ELEMENT *ae;
  register int i;
  char *t, tbuf[INT_STRLEN_BOUND(int) + 1];

  v = find_variable ("PIPESTATUS");
  if (v == 0)
    v = make_new_array_variable ("PIPESTATUS");
  if (array_p (v) == 0)
    return;		/* Do nothing if not an array variable. */
  a = array_cell (v);

  if (a == 0 || array_num_elements (a) == 0)
    {
      for (i = 0; i < nproc; i++)	/* was ps[i] != -1, not i < nproc */
	{
	  t = inttostr (ps[i], tbuf, sizeof (tbuf));
	  array_insert (a, i, t);
	}
      return;
    }

  /* Fast case */
  if (array_num_elements (a) == nproc && nproc == 1)
    {
#ifndef ALT_ARRAY_IMPLEMENTATION
      ae = element_forw (a->head);
#else
      ae = a->elements[0];
#endif
      ARRAY_ELEMENT_REPLACE (ae, itos (ps[0]));
    }
  else if (array_num_elements (a) <= nproc)
    {
      /* modify in array_num_elements members in place, then add */
#ifndef ALT_ARRAY_IMPLEMENTATION
      ae = a->head;
#endif
      for (i = 0; i < array_num_elements (a); i++)
	{
#ifndef ALT_ARRAY_IMPLEMENTATION
	  ae = element_forw (ae);
#else
	  ae = a->elements[i];
#endif
	  ARRAY_ELEMENT_REPLACE (ae, itos (ps[i]));
	}
      /* add any more */
      for ( ; i < nproc; i++)
	{
	  t = inttostr (ps[i], tbuf, sizeof (tbuf));
	  array_insert (a, i, t);
	}
    }
  else
    {
#ifndef ALT_ARRAY_IMPLEMENTATION
      /* deleting elements.  it's faster to rebuild the array. */
      array_flush (a);
      for (i = 0; i < nproc; i++)
	{
	  t = inttostr (ps[i], tbuf, sizeof (tbuf));
	  array_insert (a, i, t);
	}
#else
      /* deleting elements. replace the first NPROC, free the rest */
      for (i = 0; i < nproc; i++)
	{
	  ae = a->elements[i];
	  ARRAY_ELEMENT_REPLACE (ae, itos (ps[i]));
	}
      for ( ; i <= array_max_index (a); i++)
	{
	  array_dispose_element (a->elements[i]);
	  a->elements[i] = (ARRAY_ELEMENT *)NULL;
	}

      /* bookkeeping usually taken care of by array_insert */
      set_max_index (a, nproc - 1);
      set_first_index (a, 0);
      set_num_elements (a, nproc);
#endif /* ALT_ARRAY_IMPLEMENTATION */
    }
}

ARRAY *
save_pipestatus_array (void)
{
  SHELL_VAR *v;
  ARRAY *a;

  v = find_variable ("PIPESTATUS");
  if (v == 0 || array_p (v) == 0 || array_cell (v) == 0)
    return ((ARRAY *)NULL);

  a = array_copy (array_cell (v));

  return a;
}

void
restore_pipestatus_array (ARRAY *a)
{
  SHELL_VAR *v;
  ARRAY *a2;

  v = find_variable ("PIPESTATUS");
  /* XXX - should we still assign even if existing value is NULL? */
  if (v == 0 || array_p (v) == 0 || array_cell (v) == 0)
    return;

  a2 = array_cell (v);
  var_setarray (v, a);

  array_dispose (a2);
}
#endif

void
set_pipestatus_from_exit (int s)
{
#if defined (ARRAY_VARS)
  static int v[2] = { 0, -1 };

  v[0] = s;
  set_pipestatus_array (v, 1);
#endif
}

void
sv_xtracefd (char *name)
{
  SHELL_VAR *v;
  char *t, *e;
  int fd;
  FILE *fp;

  v = find_variable (name);
  if (v == 0)
    {
      xtrace_reset ();
      return;
    }

  t = value_cell (v);
  if (t == 0 || *t == 0)
    xtrace_reset ();
  else
    {
      fd = (int)strtol (t, &e, 10);
      if (e != t && *e == '\0' && sh_validfd (fd))
	{
	  fp = fdopen (fd, "w");
	  if (fp == 0)
	    internal_error (_("%s: %s: cannot open as FILE"), name, value_cell (v));
	  else
	    xtrace_set (fd, fp);
	}
      else
	internal_error (_("%s: %s: invalid value for trace file descriptor"), name, value_cell (v));
    }
}

#define MIN_COMPAT_LEVEL 31

void
sv_shcompat (char *name)
{
  SHELL_VAR *v;
  char *val;
  int tens, ones, compatval;

  v = find_variable (name);
  if (v == 0)
    {
      shell_compatibility_level = DEFAULT_COMPAT_LEVEL;
      set_compatibility_opts ();
      return;
    }
  val = value_cell (v);
  if (val == 0 || *val == '\0')
    {
      shell_compatibility_level = DEFAULT_COMPAT_LEVEL;
      set_compatibility_opts ();
      return;
    }
  /* Handle decimal-like compatibility version specifications: 4.2 */
  if (ISDIGIT (val[0]) && val[1] == '.' && ISDIGIT (val[2]) && val[3] == 0)
    {
      tens = val[0] - '0';
      ones = val[2] - '0';
      compatval = tens*10 + ones;
    }
  /* Handle integer-like compatibility version specifications: 42 */
  else if (ISDIGIT (val[0]) && ISDIGIT (val[1]) && val[2] == 0)
    {
      tens = val[0] - '0';
      ones = val[1] - '0';
      compatval = tens*10 + ones;
    }
  else
    {
compat_error:
      internal_error (_("%s: %s: compatibility value out of range"), name, val);
      shell_compatibility_level = DEFAULT_COMPAT_LEVEL;
      set_compatibility_opts ();
      return;
    }

  if (compatval < MIN_COMPAT_LEVEL || compatval > DEFAULT_COMPAT_LEVEL)
    goto compat_error;

  shell_compatibility_level = compatval;
  set_compatibility_opts ();
}

#if defined (JOB_CONTROL)
void
sv_childmax (char *name)
{
  char *tt;
  int s;

  tt = get_string_value (name);
  s = (tt && *tt) ? atoi (tt) : 0;
  set_maxchild (s);
}
#endif
