/* subst_comsub.c -- Command substitution, extracted from subst.c */

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

#define NEED_FPURGE_DECL

#include "bashtypes.h"
#include <stdio.h>
#include "chartypes.h"
#if defined (HAVE_PWD_H)
#  include <pwd.h>
#endif
#include <signal.h>
#include <errno.h>

#if defined (HAVE_UNISTD_H)
#  include <unistd.h>
#endif

#include "bashansi.h"
#include "posixstat.h"
#include "bashintl.h"

#include "shell.h"
#include "parser.h"
#include "redir.h"
#include "flags.h"
#include "jobs.h"
#include "execute_cmd.h"
#include "filecntl.h"
#include "trap.h"
#include "pathexp.h"
#include "mailcheck.h"

#include "shmbutil.h"
#if defined (HAVE_MBSTR_H) && defined (HAVE_MBSCHR)
#  include <mbstr.h>
#endif
#include "typemax.h"

#include "builtins/getopt.h"
#include "builtins/common.h"

#include "builtins/builtext.h"

#include <tilde/tilde.h>
#include <glob/strmatch.h>

#include "subst.h"
#include "subst_quote.h"
#include "subst_comsub.h"

/* Externs from subst.c not declared in any header */
extern struct fd_bitmap *current_fds_to_close;
extern int wordexp_only;
extern char expand_param_error;
extern WORD_LIST *subst_assign_varlist;
extern WORD_LIST *garglist;
extern pid_t current_command_subst_pid;

/***********************************/
/*				   */
/*	Command Substitution	   */
/*				   */
/***********************************/

#define COMSUB_PIPEBUF	4096

static char *read_comsub PARAMS((int, int, int, int *));

static char *
optimize_cat_file (REDIRECT *r, int quoted, int flags, int *flagp)
{
  char *ret;
  int fd;

  fd = open_redir_file (r, (char **)0);
  if (fd < 0)
    return &expand_param_error;

  ret = read_comsub (fd, quoted, flags, flagp);
  close (fd);

  return ret;
}

static char *
read_comsub (int fd, int quoted, int flags, int *rflag)
{
  char *istring, buf[COMSUB_PIPEBUF], *bufp;
  int c, tflag, skip_ctlesc, skip_ctlnul;
  int mb_cur_max;
  size_t istring_index;
  size_t istring_size;
  ssize_t bufn;
  int nullbyte;
#if defined (HANDLE_MULTIBYTE)
  mbstate_t ps;
  wchar_t wc;
  size_t mblen;
  int i;
#endif

  istring = (char *)NULL;
  istring_index = istring_size = bufn = tflag = 0;

  skip_ctlesc = ifs_cmap[CTLESC];
  skip_ctlnul = ifs_cmap[CTLNUL];

  mb_cur_max = MB_CUR_MAX;
  nullbyte = 0;

  /* Read the output of the command through the pipe. */
  while (1)
    {
      if (fd < 0)
	break;
      if (--bufn <= 0)
	{
	  bufn = zread (fd, buf, sizeof (buf));
	  if (bufn <= 0) 
	    break;
	  bufp = buf;
	}
      c = *bufp++;

      if (c == 0)
	{
#if 1
	  if (nullbyte == 0)
	    {
	      internal_warning ("%s", _("command substitution: ignored null byte in input"));
	      nullbyte = 1;
	    }
#endif
	  continue;
	}

      /* Add the character to ISTRING, possibly after resizing it. */
      RESIZE_MALLOCED_BUFFER (istring, istring_index, mb_cur_max+1, istring_size, 512);

      /* This is essentially quote_string inline */
      if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) /* || c == CTLESC || c == CTLNUL */)
	istring[istring_index++] = CTLESC;
      else if ((flags & PF_ASSIGNRHS) && skip_ctlesc && c == CTLESC)
	istring[istring_index++] = CTLESC;
      /* Escape CTLESC and CTLNUL in the output to protect those characters
	 from the rest of the word expansions (word splitting and globbing.)
	 This is essentially quote_escapes inline. */
      else if (skip_ctlesc == 0 && c == CTLESC)
	istring[istring_index++] = CTLESC;
      else if ((skip_ctlnul == 0 && c == CTLNUL) || (c == ' ' && (ifs_value && *ifs_value == 0)))
	istring[istring_index++] = CTLESC;

#if defined (HANDLE_MULTIBYTE)
      if ((locale_utf8locale && (c & 0x80)) ||
	  (locale_utf8locale == 0 && mb_cur_max > 1 && (unsigned char)c > 127))
	{
	  /* read a multibyte character from buf */
	  /* punt on the hard case for now */
	  memset (&ps, '\0', sizeof (mbstate_t));
	  mblen = mbrtowc (&wc, bufp-1, bufn, &ps);
	  if (MB_INVALIDCH (mblen) || mblen == 0 || mblen == 1)
	    istring[istring_index++] = c;
	  else
	    {
	      istring[istring_index++] = c;
	      for (i = 0; i < mblen-1; i++)
		istring[istring_index++] = *bufp++;
	      bufn -= mblen - 1;
	    }
	  continue;
	}
#endif

      istring[istring_index++] = c;
    }

  if (istring)
    istring[istring_index] = '\0';

  /* If we read no output, just return now and save ourselves some
     trouble. */
  if (istring_index == 0)
    {
      FREE (istring);
      if (rflag)
	*rflag = tflag;
      return (char *)NULL;
    }

  /* Strip trailing newlines from the output of the command. */
  if (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
    {
      while (istring_index > 0)
	{
	  if (istring[istring_index - 1] == '\n')
	    {
	      --istring_index;

	      /* If the newline was quoted, remove the quoting char. */
	      if (istring[istring_index - 1] == CTLESC)
		--istring_index;
	    }
	  else
	    break;
	}
      istring[istring_index] = '\0';
    }
  else
    strip_trailing (istring, istring_index - 1, 1);

  if (rflag)
    *rflag = tflag;
  return istring;
}

/* Perform command substitution on STRING.  This returns a WORD_DESC * with the
   contained string possibly quoted. */
WORD_DESC *
command_substitute (char *string, int quoted, int flags)
{
  pid_t pid, old_pid, old_pipeline_pgrp, old_async_pid;
  char *istring, *s;
  int result, fildes[2], function_value, pflags, rc, tflag, fork_flags;
  WORD_DESC *ret;
  sigset_t set, oset;

  istring = (char *)NULL;

  /* Don't fork () if there is no need to.  In the case of no command to
     run, just return NULL. */
  for (s = string; s && *s && (shellblank (*s) || *s == '\n'); s++)
    ;
  if (s == 0 || *s == 0)
    return ((WORD_DESC *)NULL);

  if (*s == '<' && (s[1] != '<' && s[1] != '>' && s[1] != '&'))
    {
      COMMAND *cmd;

      cmd = parse_string_to_command (string, 0);	/* XXX - flags */
      if (cmd && can_optimize_cat_file (cmd))
	{
	  tflag = 0;
	  istring = optimize_cat_file (cmd->value.Simple->redirects, quoted, flags, &tflag);
	  if (istring == &expand_param_error)
	    {
	      last_command_exit_value = EXECUTION_FAILURE;
	      istring = 0;
	    }
	  else
	    last_command_exit_value = EXECUTION_SUCCESS;	/* compat */
	  last_command_subst_pid = dollar_dollar_pid;

	  dispose_command (cmd);	  
	  ret = alloc_word_desc ();
	  ret->word = istring;
	  ret->flags = tflag;

	  return ret;
	}
      dispose_command (cmd);
    }

  if (wordexp_only && read_but_dont_execute)
    {
      last_command_exit_value = EX_WEXPCOMSUB;
      jump_to_top_level (EXITPROG);
    }

  /* We're making the assumption here that the command substitution will
     eventually run a command from the file system.  Since we'll run
     maybe_make_export_env in this subshell before executing that command,
     the parent shell and any other shells it starts will have to remake
     the environment.  If we make it before we fork, other shells won't
     have to.  Don't bother if we have any temporary variable assignments,
     though, because the export environment will be remade after this
     command completes anyway, but do it if all the words to be expanded
     are variable assignments. */
  if (subst_assign_varlist == 0 || garglist == 0)
    maybe_make_export_env ();	/* XXX */

  /* Flags to pass to parse_and_execute() */
  pflags = (interactive && sourcelevel == 0) ? SEVAL_RESETLINE : 0;

  old_pid = last_made_pid;

  /* Pipe the output of executing STRING into the current shell. */
  if (pipe (fildes) < 0)
    {
      sys_error ("%s", _("cannot make pipe for command substitution"));
      goto error_exit;
    }

#if defined (JOB_CONTROL)
  old_pipeline_pgrp = pipeline_pgrp;
  /* Don't reset the pipeline pgrp if we're already a subshell in a pipeline or
     we've already forked to run a disk command (and are expanding redirections,
     for example). */
  if ((subshell_environment & (SUBSHELL_FORK|SUBSHELL_PIPE)) == 0)
    pipeline_pgrp = shell_pgrp;
  cleanup_the_pipeline ();
#endif /* JOB_CONTROL */

  old_async_pid = last_asynchronous_pid;
  fork_flags = (subshell_environment&SUBSHELL_ASYNC) ? FORK_ASYNC : 0;
  pid = make_child ((char *)NULL, fork_flags|FORK_NOTERM);
  last_asynchronous_pid = old_async_pid;

  if (pid == 0)
    {
      /* Reset the signal handlers in the child, but don't free the
	 trap strings.  Set a flag noting that we have to free the
	 trap strings if we run trap to change a signal disposition. */
      reset_signal_handlers ();
      if (ISINTERRUPT)
	{
	  kill (getpid (), SIGINT);
	  CLRINTERRUPT;		/* if we're ignoring SIGINT somehow */
	}	
      QUIT;	/* catch any interrupts we got post-fork */
      subshell_environment |= SUBSHELL_RESETTRAP;
      subshell_environment &= ~SUBSHELL_IGNTRAP;
    }

#if defined (JOB_CONTROL)
  /* XXX DO THIS ONLY IN PARENT ? XXX */
  set_sigchld_handler ();
  stop_making_children ();
  if (pid != 0)
    pipeline_pgrp = old_pipeline_pgrp;
#else
  stop_making_children ();
#endif /* JOB_CONTROL */

  if (pid < 0)
    {
      sys_error (_("cannot make child for command substitution"));
    error_exit:

      last_made_pid = old_pid;

      FREE (istring);
      close (fildes[0]);
      close (fildes[1]);
      return ((WORD_DESC *)NULL);
    }

  if (pid == 0)
    {
      /* The currently executing shell is not interactive. */
      interactive = 0;

#if defined (JOB_CONTROL)
      /* Invariant: in child processes started to run command substitutions,
	 pipeline_pgrp == shell_pgrp. Other parts of the shell assume this. */
      if (pipeline_pgrp > 0 && pipeline_pgrp != shell_pgrp)
	shell_pgrp = pipeline_pgrp;
#endif

      set_sigint_handler ();	/* XXX */

      free_pushed_string_input ();

      /* Discard  buffered stdio output before replacing the underlying file
	 descriptor. */
      fpurge (stdout);

      if (dup2 (fildes[1], 1) < 0)
	{
	  sys_error ("%s", _("command_substitute: cannot duplicate pipe as fd 1"));
	  exit (EXECUTION_FAILURE);
	}

      /* If standard output is closed in the parent shell
	 (such as after `exec >&-'), file descriptor 1 will be
	 the lowest available file descriptor, and end up in
	 fildes[0].  This can happen for stdin and stderr as well,
	 but stdout is more important -- it will cause no output
	 to be generated from this command. */
      if ((fildes[1] != fileno (stdin)) &&
	  (fildes[1] != fileno (stdout)) &&
	  (fildes[1] != fileno (stderr)))
	close (fildes[1]);

      if ((fildes[0] != fileno (stdin)) &&
	  (fildes[0] != fileno (stdout)) &&
	  (fildes[0] != fileno (stderr)))
	close (fildes[0]);

#ifdef __CYGWIN__
      /* Let stdio know the fd may have changed from text to binary mode, and
	 make sure to preserve stdout line buffering. */
      freopen (NULL, "w", stdout);
      sh_setlinebuf (stdout);
#endif /* __CYGWIN__ */

      /* This is a subshell environment. */
      subshell_environment |= SUBSHELL_COMSUB;

      /* Many shells do not appear to inherit the -v option for command
	 substitutions. */
      change_flag ('v', FLAG_OFF);

      /* When inherit_errexit option is not enabled, command substitution does
	 not inherit the -e flag.  It is enabled when Posix mode is enabled */
      if (inherit_errexit == 0)
        {
          builtin_ignoring_errexit = 0;
	  change_flag ('e', FLAG_OFF);
        }
      set_shellopts ();

      /* If we are expanding a redirection, we can dispose of any temporary
	 environment we received, since redirections are not supposed to have
	 access to the temporary environment.  We will have to see whether this
	 affects temporary environments supplied to `eval', but the temporary
	 environment gets copied to builtin_env at some point. */
      if (expanding_redir)
	{
	  flush_temporary_env ();
	  expanding_redir = 0;
	}

      remove_quoted_escapes (string);

      /* We want to expand aliases on this pass if we are not in posix mode
	 for backwards compatibility. parse_and_execute() takes care of
	 setting expand_aliases back to the global value when executing the
	 parsed string. We only do this for $(...) command substitution,
	 since that is what parse_comsub handles; `` comsubs are processed
	 using parse.y:parse_matched_pair(). */
      if (expand_aliases && (flags & PF_BACKQUOTE) == 0)
        expand_aliases = posixly_correct == 0;

      startup_state = 2;	/* see if we can avoid a fork */
      parse_and_execute_level = 0;

      /* Give command substitution a place to jump back to on failure,
	 so we don't go back up to main (). */
      result = setjmp_nosigs (top_level);

      /* If we're running a command substitution inside a shell function,
	 trap `return' so we don't return from the function in the subshell
	 and go off to never-never land. */
      if (result == 0 && return_catch_flag)
	function_value = setjmp_nosigs (return_catch);
      else
	function_value = 0;

      if (result == ERREXIT)
	rc = last_command_exit_value;
      else if (result == EXITPROG || result == EXITBLTIN)
	rc = last_command_exit_value;
      else if (result)
	rc = EXECUTION_FAILURE;
      else if (function_value)
	rc = return_catch_value;
      else
	{
	  subshell_level++;
	  rc = parse_and_execute (string, "command substitution", pflags|SEVAL_NOHIST);
	  /* leave subshell level intact for any exit trap */
	}

      last_command_exit_value = rc;
      rc = run_exit_trap ();
#if defined (PROCESS_SUBSTITUTION)
      unlink_fifo_list ();
#endif
      exit (rc);
    }
  else
    {
      int dummyfd;

#if defined (JOB_CONTROL) && defined (PGRP_PIPE)
      close_pgrp_pipe ();
#endif /* JOB_CONTROL && PGRP_PIPE */

      close (fildes[1]);

      begin_unwind_frame ("read-comsub");
      dummyfd = fildes[0];
      add_unwind_protect (close, dummyfd);

      /* Block SIGINT while we're reading from the pipe. If the child
	 process gets a SIGINT, it will either handle it or die, and the
	 read will return. */
      BLOCK_SIGNAL (SIGINT, set, oset);
      tflag = 0;
      istring = read_comsub (fildes[0], quoted, flags, &tflag);

      close (fildes[0]);
      discard_unwind_frame ("read-comsub");
      UNBLOCK_SIGNAL (oset);

      current_command_subst_pid = pid;
      last_command_exit_value = wait_for (pid, JWAIT_NOTERM);
      last_command_subst_pid = pid;
      last_made_pid = old_pid;

#if defined (JOB_CONTROL)
      /* If last_command_exit_value > 128, then the substituted command
	 was terminated by a signal.  If that signal was SIGINT, then send
	 SIGINT to ourselves.  This will break out of loops, for instance. */
      if (last_command_exit_value == (128 + SIGINT) && last_command_exit_signal == SIGINT)
	kill (getpid (), SIGINT);
#endif /* JOB_CONTROL */

      ret = alloc_word_desc ();
      ret->word = istring;
      ret->flags = tflag;

      return ret;
    }
}

