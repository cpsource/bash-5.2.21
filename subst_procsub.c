/* subst_procsub.c -- Process substitution support, extracted from subst.c */

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

#define NEED_FPURGE_DECL

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
#  include <mbstr.h>		/* mbschr */
#endif
#include "typemax.h"

#include "builtins/getopt.h"
#include "builtins/common.h"

#include "builtins/builtext.h"

#include <tilde/tilde.h>
#include <glob/strmatch.h>

#include "subst.h"
#include "subst_procsub.h"

/* Externs from other translation units, not declared in any header */
extern struct fd_bitmap *current_fds_to_close;
extern int wordexp_only;

#if defined (PROCESS_SUBSTITUTION)

static void reap_some_procsubs PARAMS((int));

/*****************************************************************/
/*								 */
/*		    Hacking Process Substitution		 */
/*								 */
/*****************************************************************/

#if !defined (HAVE_DEV_FD)
/* Named pipes must be removed explicitly with `unlink'.  This keeps a list
   of FIFOs the shell has open.  unlink_fifo_list will walk the list and
   unlink the ones that don't have a living process on the other end.
   unlink_all_fifos will walk the list and unconditionally unlink them, trying
   to open and close the FIFO first to release any child processes sleeping on
   the FIFO. add_fifo_list adds the name of an open FIFO to the list.
   NFIFO is a count of the number of FIFOs in the list. */
#define FIFO_INCR 20

/* PROC value of -1 means the process has been reaped and the FIFO needs to
   be removed. PROC value of 0 means the slot is unused. */
struct temp_fifo {
  char *file;
  pid_t proc;
};

static struct temp_fifo *fifo_list = (struct temp_fifo *)NULL;
static int nfifo;
static int fifo_list_size;

void
clear_fifo_list ()
{
  int i;

  for (i = 0; i < fifo_list_size; i++)
    {
      if (fifo_list[i].file)
	free (fifo_list[i].file);
      fifo_list[i].file = NULL;
      fifo_list[i].proc = 0;
    }
  nfifo = 0;
}

void *
copy_fifo_list (int *sizep)
{
  if (sizep)
    *sizep = 0;
  return (void *)NULL;
}

static void
add_fifo_list (char *pathname)
{
  int osize, i;

  if (nfifo >= fifo_list_size - 1)
    {
      osize = fifo_list_size;
      fifo_list_size += FIFO_INCR;
      fifo_list = (struct temp_fifo *)xrealloc (fifo_list,
				fifo_list_size * sizeof (struct temp_fifo));
      for (i = osize; i < fifo_list_size; i++)
	{
	  fifo_list[i].file = (char *)NULL;
	  fifo_list[i].proc = 0;	/* unused */
	}
    }

  fifo_list[nfifo].file = savestring (pathname);
  nfifo++;
}

void
unlink_fifo (int i)
{
  if ((fifo_list[i].proc == (pid_t)-1) || (fifo_list[i].proc > 0 && (kill(fifo_list[i].proc, 0) == -1)))
    {
      unlink (fifo_list[i].file);
      free (fifo_list[i].file);
      fifo_list[i].file = (char *)NULL;
      fifo_list[i].proc = 0;
    }
}

void
unlink_fifo_list ()
{
  int saved, i, j;

  if (nfifo == 0)
    return;

  for (i = saved = 0; i < nfifo; i++)
    {
      if ((fifo_list[i].proc == (pid_t)-1) || (fifo_list[i].proc > 0 && (kill(fifo_list[i].proc, 0) == -1)))
	{
	  unlink (fifo_list[i].file);
	  free (fifo_list[i].file);
	  fifo_list[i].file = (char *)NULL;
	  fifo_list[i].proc = 0;
	}
      else
	saved++;
    }

  /* If we didn't remove some of the FIFOs, compact the list. */
  if (saved)
    {
      for (i = j = 0; i < nfifo; i++)
	if (fifo_list[i].file)
	  {
	    if (i != j)
	      {
		fifo_list[j].file = fifo_list[i].file;
		fifo_list[j].proc = fifo_list[i].proc;
		fifo_list[i].file = (char *)NULL;
		fifo_list[i].proc = 0;
	      }
	    j++;
	  }
      nfifo = j;
    }
  else
    nfifo = 0;
}

void
unlink_all_fifos ()
{
  int i, fd;

  if (nfifo == 0)
    return;

  for (i = 0; i < nfifo; i++)
    {
      fifo_list[i].proc = (pid_t)-1;
#if defined (O_NONBLOCK)
      fd = open (fifo_list[i].file, O_RDWR|O_NONBLOCK);
#else
      fd = -1;
#endif
      unlink_fifo (i);
      if (fd >= 0)
	close (fd);
    }

  nfifo = 0;
}

/* Take LIST, which is a bitmap denoting active FIFOs in fifo_list
   from some point in the past, and close all open FIFOs in fifo_list
   that are not marked as active in LIST.  If LIST is NULL, close
   everything in fifo_list. LSIZE is the number of elements in LIST, in
   case it's larger than fifo_list_size (size of fifo_list). */
void
close_new_fifos (void *list, int lsize)
{
  int i;
  char *plist;

  if (list == 0)
    {
      unlink_fifo_list ();
      return;
    }

  for (plist = (char *)list, i = 0; i < lsize; i++)
    if (plist[i] == 0 && i < fifo_list_size && fifo_list[i].proc != -1)
      unlink_fifo (i);

  for (i = lsize; i < fifo_list_size; i++)
    unlink_fifo (i);
}

int
find_procsub_child (pid_t pid)
{
  int i;

  for (i = 0; i < nfifo; i++)
    if (fifo_list[i].proc == pid)
      return i;
  return -1;
}

void
set_procsub_status (int ind, pid_t pid, int status)
{
  if (ind >= 0 && ind < nfifo)
    fifo_list[ind].proc = (pid_t)-1;		/* sentinel */
}

/* If we've marked the process for this procsub as dead, close the
   associated file descriptor and delete the FIFO. */
static void
reap_some_procsubs (int max)
{
  int i;

  for (i = 0; i < max; i++)
    if (fifo_list[i].proc == (pid_t)-1)	/* reaped */
      unlink_fifo (i);
}

void
reap_procsubs ()
{
  reap_some_procsubs (nfifo);
}

#if 0
/* UNUSED */
void
wait_procsubs ()
{
  int i, r;

  for (i = 0; i < nfifo; i++)
    {
      if (fifo_list[i].proc != (pid_t)-1 && fifo_list[i].proc > 0)
	{
	  r = wait_for (fifo_list[i].proc, 0);
	  save_proc_status (fifo_list[i].proc, r);
	  fifo_list[i].proc = (pid_t)-1;
	}
    }
}
#endif

int
fifos_pending ()
{
  return nfifo;
}

int
num_fifos ()
{
  return nfifo;
}

static char *
make_named_pipe ()
{
  char *tname;

  tname = sh_mktmpname ("sh-np", MT_USERANDOM|MT_USETMPDIR);
  if (mkfifo (tname, 0600) < 0)
    {
      free (tname);
      return ((char *)NULL);
    }

  add_fifo_list (tname);
  return (tname);
}

#else /* HAVE_DEV_FD */

/* DEV_FD_LIST is a bitmap of file descriptors attached to pipes the shell
   has open to children.  NFDS is a count of the number of bits currently
   set in DEV_FD_LIST.  TOTFDS is a count of the highest possible number
   of open files. */
/* dev_fd_list[I] value of -1 means the process has been reaped and file
   descriptor I needs to be closed. Value of 0 means the slot is unused. */

static pid_t *dev_fd_list = (pid_t *)NULL;
static int nfds;
static int totfds;	/* The highest possible number of open files. */

void
clear_fifo (int i)
{
  if (dev_fd_list[i])
    {
      dev_fd_list[i] = 0;
      nfds--;
    }
}

void
clear_fifo_list ()
{
  register int i;

  if (nfds == 0)
    return;

  for (i = 0; nfds && i < totfds; i++)
    clear_fifo (i);

  nfds = 0;
}

void *
copy_fifo_list (int *sizep)
{
  void *ret;

  if (nfds == 0 || totfds == 0)
    {
      if (sizep)
	*sizep = 0;
      return (void *)NULL;
    }

  if (sizep)
    *sizep = totfds;
  ret = xmalloc (totfds * sizeof (pid_t));
  return (memcpy (ret, dev_fd_list, totfds * sizeof (pid_t)));
}

static void
add_fifo_list (int fd)
{
  if (dev_fd_list == 0 || fd >= totfds)
    {
      int ofds;

      ofds = totfds;
      totfds = getdtablesize ();
      if (totfds < 0 || totfds > 256)
	totfds = 256;
      if (fd >= totfds)
	totfds = fd + 2;

      dev_fd_list = (pid_t *)xrealloc (dev_fd_list, totfds * sizeof (dev_fd_list[0]));
      /* XXX - might need a loop for this */
      memset (dev_fd_list + ofds, '\0', (totfds - ofds) * sizeof (pid_t));
    }

  dev_fd_list[fd] = 1;		/* marker; updated later */
  nfds++;
}

int
fifos_pending ()
{
  return 0;	/* used for cleanup; not needed with /dev/fd */
}

int
num_fifos ()
{
  return nfds;
}

void
unlink_fifo (int fd)
{
  if (dev_fd_list[fd])
    {
      close (fd);
      dev_fd_list[fd] = 0;
      nfds--;
    }
}

void
unlink_fifo_list ()
{
  register int i;

  if (nfds == 0)
    return;

  for (i = totfds-1; nfds && i >= 0; i--)
    unlink_fifo (i);

  nfds = 0;
}

void
unlink_all_fifos ()
{
  unlink_fifo_list ();
}

/* Take LIST, which is a snapshot copy of dev_fd_list from some point in
   the past, and close all open fds in dev_fd_list that are not marked
   as open in LIST.  If LIST is NULL, close everything in dev_fd_list.
   LSIZE is the number of elements in LIST, in case it's larger than
   totfds (size of dev_fd_list). */
void
close_new_fifos (void *list, int lsize)
{
  int i;
  pid_t *plist;

  if (list == 0)
    {
      unlink_fifo_list ();
      return;
    }

  for (plist = (pid_t *)list, i = 0; i < lsize; i++)
    if (plist[i] == 0 && i < totfds && dev_fd_list[i])
      unlink_fifo (i);

  for (i = lsize; i < totfds; i++)
    unlink_fifo (i);
}

int
find_procsub_child (pid_t pid)
{
  int i;

  if (nfds == 0)
    return -1;

  for (i = 0; i < totfds; i++)
    if (dev_fd_list[i] == pid)
      return i;

  return -1;
}

void
set_procsub_status (int ind, pid_t pid, int status)
{
  if (ind >= 0 && ind < totfds)
    dev_fd_list[ind] = (pid_t)-1;		/* sentinel */
}

/* If we've marked the process for this procsub as dead, close the
   associated file descriptor. */
static void
reap_some_procsubs (int max)
{
  int i;

  for (i = 0; nfds > 0 && i < max; i++)
    if (dev_fd_list[i] == (pid_t)-1)
      unlink_fifo (i);
}

void
reap_procsubs ()
{
  reap_some_procsubs (totfds);
}

#if 0
/* UNUSED */
void
wait_procsubs ()
{
  int i, r;

  for (i = 0; nfds > 0 && i < totfds; i++)
    {
      if (dev_fd_list[i] != (pid_t)-1 && dev_fd_list[i] > 0)
	{
	  r = wait_for (dev_fd_list[i], 0);
	  save_proc_status (dev_fd_list[i], r);
	  dev_fd_list[i] = (pid_t)-1;
	}
    }
}
#endif

#if defined (NOTDEF)
print_dev_fd_list ()
{
  register int i;

  fprintf (stderr, "pid %ld: dev_fd_list:", (long)getpid ());
  fflush (stderr);

  for (i = 0; i < totfds; i++)
    {
      if (dev_fd_list[i])
	fprintf (stderr, " %d", i);
    }
  fprintf (stderr, "\n");
}
#endif /* NOTDEF */

static char *
make_dev_fd_filename (int fd)
{
  char *ret, intbuf[INT_STRLEN_BOUND (int) + 1], *p;

  ret = (char *)xmalloc (sizeof (DEV_FD_PREFIX) + 8);

  strcpy (ret, DEV_FD_PREFIX);
  p = inttostr (fd, intbuf, sizeof (intbuf));
  strcpy (ret + sizeof (DEV_FD_PREFIX) - 1, p);

  add_fifo_list (fd);
  return (ret);
}

#endif /* HAVE_DEV_FD */

/* Return a filename that will open a connection to the process defined by
   executing STRING.  HAVE_DEV_FD, if defined, means open a pipe and return
   a filename in /dev/fd corresponding to a descriptor that is one of the
   ends of the pipe.  If not defined, we use named pipes on systems that have
   them.  Systems without /dev/fd and named pipes are out of luck.

   OPEN_FOR_READ_IN_CHILD, if 1, means open the named pipe for reading or
   use the read end of the pipe and dup that file descriptor to fd 0 in
   the child.  If OPEN_FOR_READ_IN_CHILD is 0, we open the named pipe for
   writing or use the write end of the pipe in the child, and dup that
   file descriptor to fd 1 in the child.  The parent does the opposite. */

char *
process_substitute (char *string, int open_for_read_in_child)
{
  char *pathname;
  int fd, result, rc, function_value;
  pid_t old_pid, pid;
#if defined (HAVE_DEV_FD)
  int parent_pipe_fd, child_pipe_fd;
  int fildes[2];
#endif /* HAVE_DEV_FD */
#if defined (JOB_CONTROL)
  pid_t old_pipeline_pgrp;
#endif

  if (!string || !*string || wordexp_only)
    return ((char *)NULL);

#if !defined (HAVE_DEV_FD)
  pathname = make_named_pipe ();
#else /* HAVE_DEV_FD */
  if (pipe (fildes) < 0)
    {
      sys_error ("%s", _("cannot make pipe for process substitution"));
      return ((char *)NULL);
    }
  /* If OPEN_FOR_READ_IN_CHILD == 1, we want to use the write end of
     the pipe in the parent, otherwise the read end. */
  parent_pipe_fd = fildes[open_for_read_in_child];
  child_pipe_fd = fildes[1 - open_for_read_in_child];
  /* Move the parent end of the pipe to some high file descriptor, to
     avoid clashes with FDs used by the script. */
  parent_pipe_fd = move_to_high_fd (parent_pipe_fd, 1, 64);

  pathname = make_dev_fd_filename (parent_pipe_fd);
#endif /* HAVE_DEV_FD */

  if (pathname == 0)
    {
      sys_error ("%s", _("cannot make pipe for process substitution"));
      return ((char *)NULL);
    }

  old_pid = last_made_pid;

#if defined (JOB_CONTROL)
  old_pipeline_pgrp = pipeline_pgrp;
  if (pipeline_pgrp == 0 || (subshell_environment & (SUBSHELL_PIPE|SUBSHELL_FORK|SUBSHELL_ASYNC)) == 0)
    pipeline_pgrp = shell_pgrp;
  save_pipeline (1);
#endif /* JOB_CONTROL */

  pid = make_child ((char *)NULL, FORK_ASYNC);
  if (pid == 0)
    {
#if 0
      int old_interactive;

      old_interactive = interactive;
#endif
      /* The currently-executing shell is not interactive */
      interactive = 0;

      reset_terminating_signals ();	/* XXX */
      free_pushed_string_input ();
      /* Cancel traps, in trap.c. */
      restore_original_signals ();	/* XXX - what about special builtins? bash-4.2 */
      subshell_environment &= ~SUBSHELL_IGNTRAP;
      QUIT;	/* catch any interrupts we got post-fork */
      setup_async_signals ();
#if 0
      if (open_for_read_in_child == 0 && old_interactive && (bash_input.type == st_stdin || bash_input.type == st_stream))
	async_redirect_stdin ();
#endif

      subshell_environment |= SUBSHELL_COMSUB|SUBSHELL_PROCSUB|SUBSHELL_ASYNC;

      /* We don't inherit the verbose option for command substitutions now, so
	 let's try it for process substitutions. */
      change_flag ('v', FLAG_OFF);

      /* if we're expanding a redirection, we shouldn't have access to the
	 temporary environment, but commands in the subshell should have
	 access to their own temporary environment. */
      if (expanding_redir)
        flush_temporary_env ();
    }

#if defined (JOB_CONTROL)
  set_sigchld_handler ();
  stop_making_children ();
  /* XXX - should we only do this in the parent? (as in command subst) */
  pipeline_pgrp = old_pipeline_pgrp;
#else
  stop_making_children ();
#endif /* JOB_CONTROL */

  if (pid < 0)
    {
      sys_error ("%s", _("cannot make child for process substitution"));
      free (pathname);
#if defined (HAVE_DEV_FD)
      close (parent_pipe_fd);
      close (child_pipe_fd);
#endif /* HAVE_DEV_FD */
#if defined (JOB_CONTROL)
      restore_pipeline (1);
#endif
      return ((char *)NULL);
    }

  if (pid > 0)
    {
#if defined (JOB_CONTROL)
      last_procsub_child = restore_pipeline (0);
      /* We assume that last_procsub_child->next == last_procsub_child because
	 of how jobs.c:add_process() works. */
      last_procsub_child->next = 0;
      procsub_add (last_procsub_child);
#endif

#if defined (HAVE_DEV_FD)
      dev_fd_list[parent_pipe_fd] = pid;
#else
      fifo_list[nfifo-1].proc = pid;
#endif

      last_made_pid = old_pid;

#if defined (JOB_CONTROL) && defined (PGRP_PIPE)
      close_pgrp_pipe ();
#endif /* JOB_CONTROL && PGRP_PIPE */

#if defined (HAVE_DEV_FD)
      close (child_pipe_fd);
#endif /* HAVE_DEV_FD */

      return (pathname);
    }

  set_sigint_handler ();

#if defined (JOB_CONTROL)
  /* make sure we don't have any job control */
  set_job_control (0);

  /* Clear out any existing list of process substitutions */
  procsub_clear ();

  /* The idea is that we want all the jobs we start from an async process
     substitution to be in the same process group, but not the same pgrp
     as our parent shell, since we don't want to affect our parent shell's
     jobs if we get a SIGHUP and end up calling hangup_all_jobs, for example.
     If pipeline_pgrp != shell_pgrp, we assume that there is a job control
     shell somewhere in our parent process chain (since make_child initializes
     pipeline_pgrp to shell_pgrp if job_control == 0). What we do in this
     case is to set pipeline_pgrp to our PID, so all jobs started by this
     process have that same pgrp and we are basically the process group leader.
     This should not have negative effects on child processes surviving
     after we exit, since we wait for the children we create, but that is
     something to watch for. */

  if (pipeline_pgrp != shell_pgrp)
    pipeline_pgrp = getpid ();
#endif /* JOB_CONTROL */

#if !defined (HAVE_DEV_FD)
  /* Open the named pipe in the child. */
  fd = open (pathname, open_for_read_in_child ? O_RDONLY : O_WRONLY);
  if (fd < 0)
    {
      /* Two separate strings for ease of translation. */
      if (open_for_read_in_child)
	sys_error (_("cannot open named pipe %s for reading"), pathname);
      else
	sys_error (_("cannot open named pipe %s for writing"), pathname);

      exit (127);
    }
  if (open_for_read_in_child)
    {
      if (sh_unset_nodelay_mode (fd) < 0)
	{
	  sys_error (_("cannot reset nodelay mode for fd %d"), fd);
	  exit (127);
	}
    }
#else /* HAVE_DEV_FD */
  fd = child_pipe_fd;
#endif /* HAVE_DEV_FD */

  /* Discard  buffered stdio output before replacing the underlying file
     descriptor. */
  if (open_for_read_in_child == 0)
    fpurge (stdout);

  if (dup2 (fd, open_for_read_in_child ? 0 : 1) < 0)
    {
      sys_error (_("cannot duplicate named pipe %s as fd %d"), pathname,
	open_for_read_in_child ? 0 : 1);
      exit (127);
    }

  if (fd != (open_for_read_in_child ? 0 : 1))
    close (fd);

  /* Need to close any files that this process has open to pipes inherited
     from its parent. */
  if (current_fds_to_close)
    {
      close_fd_bitmap (current_fds_to_close);
      current_fds_to_close = (struct fd_bitmap *)NULL;
    }

#if defined (HAVE_DEV_FD)
  /* Make sure we close the parent's end of the pipe and clear the slot
     in the fd list so it is not closed later, if reallocated by, for
     instance, pipe(2). */
  close (parent_pipe_fd);
  dev_fd_list[parent_pipe_fd] = 0;
#endif /* HAVE_DEV_FD */

  /* subshells shouldn't have this flag, which controls using the temporary
     environment for variable lookups.  We have already flushed the temporary
     environment above in the case we're expanding a redirection, so processes
     executed by this command need to be able to set it independently of their
     parent. */
  expanding_redir = 0;

  remove_quoted_escapes (string);

  startup_state = 2;	/* see if we can avoid a fork */
  parse_and_execute_level = 0;

  /* Give process substitution a place to jump back to on failure,
     so we don't go back up to main (). */
  result = setjmp_nosigs (top_level);

  /* If we're running a process substitution inside a shell function,
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
      rc = parse_and_execute (string, "process substitution", (SEVAL_NONINT|SEVAL_NOHIST));
      /* leave subshell level intact for any exit trap */
    }

#if !defined (HAVE_DEV_FD)
  /* Make sure we close the named pipe in the child before we exit. */
  close (open_for_read_in_child ? 0 : 1);
#endif /* !HAVE_DEV_FD */

  last_command_exit_value = rc;
  rc = run_exit_trap ();
  exit (rc);
  /*NOTREACHED*/
}
#endif /* PROCESS_SUBSTITUTION */
