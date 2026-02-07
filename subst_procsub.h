/* subst_procsub.h -- declarations for process substitution support extracted
   from subst.c */

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

#ifndef _SUBST_PROCSUB_H_
#define _SUBST_PROCSUB_H_

#if defined (PROCESS_SUBSTITUTION)

/* Return a filename that will open a connection to the process defined by
   executing STRING.  OPEN_FOR_READ_IN_CHILD, if 1, means open the named
   pipe for reading or use the read end of the pipe and dup that file
   descriptor to fd 0 in the child.  If OPEN_FOR_READ_IN_CHILD is 0, we
   open the named pipe for writing or use the write end of the pipe in the
   child, and dup that file descriptor to fd 1 in the child. */
extern char *process_substitute PARAMS((char *, int));

#endif /* PROCESS_SUBSTITUTION */

#endif /* _SUBST_PROCSUB_H_ */
