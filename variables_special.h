/* variables_special.h -- declarations for special variable handlers extracted from variables.c */

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

#ifndef _VARIABLES_SPECIAL_H_
#define _VARIABLES_SPECIAL_H_

#include "stdc.h"

/* Functions to manage special variables */
extern void stupidly_hack_special_variables PARAMS((char *));
extern void reinit_special_variables PARAMS((void));

extern int find_special_var PARAMS((const char *));

/* Pipestatus functions */
#if defined (ARRAY_VARS)
extern void set_pipestatus_array PARAMS((int *, int));
extern ARRAY *save_pipestatus_array PARAMS((void));
extern void restore_pipestatus_array PARAMS((ARRAY *));
#endif

extern void set_pipestatus_from_exit PARAMS((int));

/* sv_* handler functions -- also declared in variables.h */
extern void sv_ifs PARAMS((char *));
extern void sv_path PARAMS((char *));
extern void sv_mail PARAMS((char *));
extern void sv_funcnest PARAMS((char *));
extern void sv_execignore PARAMS((char *));
extern void sv_globignore PARAMS((char *));
extern void sv_ignoreeof PARAMS((char *));
extern void sv_strict_posix PARAMS((char *));
extern void sv_optind PARAMS((char *));
extern void sv_opterr PARAMS((char *));
extern void sv_locale PARAMS((char *));
extern void sv_xtracefd PARAMS((char *));
extern void sv_shcompat PARAMS((char *));

#if defined (READLINE)
extern void sv_comp_wordbreaks PARAMS((char *));
extern void sv_terminal PARAMS((char *));
extern void sv_hostfile PARAMS((char *));
extern void sv_winsize PARAMS((char *));
#endif

#if defined (__CYGWIN__)
extern void sv_home PARAMS((char *));
#endif

#if defined (HISTORY)
extern void sv_histsize PARAMS((char *));
extern void sv_histignore PARAMS((char *));
extern void sv_history_control PARAMS((char *));
#  if defined (BANG_HISTORY)
extern void sv_histchars PARAMS((char *));
#  endif
extern void sv_histtimefmt PARAMS((char *));
#endif /* HISTORY */

#if defined (HAVE_TZSET)
extern void sv_tz PARAMS((char *));
#endif

#if defined (JOB_CONTROL)
extern void sv_childmax PARAMS((char *));
#endif

#endif /* _VARIABLES_SPECIAL_H_ */
