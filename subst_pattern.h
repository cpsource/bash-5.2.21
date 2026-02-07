/* subst_pattern.h -- declarations for pattern matching/substitution
   functions extracted from subst.c */

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

#ifndef _SUBST_PATTERN_H_
#define _SUBST_PATTERN_H_

#include "stdc.h"
#include "command.h"

/* Functions called from subst.c (were static, now cross-file) */
extern char *parameter_brace_remove_pattern PARAMS((char *, char *, array_eltstate_t *, char *, int, int, int));
extern char *parameter_brace_patsub PARAMS((char *, char *, array_eltstate_t *, char *, int, int, int));
extern char *getpattern PARAMS((char *, int, int));

#endif /* _SUBST_PATTERN_H_ */
