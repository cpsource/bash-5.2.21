/* _variables_dynamic.h -- declarations for dynamic variable functions extracted from variables.c */
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

#ifndef _VARIABLES_DYNAMIC_H_
#define _VARIABLES_DYNAMIC_H_

#include "stdc.h"

/* Dynamic variable initialization */
extern void initialize_dynamic_variables PARAMS((void));

/* FUNCNAME visibility */
extern void make_funcname_visible PARAMS((int));

/* BASH_ARGV0 initialization */
extern void set_argv0 PARAMS((void));

/* Random number support */
extern int get_random_number PARAMS((void));
extern int last_random_value;

#endif /* _VARIABLES_DYNAMIC_H_ */
