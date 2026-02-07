/* _variables_init.h -- declarations for initialization functions extracted from variables.c */
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

#ifndef _VARIABLES_INIT_H_
#define _VARIABLES_INIT_H_

#include "stdc.h"

/* Initialization functions */
extern void create_variable_tables PARAMS((void));
extern void initialize_shell_variables PARAMS((char **, int));

/* Setting values for special shell variables */
extern void adjust_shell_level PARAMS((int));
extern void set_pwd PARAMS((void));
extern void set_ppid PARAMS((void));

extern void sh_set_lines_and_columns PARAMS((int, int));

/* Printing variables and values */
extern void print_var_list PARAMS((SHELL_VAR **));
extern void print_func_list PARAMS((SHELL_VAR **));
extern void print_assignment PARAMS((SHELL_VAR *));
extern void print_var_value PARAMS((SHELL_VAR *, int));
extern void print_var_function PARAMS((SHELL_VAR *));

#if defined (READLINE)
extern int winsize_assignment;
#endif

#endif /* _VARIABLES_INIT_H_ */
