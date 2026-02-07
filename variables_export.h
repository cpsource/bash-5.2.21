/* _variables_export.h -- declarations for export and environment functions extracted from variables.c */
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

#ifndef _VARIABLES_EXPORT_H_
#define _VARIABLES_EXPORT_H_

#include "stdc.h"

/* Temporary environment management */
extern SHELL_VAR *bind_tempenv_variable PARAMS((const char *, char *));
extern SHELL_VAR *find_tempenv_variable PARAMS((const char *));
extern void dispose_used_env_vars PARAMS((void));
extern void merge_temporary_env PARAMS((void));
extern void merge_function_temporary_env PARAMS((void));
extern void flush_temporary_env PARAMS((void));

/* Environment string and array management */
extern char *mk_env_string PARAMS((const char *, const char *, int));
extern char **add_or_supercede_exported_var PARAMS((char *, int));
extern int chkexport PARAMS((char *));
extern void maybe_make_export_env PARAMS((void));
extern void update_export_env_inplace PARAMS((char *, int, char *));
extern void put_command_name_into_env PARAMS((char *));

/* Temporary variable list (used by scope management) */
extern char **tempvar_list;
extern int tvlist_ind;

#endif /* _VARIABLES_EXPORT_H_ */
