/* _variables_scope.h -- declarations for variable scope management extracted from variables.c */
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

#ifndef _VARIABLES_SCOPE_H_
#define _VARIABLES_SCOPE_H_

#include "stdc.h"

/* Variable context management */
extern VAR_CONTEXT *new_var_context PARAMS((char *, int));
extern void dispose_var_context PARAMS((VAR_CONTEXT *));
extern VAR_CONTEXT *push_var_context PARAMS((char *, int, HASH_TABLE *));
extern void pop_var_context PARAMS((void));
extern void delete_all_contexts PARAMS((VAR_CONTEXT *));
extern void reset_local_contexts PARAMS((void));

/* Temporary variable scopes */
extern VAR_CONTEXT *push_scope PARAMS((int, HASH_TABLE *));
extern void pop_scope PARAMS((int));

/* Function contexts */
extern void clear_dollar_vars PARAMS((void));
extern void push_context PARAMS((char *, int, HASH_TABLE *));
extern void pop_context PARAMS((void));
extern void push_dollar_vars PARAMS((void));
extern void pop_dollar_vars PARAMS((void));
extern void dispose_saved_dollar_vars PARAMS((void));

/* BASH_ARGV management */
extern void init_bash_argv PARAMS((void));
extern void save_bash_argv PARAMS((void));
extern void push_args PARAMS((WORD_LIST *));
extern void pop_args PARAMS((void));

#endif /* _VARIABLES_SCOPE_H_ */
