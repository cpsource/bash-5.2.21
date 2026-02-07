/* subst_extract.h -- declarations for string extraction functions
   extracted from subst.c */

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

#ifndef _SUBST_EXTRACT_H_
#define _SUBST_EXTRACT_H_

/* Functions that were static in subst.c but are now needed cross-file. */
extern char *string_extract PARAMS((char *, int *, char *, int));
extern char *string_extract_double_quoted PARAMS((char *, int *, int));
extern char *string_extract_single_quoted PARAMS((char *, int *, int));
extern int skip_single_quoted PARAMS((const char *, size_t, int, int));
extern int skip_double_quoted PARAMS((char *, size_t, int, int));
extern char *string_extract_verbatim PARAMS((char *, size_t, int *, char *, int));
extern char *extract_dollar_brace_string PARAMS((char *, int *, int, int));

#endif /* _SUBST_EXTRACT_H_ */
