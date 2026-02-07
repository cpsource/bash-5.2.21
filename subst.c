/* subst.c -- The part of the shell that does parameter, command, arithmetic,
   and globbing substitutions. */

/* ``Have a little faith, there's magic in the night.  You ain't a
     beauty, but, hey, you're alright.'' */

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

#if defined (PROCESS_SUBSTITUTION)
#include "subst_procsub.h"
#endif

#include "subst_quote.h"
#include "subst_pattern.h"
#include "subst_comsub.h"
#include "subst_extract.h"

#if !defined (errno)
extern int errno;
#endif /* !errno */

/* The size that strings change by. */
#define DEFAULT_INITIAL_ARRAY_SIZE 112
#define DEFAULT_ARRAY_SIZE 128

/* Variable types. */
#define VT_VARIABLE	0
#define VT_POSPARMS	1
#define VT_ARRAYVAR	2
#define VT_ARRAYMEMBER	3
#define VT_ASSOCVAR	4

#define VT_STARSUB	128	/* $* or ${array[*]} -- used to split */

/* Flags for quoted_strchr */
#define ST_BACKSL	0x01
#define ST_CTLESC	0x02
#define ST_SQUOTE	0x04	/* unused yet */
#define ST_DQUOTE	0x08	/* unused yet */

/* Values for the quoted_state variable in expand_word_internal. */
#define UNQUOTED	 0
#define PARTIALLY_QUOTED 1
#define WHOLLY_QUOTED    2

/* These defs make it easier to use the editor. */
#define LBRACE		'{'
#define RBRACE		'}'
#define LPAREN		'('
#define RPAREN		')'
#define LBRACK		'['
#define RBRACK		']'

#if defined (HANDLE_MULTIBYTE)
#define WLPAREN		L'('
#define WRPAREN		L')'
#endif

#define DOLLAR_AT_STAR(c)	((c) == '@' || (c) == '*')
#define STR_DOLLAR_AT_STAR(s)	(DOLLAR_AT_STAR ((s)[0]) && (s)[1] == '\0')

/* Evaluates to 1 if C is one of the shell's special parameters whose length
   can be taken, but is also one of the special expansion characters. */
#define VALID_SPECIAL_LENGTH_PARAM(c) \
  ((c) == '-' || (c) == '?' || (c) == '#' || (c) == '@')

/* Evaluates to 1 if C is one of the shell's special parameters for which an
   indirect variable reference may be made. */
#define VALID_INDIR_PARAM(c) \
  ((posixly_correct == 0 && (c) == '#') || (posixly_correct == 0 && (c) == '?') || (c) == '@' || (c) == '*')

/* Evaluates to 1 if C is one of the OP characters that follows the parameter
   in ${parameter[:]OPword}. */
#define VALID_PARAM_EXPAND_CHAR(c) (sh_syntaxtab[(unsigned char)c] & CSUBSTOP)

/* Evaluates to 1 if this is one of the shell's special variables. */
#define SPECIAL_VAR(name, wi) \
 (*name && ((DIGIT (*name) && all_digits (name)) || \
      (name[1] == '\0' && (sh_syntaxtab[(unsigned char)*name] & CSPECVAR)) || \
      (wi && name[2] == '\0' && VALID_INDIR_PARAM (name[1]))))

/* This can be used by all of the *_extract_* functions that have a similar
   structure.  It can't just be wrapped in a do...while(0) loop because of
   the embedded `break'. The dangling else accommodates a trailing semicolon;
   we could also put in a do ; while (0) */

#define CHECK_STRING_OVERRUN(oind, ind, len, ch) \
  if (ind >= len) \
    { \
      oind = len; \
      ch = 0; \
      break; \
    } \
  else \

/* An expansion function that takes a string and a quoted flag and returns
   a WORD_LIST *.  Used as the type of the third argument to
   expand_string_if_necessary(). */
typedef WORD_LIST *EXPFUNC PARAMS((char *, int));

/* Process ID of the last command executed within command substitution. */
pid_t last_command_subst_pid = NO_PID;
pid_t current_command_subst_pid = NO_PID;

/* Variables used to keep track of the characters in IFS. */
IFS_STATE global_ifs;

/* If non-zero, command substitution inherits the value of errexit option */
int inherit_errexit = 0;

/* Sentinel to tell when we are performing variable assignments preceding a
   command name and putting them into the environment.  Used to make sure
   we use the temporary environment when looking up variable values. */
int assigning_in_environment;

/* Used to hold a list of variable assignments preceding a command.  Global
   so the SIGCHLD handler in jobs.c can unwind-protect it when it runs a
   SIGCHLD trap and so it can be saved and restored by the trap handlers. */
WORD_LIST *subst_assign_varlist = (WORD_LIST *)NULL;

/* Expansion control flags — single instance, macros in subst.h. */
EXPAND_FLAGS global_expand_flags = { 0, 0, 0, 1, 0 };

/* Extern functions and variables from different files. */
extern struct fd_bitmap *current_fds_to_close;
extern int wordexp_only;
extern int singlequote_translations;
extern int extended_quote;

#if defined (JOB_CONTROL) && defined (PROCESS_SUBSTITUTION)
extern PROCESS *last_procsub_child;
#endif

#if !defined (HAVE_WCSDUP) && defined (HANDLE_MULTIBYTE)
extern wchar_t *wcsdup PARAMS((const wchar_t *));
#endif

#if 0
/* Variables to keep track of which words in an expanded word list (the
   output of expand_word_list_internal) are the result of globbing
   expansions.  GLOB_ARGV_FLAGS is used by execute_cmd.c.
   (CURRENTLY UNUSED). */
char *glob_argv_flags;
static int glob_argv_flags_size;
#endif

static WORD_LIST *cached_quoted_dollar_at = 0;

/* Distinguished error values to return from expansion functions */
static WORD_LIST expand_word_error, expand_word_fatal;
static WORD_DESC expand_wdesc_error, expand_wdesc_fatal;
char expand_param_error, expand_param_fatal, expand_param_unset;
char extract_string_error, extract_string_fatal;

/* A WORD_LIST of words to be expanded by expand_word_list_internal,
   without any leading variable assignments. */
WORD_LIST *garglist = (WORD_LIST *)NULL;

static char *quoted_substring PARAMS((char *, int, int));
static int quoted_strlen PARAMS((const char *));
static char *quoted_strchr PARAMS((char *, int, int));

static WORD_LIST *call_expand_word_internal PARAMS((WORD_DESC *, int, int, int *, int *));
static WORD_LIST *expand_string_internal PARAMS((char *, int));
static WORD_LIST *expand_string_leave_quoted PARAMS((char *, int));
static WORD_LIST *expand_string_for_rhs PARAMS((char *, int, int, int, int *, int *));

/* Non-static forward declarations for functions used before their definitions */
char *expand_string_if_necessary PARAMS((char *, int, EXPFUNC *));
char *expand_string_to_string_internal PARAMS((char *, int, EXPFUNC *));
WORD_LIST *expand_string_for_pat PARAMS((char *, int, int *, int *));
int get_var_and_type PARAMS((char *, char *, array_eltstate_t *, int, int, SHELL_VAR **, char **));

static int unquoted_substring PARAMS((const char *, char *));
static int unquoted_member PARAMS((int, char *));

#if defined (ARRAY_VARS)
static SHELL_VAR *do_compound_assignment PARAMS((char *, char *, int));
#endif
static int do_assignment_internal PARAMS((const WORD_DESC *, int));


static char *pos_params PARAMS((char *, int, int, int, int));


static char *string_var_assignment PARAMS((SHELL_VAR *, char *));
#if defined (ARRAY_VARS)
static char *array_var_assignment PARAMS((SHELL_VAR *, int, int, int));
#endif
static char *pos_params_assignment PARAMS((WORD_LIST *, int, int));
static char *string_transform PARAMS((int, SHELL_VAR *, char *));
static char *list_transform PARAMS((int, SHELL_VAR *, WORD_LIST *, int, int));
static char *parameter_list_transform PARAMS((int, int, int));
#if defined ARRAY_VARS
static char *array_transform PARAMS((int, SHELL_VAR *, int, int));
#endif
static char *parameter_brace_transform PARAMS((char *, char *, array_eltstate_t *, char *, int, int, int, int));
static int valid_parameter_transform PARAMS((char *));

#ifdef ARRAY_VARS
static arrayind_t array_length_reference PARAMS((char *));
#endif

static int valid_brace_expansion_word PARAMS((const char *, int));
static int chk_atstar PARAMS((char *, int, int, int *, int *));
static int chk_arithsub PARAMS((const char *, int));

static WORD_DESC *parameter_brace_expand_word PARAMS((char *, int, int, int, array_eltstate_t *));
static char *parameter_brace_find_indir PARAMS((char *, int, int, int));
static WORD_DESC *parameter_brace_expand_indir PARAMS((char *, int, int, int, int *, int *));
static WORD_DESC *parameter_brace_expand_rhs PARAMS((char *, char *, int, int, int, int *, int *));
static void parameter_brace_expand_error PARAMS((char *, char *, int));

static int valid_length_expression PARAMS((char *));
static intmax_t parameter_brace_expand_length PARAMS((char *));

static char *skiparith PARAMS((char *, int));
static int verify_substring_values PARAMS((SHELL_VAR *, char *, char *, int, intmax_t *, intmax_t *));
static char *mb_substring PARAMS((char *, int, int));
static char *parameter_brace_substring PARAMS((char *, char *, array_eltstate_t *, char *, int, int, int));

static char *pos_params_casemod PARAMS((char *, char *, int, int));
static char *parameter_brace_casemod PARAMS((char *, char *, array_eltstate_t *, int, char *, int, int, int));

static WORD_DESC *parameter_brace_expand PARAMS((char *, int *, int, int, int *, int *));
static WORD_DESC *param_expand PARAMS((char *, int *, int, int *, int *, int *, int *, int));

static WORD_LIST *expand_word_internal PARAMS((WORD_DESC *, int, int, int *, int *));

static WORD_LIST *word_list_split PARAMS((WORD_LIST *));

void exp_jump_to_top_level PARAMS((int));

static WORD_LIST *separate_out_assignments PARAMS((WORD_LIST *));
static WORD_LIST *glob_expand_word_list PARAMS((WORD_LIST *, int));
#ifdef BRACE_EXPANSION
static WORD_LIST *brace_expand_word_list PARAMS((WORD_LIST *, int));
#endif
#if defined (ARRAY_VARS)
static int make_internal_declare PARAMS((char *, char *, char *));
static void expand_compound_assignment_word PARAMS((WORD_LIST *, int));
static WORD_LIST *expand_declaration_argument PARAMS((WORD_LIST *, WORD_LIST *));
#endif
static WORD_LIST *shell_expand_word_list PARAMS((WORD_LIST *, int));
static WORD_LIST *expand_word_list_internal PARAMS((WORD_LIST *, int));

static int do_assignment_statements PARAMS((WORD_LIST *, char *, int));

/* **************************************************************** */
/*								    */
/*			Utility Functions			    */
/*								    */
/* **************************************************************** */

#if defined (DEBUG)
void
dump_word_flags (int flags)
{
  int f;

  f = flags;
  fprintf (stderr, "%d -> ", f);
  if (f & W_ARRAYIND)
    {
      f &= ~W_ARRAYIND;
      fprintf (stderr, "W_ARRAYIND%s", f ? "|" : "");
    }
  if (f & W_ASSIGNASSOC)
    {
      f &= ~W_ASSIGNASSOC;
      fprintf (stderr, "W_ASSIGNASSOC%s", f ? "|" : "");
    }
  if (f & W_ASSIGNARRAY)
    {
      f &= ~W_ASSIGNARRAY;
      fprintf (stderr, "W_ASSIGNARRAY%s", f ? "|" : "");
    }
  if (f & W_SAWQUOTEDNULL)
    {
      f &= ~W_SAWQUOTEDNULL;
      fprintf (stderr, "W_SAWQUOTEDNULL%s", f ? "|" : "");
    }
  if (f & W_NOPROCSUB)
    {
      f &= ~W_NOPROCSUB;
      fprintf (stderr, "W_NOPROCSUB%s", f ? "|" : "");
    }
  if (f & W_DQUOTE)
    {
      f &= ~W_DQUOTE;
      fprintf (stderr, "W_DQUOTE%s", f ? "|" : "");
    }
  if (f & W_HASQUOTEDNULL)
    {
      f &= ~W_HASQUOTEDNULL;
      fprintf (stderr, "W_HASQUOTEDNULL%s", f ? "|" : "");
    }
  if (f & W_ASSIGNARG)
    {
      f &= ~W_ASSIGNARG;
      fprintf (stderr, "W_ASSIGNARG%s", f ? "|" : "");
    }
  if (f & W_ASSNBLTIN)
    {
      f &= ~W_ASSNBLTIN;
      fprintf (stderr, "W_ASSNBLTIN%s", f ? "|" : "");
    }
  if (f & W_ASSNGLOBAL)
    {
      f &= ~W_ASSNGLOBAL;
      fprintf (stderr, "W_ASSNGLOBAL%s", f ? "|" : "");
    }
  if (f & W_COMPASSIGN)
    {
      f &= ~W_COMPASSIGN;
      fprintf (stderr, "W_COMPASSIGN%s", f ? "|" : "");
    }
  if (f & W_EXPANDRHS)
    {
      f &= ~W_EXPANDRHS;
      fprintf (stderr, "W_EXPANDRHS%s", f ? "|" : "");
    }
  if (f & W_NOTILDE)
    {
      f &= ~W_NOTILDE;
      fprintf (stderr, "W_NOTILDE%s", f ? "|" : "");
    }
  if (f & W_ASSIGNRHS)
    {
      f &= ~W_ASSIGNRHS;
      fprintf (stderr, "W_ASSIGNRHS%s", f ? "|" : "");
    }
  if (f & W_NOASSNTILDE)
    {
      f &= ~W_NOASSNTILDE;
      fprintf (stderr, "W_NOASSNTILDE%s", f ? "|" : "");
    }
  if (f & W_NOCOMSUB)
    {
      f &= ~W_NOCOMSUB;
      fprintf (stderr, "W_NOCOMSUB%s", f ? "|" : "");
    }
  if (f & W_ARRAYREF)
    {
      f &= ~W_ARRAYREF;
      fprintf (stderr, "W_ARRAYREF%s", f ? "|" : "");
    }
  if (f & W_DOLLARAT)
    {
      f &= ~W_DOLLARAT;
      fprintf (stderr, "W_DOLLARAT%s", f ? "|" : "");
    }
  if (f & W_TILDEEXP)
    {
      f &= ~W_TILDEEXP;
      fprintf (stderr, "W_TILDEEXP%s", f ? "|" : "");
    }
  if (f & W_NOSPLIT2)
    {
      f &= ~W_NOSPLIT2;
      fprintf (stderr, "W_NOSPLIT2%s", f ? "|" : "");
    }
  if (f & W_NOSPLIT)
    {
      f &= ~W_NOSPLIT;
      fprintf (stderr, "W_NOSPLIT%s", f ? "|" : "");
    }
  if (f & W_NOBRACE)
    {
      f &= ~W_NOBRACE;
      fprintf (stderr, "W_NOBRACE%s", f ? "|" : "");
    }
  if (f & W_NOGLOB)
    {
      f &= ~W_NOGLOB;
      fprintf (stderr, "W_NOGLOB%s", f ? "|" : "");
    }
  if (f & W_SPLITSPACE)
    {
      f &= ~W_SPLITSPACE;
      fprintf (stderr, "W_SPLITSPACE%s", f ? "|" : "");
    }
  if (f & W_ASSIGNMENT)
    {
      f &= ~W_ASSIGNMENT;
      fprintf (stderr, "W_ASSIGNMENT%s", f ? "|" : "");
    }
  if (f & W_QUOTED)
    {
      f &= ~W_QUOTED;
      fprintf (stderr, "W_QUOTED%s", f ? "|" : "");
    }
  if (f & W_HASDOLLAR)
    {
      f &= ~W_HASDOLLAR;
      fprintf (stderr, "W_HASDOLLAR%s", f ? "|" : "");
    }
  if (f & W_COMPLETE)
    {
      f &= ~W_COMPLETE;
      fprintf (stderr, "W_COMPLETE%s", f ? "|" : "");
    }
  if (f & W_CHKLOCAL)
    {
      f &= ~W_CHKLOCAL;
      fprintf (stderr, "W_CHKLOCAL%s", f ? "|" : "");
    }
  if (f & W_FORCELOCAL)
    {
      f &= ~W_FORCELOCAL;
      fprintf (stderr, "W_FORCELOCAL%s", f ? "|" : "");
    }

  fprintf (stderr, "\n");
  fflush (stderr);
}
#endif

#ifdef INCLUDE_UNUSED
static char *
quoted_substring (char *string, int start, int end)
{
  register int len, l;
  register char *result, *s, *r;

  len = end - start;

  /* Move to string[start], skipping quoted characters. */
  for (s = string, l = 0; *s && l < start; )
    {
      if (*s == CTLESC)
	{
	  s++;
	  continue;
	}
      l++;
      if (*s == 0)
	break;
    }

  r = result = (char *)xmalloc (2*len + 1);      /* save room for quotes */

  /* Copy LEN characters, including quote characters. */
  s = string + l;
  for (l = 0; l < len; s++)
    {
      if (*s == CTLESC)
	*r++ = *s++;
      *r++ = *s;
      l++;
      if (*s == 0)
	break;
    }
  *r = '\0';
  return result;
}
#endif

#ifdef INCLUDE_UNUSED
/* Return the length of S, skipping over quoted characters */
static int
quoted_strlen (const char *s)
{
  register const char *p;
  int i;

  i = 0;
  for (p = s; *p; p++)
    {
      if (*p == CTLESC)
	{
	  p++;
	  if (*p == 0)
	    return (i + 1);
	}
      i++;
    }

  return i;
}
#endif

#ifdef INCLUDE_UNUSED
/* Find the first occurrence of character C in string S, obeying shell
   quoting rules.  If (FLAGS & ST_BACKSL) is non-zero, backslash-escaped
   characters are skipped.  If (FLAGS & ST_CTLESC) is non-zero, characters
   escaped with CTLESC are skipped. */
static char *
quoted_strchr (char *s, int c, int flags)
{
  register char *p;

  for (p = s; *p; p++)
    {
      if (((flags & ST_BACKSL) && *p == '\\')
	    || ((flags & ST_CTLESC) && *p == CTLESC))
	{
	  p++;
	  if (*p == '\0')
	    return ((char *)NULL);
	  continue;
	}
      else if (*p == c)
	return p;
    }
  return ((char *)NULL);
}

/* Return 1 if CHARACTER appears in an unquoted portion of
   STRING.  Return 0 otherwise.  CHARACTER must be a single-byte character. */
static int
unquoted_member (int character, char *string)
{
  size_t slen;
  int sindex, c;
  DECLARE_MBSTATE;

  slen = strlen (string);
  sindex = 0;
  while (c = string[sindex])
    {
      if (c == character)
	return (1);

      switch (c)
	{
	default:
	  ADVANCE_CHAR (string, slen, sindex);
	  break;

	case '\\':
	  sindex++;
	  if (string[sindex])
	    ADVANCE_CHAR (string, slen, sindex);
	  break;

	case '\'':
	  sindex = skip_single_quoted (string, slen, ++sindex, 0);
	  break;

	case '"':
	  sindex = skip_double_quoted (string, slen, ++sindex, 0);
	  break;
	}
    }
  return (0);
}

/* Return 1 if SUBSTR appears in an unquoted portion of STRING. */
static int
unquoted_substring (const char *substr, char *string)
{
  size_t slen;
  int sindex, c, sublen;
  DECLARE_MBSTATE;

  if (substr == 0 || *substr == '\0')
    return (0);

  slen = strlen (string);
  sublen = strlen (substr);
  for (sindex = 0; c = string[sindex]; )
    {
      if (STREQN (string + sindex, substr, sublen))
	return (1);

      switch (c)
	{
	case '\\':
	  sindex++;
	  if (string[sindex])
	    ADVANCE_CHAR (string, slen, sindex);
	  break;

	case '\'':
	  sindex = skip_single_quoted (string, slen, ++sindex, 0);
	  break;

	case '"':
	  sindex = skip_double_quoted (string, slen, ++sindex, 0);
	  break;

	default:
	  ADVANCE_CHAR (string, slen, sindex);
	  break;
	}
    }
  return (0);
}
#endif

/* Most of the substitutions must be done in parallel.  In order
   to avoid using tons of unclear goto's, I have some functions
   for manipulating malloc'ed strings.  They all take INDX, a
   pointer to an integer which is the offset into the string
   where manipulation is taking place.  They also take SIZE, a
   pointer to an integer which is the current length of the
   character array for this string. */

/* Append SOURCE to TARGET at INDEX.  SIZE is the current amount
   of space allocated to TARGET.  SOURCE can be NULL, in which
   case nothing happens.  Gets rid of SOURCE by freeing it.
   Returns TARGET in case the location has changed. */
INLINE char *
sub_append_string (char *source, char *target, size_t *indx, size_t *size)
{
  if (source)
    {
      size_t n, srclen;

      srclen = STRLEN (source);
      if (srclen >= (*size - *indx))
	{
	  n = srclen + *indx;
	  n = (n + DEFAULT_ARRAY_SIZE) - (n % DEFAULT_ARRAY_SIZE);
	  target = (char *)xrealloc (target, (*size = n));
	}

      FASTCOPY (source, target + *indx, srclen);
      *indx += srclen;
      target[*indx] = '\0';

      free (source);
    }
  return (target);
}

#if 0
/* UNUSED */
/* Append the textual representation of NUMBER to TARGET.
   INDX and SIZE are as in SUB_APPEND_STRING. */
char *
sub_append_number (intmax_t number, char *target, size_t *indx, size_t *size)
{
  char *temp;

  temp = itos (number);
  return (sub_append_string (temp, target, indx, size));
}
#endif


/* **************************************************************** */
/*								    */
/*     Functions to convert strings to WORD_LISTs and vice versa    */
/*								    */
/* **************************************************************** */

/* Return a single string of all the words in LIST.  SEP is the separator
   to put between individual elements of LIST in the output string. */
char *
string_list_internal (WORD_LIST *list, char *sep)
{
  register WORD_LIST *t;
  char *result, *r;
  size_t word_len, sep_len, result_size;

  if (list == 0)
    return ((char *)NULL);

  /* Short-circuit quickly if we don't need to separate anything. */
  if (list->next == 0)
    return (savestring (list->word->word));

  /* This is nearly always called with either sep[0] == 0 or sep[1] == 0. */
  sep_len = STRLEN (sep);
  result_size = 0;

  for (t = list; t; t = t->next)
    {
      if (t != list)
	result_size += sep_len;
      result_size += strlen (t->word->word);
    }

  r = result = (char *)xmalloc (result_size + 1);

  for (t = list; t; t = t->next)
    {
      if (t != list && sep_len)
	{
	  if (sep_len > 1)
	    {
	      FASTCOPY (sep, r, sep_len);
	      r += sep_len;
	    }
	  else
	    *r++ = sep[0];
	}

      word_len = strlen (t->word->word);
      FASTCOPY (t->word->word, r, word_len);
      r += word_len;
    }

  *r = '\0';
  return (result);
}

/* Return a single string of all the words present in LIST, separating
   each word with a space. */
char *
string_list (WORD_LIST *list)
{
  return (string_list_internal (list, " "));
}

/* An external interface that can be used by the rest of the shell to
   obtain a string containing the first character in $IFS.  Handles all
   the multibyte complications.  If LENP is non-null, it is set to the
   length of the returned string. */
char *
ifs_firstchar (int *lenp)
{
  char *ret;
  int len;

  ret = xmalloc (MB_LEN_MAX + 1);
#if defined (HANDLE_MULTIBYTE)
  if (ifs_firstc_len == 1)
    {
      ret[0] = ifs_firstc[0];
      ret[1] = '\0';
      len = ret[0] ? 1 : 0;
    }
  else
    {
      memcpy (ret, ifs_firstc, ifs_firstc_len);
      ret[len = ifs_firstc_len] = '\0';
    }
#else
  ret[0] = ifs_firstc;
  ret[1] = '\0';
  len = ret[0] ? 0 : 1;
#endif

  if (lenp)
    *lenp = len;

  return ret;
}

/* Return a single string of all the words present in LIST, obeying the
   quoting rules for "$*", to wit: (P1003.2, draft 11, 3.5.2) "If the
   expansion [of $*] appears within a double quoted string, it expands
   to a single field with the value of each parameter separated by the
   first character of the IFS variable, or by a <space> if IFS is unset." */
/* Posix interpretation 888 changes this when IFS is null by specifying
   that when unquoted, this expands to separate arguments */
char *
string_list_dollar_star (WORD_LIST *list, int quoted, int flags)
{
  char *ret;
#if defined (HANDLE_MULTIBYTE)
#  if defined (__GNUC__)
  char sep[MB_CUR_MAX + 1];
#  else
  char *sep = 0;
#  endif
#else
  char sep[2];
#endif

#if defined (HANDLE_MULTIBYTE)
#  if !defined (__GNUC__)
  sep = (char *)xmalloc (MB_CUR_MAX + 1);
#  endif /* !__GNUC__ */
  if (ifs_firstc_len == 1)
    {
      sep[0] = ifs_firstc[0];
      sep[1] = '\0';
    }
  else
    {
      memcpy (sep, ifs_firstc, ifs_firstc_len);
      sep[ifs_firstc_len] = '\0';
    }
#else
  sep[0] = ifs_firstc;
  sep[1] = '\0';
#endif

  ret = string_list_internal (list, sep);
#if defined (HANDLE_MULTIBYTE) && !defined (__GNUC__)
  free (sep);
#endif
  return ret;
}

/* Turn $@ into a string.  If (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
   is non-zero, the $@ appears within double quotes, and we should quote
   the list before converting it into a string.  If IFS is unset, and the
   word is not quoted, we just need to quote CTLESC and CTLNUL characters
   in the words in the list, because the default value of $IFS is
   <space><tab><newline>, IFS characters in the words in the list should
   also be split.  If IFS is null, and the word is not quoted, we need
   to quote the words in the list to preserve the positional parameters
   exactly.
   Valid values for the FLAGS argument are the PF_ flags in command.h,
   the only one we care about is PF_ASSIGNRHS.  $@ is supposed to expand
   to the positional parameters separated by spaces no matter what IFS is
   set to if in a context where word splitting is not performed.  The only
   one that we didn't handle before is assignment statement arguments to
   declaration builtins like `declare'. */
char *
string_list_dollar_at (WORD_LIST *list, int quoted, int flags)
{
  char *ifs, *ret;
#if defined (HANDLE_MULTIBYTE)
#  if defined (__GNUC__)
  char sep[MB_CUR_MAX + 1];
#  else
  char *sep = 0;
#  endif /* !__GNUC__ */
#else
  char sep[2];
#endif
  WORD_LIST *tlist;

  /* XXX this could just be ifs = ifs_value; */
  ifs = ifs_var ? value_cell (ifs_var) : (char *)0;

#if defined (HANDLE_MULTIBYTE)
#  if !defined (__GNUC__)
  sep = (char *)xmalloc (MB_CUR_MAX + 1);
#  endif /* !__GNUC__ */
  /* XXX - testing PF_ASSIGNRHS to make sure positional parameters are
     separated with a space even when word splitting will not occur. */
  if (flags & PF_ASSIGNRHS)
    {
      sep[0] = ' ';
      sep[1] = '\0';
    }
  else if (ifs && *ifs)
    {
      if (ifs_firstc_len == 1)
	{
	  sep[0] = ifs_firstc[0];
	  sep[1] = '\0';
	}
      else
	{
	  memcpy (sep, ifs_firstc, ifs_firstc_len);
	  sep[ifs_firstc_len] = '\0';
	}
    }
  else
    {
      sep[0] = ' ';
      sep[1] = '\0';
    }
#else	/* !HANDLE_MULTIBYTE */
  /* XXX - PF_ASSIGNRHS means no word splitting, so we want positional
     parameters separated by a space. */
  sep[0] = ((flags & PF_ASSIGNRHS) || ifs == 0 || *ifs == 0) ? ' ' : *ifs;
  sep[1] = '\0';
#endif	/* !HANDLE_MULTIBYTE */

  /* XXX -- why call quote_list if ifs == 0?  we can get away without doing
     it now that quote_escapes quotes spaces */
  tlist = (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES|Q_PATQUOTE))
		? quote_list (list)
		: list_quote_escapes (list);

  ret = string_list_internal (tlist, sep);
#if defined (HANDLE_MULTIBYTE) && !defined (__GNUC__)
  free (sep);
#endif
  return ret;
}

/* Turn the positional parameters into a string, understanding quoting and
   the various subtleties of using the first character of $IFS as the
   separator.  Calls string_list_dollar_at, string_list_dollar_star, and
   string_list as appropriate. */
/* This needs to fully understand the additional contexts where word
   splitting does not occur (W_ASSIGNRHS, etc.) */
char *
string_list_pos_params (int pchar, WORD_LIST *list, int quoted, int pflags)
{
  char *ret;
  WORD_LIST *tlist;

  if (pchar == '*' && (quoted & Q_DOUBLE_QUOTES))
    {
      tlist = quote_list (list);
      word_list_remove_quoted_nulls (tlist);
      ret = string_list_dollar_star (tlist, 0, 0);
    }
  else if (pchar == '*' && (quoted & Q_HERE_DOCUMENT))
    {
      tlist = quote_list (list);
      word_list_remove_quoted_nulls (tlist);
      ret = string_list (tlist);
    }
  else if (pchar == '*' && quoted == 0 && ifs_is_null)	/* XXX */
    ret = expand_no_split_dollar_star ? string_list_dollar_star (list, quoted, 0) : string_list_dollar_at (list, quoted, 0);	/* Posix interp 888 */
  else if (pchar == '*' && quoted == 0 && (pflags & PF_ASSIGNRHS))	/* XXX */
    ret = expand_no_split_dollar_star ? string_list_dollar_star (list, quoted, 0) : string_list_dollar_at (list, quoted, 0);	/* Posix interp 888 */
  else if (pchar == '*')
    {
      /* Even when unquoted, string_list_dollar_star does the right thing
	 making sure that the first character of $IFS is used as the
	 separator. */
      ret = string_list_dollar_star (list, quoted, 0);
    }
  else if (pchar == '@' && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
    /* We use string_list_dollar_at, but only if the string is quoted, since
       that quotes the escapes if it's not, which we don't want.  We could
       use string_list (the old code did), but that doesn't do the right
       thing if the first character of $IFS is not a space.  We use
       string_list_dollar_star if the string is unquoted so we make sure that
       the elements of $@ are separated by the first character of $IFS for
       later splitting. */
    ret = string_list_dollar_at (list, quoted, 0);
  else if (pchar == '@' && quoted == 0 && ifs_is_null)	/* XXX */
    ret = string_list_dollar_at (list, quoted, 0);	/* Posix interp 888 */
  else if (pchar == '@' && quoted == 0 && (pflags & PF_ASSIGNRHS))
    ret = string_list_dollar_at (list, quoted, pflags);	/* Posix interp 888 */
  else if (pchar == '@')
    ret = string_list_dollar_star (list, quoted, 0);
  else
    ret = string_list ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) ? quote_list (list) : list);

  return ret;
}

/* Return the list of words present in STRING.  Separate the string into
   words at any of the characters found in SEPARATORS.  If QUOTED is
   non-zero then word in the list will have its quoted flag set, otherwise
   the quoted flag is left as make_word () deemed fit.

   This obeys the P1003.2 word splitting semantics.  If `separators' is
   exactly <space><tab><newline>, then the splitting algorithm is that of
   the Bourne shell, which treats any sequence of characters from `separators'
   as a delimiter.  If IFS is unset, which results in `separators' being set
   to "", no splitting occurs.  If separators has some other value, the
   following rules are applied (`IFS white space' means zero or more
   occurrences of <space>, <tab>, or <newline>, as long as those characters
   are in `separators'):

	1) IFS white space is ignored at the start and the end of the
	   string.
	2) Each occurrence of a character in `separators' that is not
	   IFS white space, along with any adjacent occurrences of
	   IFS white space delimits a field.
	3) Any nonzero-length sequence of IFS white space delimits a field.
   */

/* BEWARE!  list_string strips null arguments.  Don't call it twice and
   expect to have "" preserved! */

/* This performs word splitting and quoted null character removal on
   STRING. */
#define issep(c) \
	(((separators)[0]) ? ((separators)[1] ? isifs(c) \
					      : (c) == (separators)[0]) \
			   : 0)

/* member of the space character class in the current locale */
#define ifs_whitespace(c)	ISSPACE(c)

/* "adjacent IFS white space" */
#define ifs_whitesep(c)	((sh_style_split || separators == 0) ? spctabnl (c) \
							     : ifs_whitespace (c))

WORD_LIST *
list_string (register char *string, register char *separators, int quoted)
{
  WORD_LIST *result;
  WORD_DESC *t;
  char *current_word, *s;
  int sindex, sh_style_split, whitesep, xflags, free_word;
  size_t slen;

  if (!string || !*string)
    return ((WORD_LIST *)NULL);

  sh_style_split = separators && separators[0] == ' ' &&
				 separators[1] == '\t' &&
				 separators[2] == '\n' &&
				 separators[3] == '\0';
  for (xflags = 0, s = ifs_value; s && *s; s++)
    {
      if (*s == CTLESC) xflags |= SX_NOCTLESC;
      else if (*s == CTLNUL) xflags |= SX_NOESCCTLNUL;
    }

  slen = 0;
  /* Remove sequences of whitespace at the beginning of STRING, as
     long as those characters appear in IFS.  Do not do this if
     STRING is quoted or if there are no separator characters. We use the
     Posix definition of whitespace as a member of the space character
     class in the current locale. */
#if 0
  if (!quoted || !separators || !*separators)
#else
  /* issep() requires that separators be non-null, and always returns 0 if
     separator is the empty string, so don't bother if we get an empty string
     for separators. We already returned NULL above if STRING is empty. */
  if (!quoted && separators && *separators)
#endif
    {
      for (s = string; *s && issep (*s) && ifs_whitespace (*s); s++);

      if (!*s)
	return ((WORD_LIST *)NULL);

      string = s;
    }

  /* OK, now STRING points to a word that does not begin with white space.
     The splitting algorithm is:
	extract a word, stopping at a separator
	skip sequences of whitespace characters as long as they are separators
     This obeys the field splitting rules in Posix.2. */
  slen = STRLEN (string);
  for (result = (WORD_LIST *)NULL, sindex = 0; string[sindex]; )
    {
      /* Don't need string length in ADVANCE_CHAR unless multibyte chars are
	 possible, but need it in string_extract_verbatim for bounds checking */
      current_word = string_extract_verbatim (string, slen, &sindex, separators, xflags);
      if (current_word == 0)
	break;

      free_word = 1;	/* If non-zero, we free current_word */

      /* If we have a quoted empty string, add a quoted null argument.  We
	 want to preserve the quoted null character iff this is a quoted
	 empty string; otherwise the quoted null characters are removed
	 below. */
      if (QUOTED_NULL (current_word))
	{
	  t = alloc_word_desc ();
	  t->word = make_quoted_char ('\0');
	  t->flags |= W_QUOTED|W_HASQUOTEDNULL;
	  result = make_word_list (t, result);
	}
      else if (current_word[0] != '\0')
	{
	  /* If we have something, then add it regardless.  However,
	     perform quoted null character removal on the current word. */
	  remove_quoted_nulls (current_word);

	  /* We don't want to set the word flags based on the string contents
	     here -- that's mostly for the parser -- so we just allocate a
	     WORD_DESC *, assign current_word (noting that we don't want to
	     free it), and skip all of make_word. */
	  t = alloc_word_desc ();
	  t->word = current_word;
	  result = make_word_list (t, result);
	  free_word = 0;
	  result->word->flags &= ~W_HASQUOTEDNULL;	/* just to be sure */
	  if (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT))
	    result->word->flags |= W_QUOTED;
	  /* If removing quoted null characters leaves an empty word, note
	     that we saw this for the caller to act on. */
	  if (current_word == 0 || current_word[0] == '\0')
	    result->word->flags |= W_SAWQUOTEDNULL;
	}

      /* If we're not doing sequences of separators in the traditional
	 Bourne shell style, then add a quoted null argument. */
      else if (!sh_style_split && !ifs_whitespace (string[sindex]))
	{
	  t = alloc_word_desc ();
	  t->word = make_quoted_char ('\0');
	  t->flags |= W_QUOTED|W_HASQUOTEDNULL;
	  result = make_word_list (t, result);
	}

      if (free_word)
	free (current_word);

      /* Note whether or not the separator is IFS whitespace, used later. */
      whitesep = string[sindex] && ifs_whitesep (string[sindex]);

      /* Move past the current separator character. */
      if (string[sindex])
	{
	  DECLARE_MBSTATE;
	  ADVANCE_CHAR (string, slen, sindex);
	}

      /* Now skip sequences of whitespace characters if they are
	 in the list of separators. */
      while (string[sindex] && ifs_whitesep (string[sindex]) && issep (string[sindex]))
	sindex++;

      /* If the first separator was IFS whitespace and the current character
	 is a non-whitespace IFS character, it should be part of the current
	 field delimiter, not a separate delimiter that would result in an
	 empty field.  Look at POSIX.2, 3.6.5, (3)(b). */
      if (string[sindex] && whitesep && issep (string[sindex]) && !ifs_whitesep (string[sindex]))
	{
	  sindex++;
	  /* An IFS character that is not IFS white space, along with any
	     adjacent IFS white space, shall delimit a field. (SUSv3) */
	  while (string[sindex] && ifs_whitesep (string[sindex]) && isifs (string[sindex]))
	    sindex++;
	}
    }
  return (REVERSE_LIST (result, WORD_LIST *));
}

/* Parse a single word from STRING, using SEPARATORS to separate fields.
   ENDPTR is set to the first character after the word.  This is used by
   the `read' builtin.
   
   This is never called with SEPARATORS != $IFS, and takes advantage of that.

   XXX - this function is very similar to list_string; they should be
	 combined - XXX */

/* character is in $IFS */
#define islocalsep(c)	(local_cmap[(unsigned char)(c)] != 0)

char *
get_word_from_string (char **stringp, char *separators, char **endptr)
{
  register char *s;
  char *current_word;
  int sindex, sh_style_split, whitesep, xflags;
  unsigned char local_cmap[UCHAR_MAX+1];	/* really only need single-byte chars here */
  size_t slen;

  if (!stringp || !*stringp || !**stringp)
    return ((char *)NULL);

  sh_style_split = separators && separators[0] == ' ' &&
				 separators[1] == '\t' &&
				 separators[2] == '\n' &&
				 separators[3] == '\0';
  memset (local_cmap, '\0', sizeof (local_cmap));
  for (xflags = 0, s = separators; s && *s; s++)
    {
      if (*s == CTLESC) xflags |= SX_NOCTLESC;
      if (*s == CTLNUL) xflags |= SX_NOESCCTLNUL;
      local_cmap[(unsigned char)*s] = 1;	/* local charmap of separators */
    }

  s = *stringp;
  slen = 0;

  /* Remove sequences of whitespace at the beginning of STRING, as
     long as those characters appear in SEPARATORS.  This happens if
     SEPARATORS == $' \t\n' or if IFS is unset. */
  if (sh_style_split || separators == 0)
    for (; *s && spctabnl (*s) && islocalsep (*s); s++);
  else
    for (; *s && ifs_whitespace (*s) && islocalsep (*s); s++);

  /* If the string is nothing but whitespace, update it and return. */
  if (!*s)
    {
      *stringp = s;
      if (endptr)
	*endptr = s;
      return ((char *)NULL);
    }

  /* OK, S points to a word that does not begin with white space.
     Now extract a word, stopping at a separator, save a pointer to
     the first character after the word, then skip sequences of spc,
     tab, or nl as long as they are separators.

     This obeys the field splitting rules in Posix.2. */
  sindex = 0;
  /* Don't need string length in ADVANCE_CHAR unless multibyte chars are
     possible, but need it in string_extract_verbatim for bounds checking */
  slen = STRLEN (s);
  current_word = string_extract_verbatim (s, slen, &sindex, separators, xflags);

  /* Set ENDPTR to the first character after the end of the word. */
  if (endptr)
    *endptr = s + sindex;

  /* Note whether or not the separator is IFS whitespace, used later. */
  whitesep = s[sindex] && ifs_whitesep (s[sindex]);

  /* Move past the current separator character. */
  if (s[sindex])
    {
      DECLARE_MBSTATE;
      ADVANCE_CHAR (s, slen, sindex);
    }

  /* Now skip sequences of space, tab, or newline characters if they are
     in the list of separators. */
  while (s[sindex] && spctabnl (s[sindex]) && islocalsep (s[sindex]))
    sindex++;

  /* If the first separator was IFS whitespace and the current character is
     a non-whitespace IFS character, it should be part of the current field
     delimiter, not a separate delimiter that would result in an empty field.
     Look at POSIX.2, 3.6.5, (3)(b). */
  if (s[sindex] && whitesep && islocalsep (s[sindex]) && !ifs_whitesep (s[sindex]))
    {
      sindex++;
      /* An IFS character that is not IFS white space, along with any adjacent
	 IFS white space, shall delimit a field. */
      while (s[sindex] && ifs_whitesep (s[sindex]) && islocalsep(s[sindex]))
	sindex++;
    }

  /* Update STRING to point to the next field. */
  *stringp = s + sindex;
  return (current_word);
}

/* Remove IFS white space at the end of STRING.  Start at the end
   of the string and walk backwards until the beginning of the string
   or we find a character that's not IFS white space and not CTLESC.
   Only let CTLESC escape a white space character if SAW_ESCAPE is
   non-zero.  */
char *
strip_trailing_ifs_whitespace (char *string, char *separators, int saw_escape)
{
  char *s;

  s = string + STRLEN (string) - 1;
  while (s > string && ((spctabnl (*s) && isifs (*s)) ||
			(saw_escape && *s == CTLESC && spctabnl (s[1]))))
    s--;
  *++s = '\0';
  return string;
}

#if 0
/* UNUSED */
/* Split STRING into words at whitespace.  Obeys shell-style quoting with
   backslashes, single and double quotes. */
WORD_LIST *
list_string_with_quotes (char *string)
{
  WORD_LIST *list;
  char *token, *s;
  size_t s_len;
  int c, i, tokstart, len;

  for (s = string; s && *s && spctabnl (*s); s++)
    ;
  if (s == 0 || *s == 0)
    return ((WORD_LIST *)NULL);

  s_len = strlen (s);
  tokstart = i = 0;
  list = (WORD_LIST *)NULL;
  while (1)
    {
      c = s[i];
      if (c == '\\')
	{
	  i++;
	  if (s[i])
	    i++;
	}
      else if (c == '\'')
	i = skip_single_quoted (s, s_len, ++i, 0);
      else if (c == '"')
	i = skip_double_quoted (s, s_len, ++i, 0);
      else if (c == 0 || spctabnl (c))
	{
	  /* We have found the end of a token.  Make a word out of it and
	     add it to the word list. */
	  token = substring (s, tokstart, i);
	  list = add_string_to_list (token, list);
	  free (token);
	  while (spctabnl (s[i]))
	    i++;
	  if (s[i])
	    tokstart = i;
	  else
	    break;
	}
      else
	i++;	/* normal character */
    }
  return (REVERSE_LIST (list, WORD_LIST *));
}
#endif

/********************************************************/
/*							*/
/*	Functions to perform assignment statements	*/
/*							*/
/********************************************************/

#if defined (ARRAY_VARS)
static SHELL_VAR *
do_compound_assignment (char *name, char *value, int flags)
{
  SHELL_VAR *v;
  int mklocal, mkassoc, mkglobal, chklocal;
  WORD_LIST *list;
  char *newname;	/* used for local nameref references */

  mklocal = flags & ASS_MKLOCAL;
  mkassoc = flags & ASS_MKASSOC;
  mkglobal = flags & ASS_MKGLOBAL;
  chklocal = flags & ASS_CHKLOCAL;

  if (mklocal && variable_context)
    {
      v = find_variable (name);		/* follows namerefs */
      newname = (v == 0) ? nameref_transform_name (name, flags) : v->name;
      if (v && ((readonly_p (v) && (flags & ASS_FORCE) == 0) || noassign_p (v)))
	{
	  if (readonly_p (v))
	    err_readonly (name);
	  return (v);	/* XXX */
	}
      list = expand_compound_array_assignment (v, value, flags);
      if (mkassoc)
	v = make_local_assoc_variable (newname, 0);
      else if (v == 0 || (array_p (v) == 0 && assoc_p (v) == 0) || v->context != variable_context)
        v = make_local_array_variable (newname, 0);
      if (v)
	assign_compound_array_list (v, list, flags);
      if (list)
	dispose_words (list);
    }
  /* In a function but forcing assignment in global context. CHKLOCAL means to
     check for an existing local variable first. */
  else if (mkglobal && variable_context)
    {
      v = chklocal ? find_variable (name) : 0;
      if (v && (local_p (v) == 0 || v->context != variable_context))
	v = 0;
      if (v == 0)
        v = find_global_variable (name);
      if (v && ((readonly_p (v) && (flags & ASS_FORCE) == 0) || noassign_p (v)))
	{
	  if (readonly_p (v))
	    err_readonly (name);
	  return (v);	/* XXX */
	}
      /* sanity check */
      newname = (v == 0) ? nameref_transform_name (name, flags) : name;
      list = expand_compound_array_assignment (v, value, flags);
      if (v == 0 && mkassoc)
	v = make_new_assoc_variable (newname);
      else if (v && mkassoc && assoc_p (v) == 0)
	v = convert_var_to_assoc (v);
      else if (v == 0)
	v = make_new_array_variable (newname);
      else if (v && mkassoc == 0 && array_p (v) == 0)
	v = convert_var_to_array (v);
      if (v)
	assign_compound_array_list (v, list, flags);
      if (list)
	dispose_words (list);
    }
  else
    {
      v = assign_array_from_string (name, value, flags);
      if (v && ((readonly_p (v) && (flags & ASS_FORCE) == 0) || noassign_p (v)))
	{
	  if (readonly_p (v))
	    err_readonly (name);
	  return (v);	/* XXX */
	}
    }

  return (v);
}
#endif

/* Given STRING, an assignment string, get the value of the right side
   of the `=', and bind it to the left side.  If EXPAND is true, then
   perform parameter expansion, command substitution, and arithmetic
   expansion on the right-hand side.  Perform tilde expansion in any
   case.  Do not perform word splitting on the result of expansion. */
static int
do_assignment_internal (const WORD_DESC *word, int expand)
{
  int offset, appendop, assign_list, aflags, retval;
  char *name, *value, *temp;
  SHELL_VAR *entry;
#if defined (ARRAY_VARS)
  char *t;
  int ni;
#endif
  const char *string;

  if (word == 0 || word->word == 0)
    return 0;

  appendop = assign_list = aflags = 0;
  string = word->word;
  offset = assignment (string, 0);
  name = savestring (string);
  value = (char *)NULL;

  if (name[offset] == '=')
    {
      if (name[offset - 1] == '+')
	{
	  appendop = 1;
	  name[offset - 1] = '\0';
	}

      name[offset] = 0;		/* might need this set later */
      temp = name + offset + 1;

#if defined (ARRAY_VARS)
      if (expand && (word->flags & W_COMPASSIGN))
	{
	  assign_list = ni = 1;
	  value = extract_array_assignment_list (temp, &ni);
	}
      else
#endif
      if (expand && temp[0])
	value = expand_string_if_necessary (temp, 0, expand_string_assignment);
      else
	value = savestring (temp);
    }

  if (value == 0)
    {
      value = (char *)xmalloc (1);
      value[0] = '\0';
    }

  if (echo_command_at_execute)
    {
      if (appendop)
	name[offset - 1] = '+';
      xtrace_print_assignment (name, value, assign_list, 1);
      if (appendop)
	name[offset - 1] = '\0';
    }

#define ASSIGN_RETURN(r)	do { FREE (value); free (name); return (r); } while (0)

  if (appendop)
    aflags |= ASS_APPEND;

#if defined (ARRAY_VARS)
  if (t = mbschr (name, LBRACK))
    {
      if (assign_list)
	{
	  report_error (_("%s: cannot assign list to array member"), name);
	  ASSIGN_RETURN (0);
	}
      aflags |= ASS_ALLOWALLSUB;	/* allow a[@]=value for existing associative arrays */
      entry = assign_array_element (name, value, aflags, (array_eltstate_t *)0);
      if (entry == 0)
	ASSIGN_RETURN (0);
    }
  else if (assign_list)
    {
      if ((word->flags & W_ASSIGNARG) && (word->flags & W_CHKLOCAL))
	aflags |= ASS_CHKLOCAL;
      if ((word->flags & W_ASSIGNARG) && (word->flags & W_ASSNGLOBAL) == 0)
	aflags |= ASS_MKLOCAL;
      if ((word->flags & W_ASSIGNARG) && (word->flags & W_ASSNGLOBAL))
	aflags |= ASS_MKGLOBAL;
      if (word->flags & W_ASSIGNASSOC)
	aflags |= ASS_MKASSOC;
      entry = do_compound_assignment (name, value, aflags);
    }
  else
#endif /* ARRAY_VARS */
  entry = bind_variable (name, value, aflags);

  if (entry)
    stupidly_hack_special_variables (entry->name);	/* might be a nameref */
  else
    stupidly_hack_special_variables (name);

  /* Return 1 if the assignment seems to have been performed correctly. */
  if (entry == 0 || readonly_p (entry))
    retval = 0;		/* assignment failure */
  else if (noassign_p (entry))
    {
      set_exit_status (EXECUTION_FAILURE);
      retval = 1;	/* error status, but not assignment failure */
    }
  else
    retval = 1;

  if (entry && retval != 0 && noassign_p (entry) == 0)
    VUNSETATTR (entry, att_invisible);

  ASSIGN_RETURN (retval);
}

/* Perform the assignment statement in STRING, and expand the
   right side by doing tilde, command and parameter expansion. */
int
do_assignment (char *string)
{
  WORD_DESC td;

  td.flags = W_ASSIGNMENT;
  td.word = string;

  return do_assignment_internal (&td, 1);
}

int
do_word_assignment (WORD_DESC *word, int flags)
{
  return do_assignment_internal (word, 1);
}

/* Given STRING, an assignment string, get the value of the right side
   of the `=', and bind it to the left side.  Do not perform any word
   expansions on the right hand side. */
int
do_assignment_no_expand (char *string)
{
  WORD_DESC td;

  td.flags = W_ASSIGNMENT;
  td.word = string;

  return (do_assignment_internal (&td, 0));
}

/***************************************************
 *						   *
 *  Functions to manage the positional parameters  *
 *						   *
 ***************************************************/

/* Return the word list that corresponds to `$*'. */
WORD_LIST *
list_rest_of_args ()
{
  register WORD_LIST *list, *args;
  int i;

  /* Break out of the loop as soon as one of the dollar variables is null. */
  for (i = 1, list = (WORD_LIST *)NULL; i < 10 && dollar_vars[i]; i++)
    list = make_word_list (make_bare_word (dollar_vars[i]), list);

  for (args = rest_of_args; args; args = args->next)
    list = make_word_list (make_bare_word (args->word->word), list);

  return (REVERSE_LIST (list, WORD_LIST *));
}

/* Return the value of a positional parameter.  This handles values > 10. */
char *
get_dollar_var_value (intmax_t ind)
{
  char *temp;
  WORD_LIST *p;

  if (ind < 10)
    temp = dollar_vars[ind] ? savestring (dollar_vars[ind]) : (char *)NULL;
  else	/* We want something like ${11} */
    {
      ind -= 10;
      for (p = rest_of_args; p && ind--; p = p->next)
	;
      temp = p ? savestring (p->word->word) : (char *)NULL;
    }
  return (temp);
}

/* Make a single large string out of the dollar digit variables,
   and the rest_of_args.  If DOLLAR_STAR is 1, then obey the special
   case of "$*" with respect to IFS. */
char *
string_rest_of_args (int dollar_star)
{
  register WORD_LIST *list;
  char *string;

  list = list_rest_of_args ();
  string = dollar_star ? string_list_dollar_star (list, 0, 0) : string_list (list);
  dispose_words (list);
  return (string);
}

/* Return a string containing the positional parameters from START to
   END, inclusive.  If STRING[0] == '*', we obey the rules for $*,
   which only makes a difference if QUOTED is non-zero.  If QUOTED includes
   Q_HERE_DOCUMENT or Q_DOUBLE_QUOTES, this returns a quoted list, otherwise
   no quoting chars are added. */
static char *
pos_params (char *string, int start, int end, int quoted, int pflags)
{
  WORD_LIST *save, *params, *h, *t;
  char *ret;
  int i;

  /* see if we can short-circuit.  if start == end, we want 0 parameters. */
  if (start == end)
    return ((char *)NULL);

  save = params = list_rest_of_args ();
  if (save == 0 && start > 0)
    return ((char *)NULL);

  if (start == 0)		/* handle ${@:0[:x]} specially */
    {
      t = make_word_list (make_word (dollar_vars[0]), params);
      save = params = t;
    }

  for (i = start ? 1 : 0; params && i < start; i++)
    params = params->next;
  if (params == 0)
    {
      dispose_words (save);
      return ((char *)NULL);
    }
  for (h = t = params; params && i < end; i++)
    {
      t = params;
      params = params->next;
    }
  t->next = (WORD_LIST *)NULL;

  ret = string_list_pos_params (string[0], h, quoted, pflags);

  if (t != params)
    t->next = params;

  dispose_words (save);
  return (ret);
}

/******************************************************************/
/*								  */
/*	Functions to expand strings to strings or WORD_LISTs      */
/*								  */
/******************************************************************/

#if defined (PROCESS_SUBSTITUTION)
#define EXP_CHAR(s) (s == '$' || s == '`' || s == '<' || s == '>' || s == CTLESC || s == '~')
#else
#define EXP_CHAR(s) (s == '$' || s == '`' || s == CTLESC || s == '~')
#endif

/* We don't perform process substitution in arithmetic expressions, so don't
   bother checking for it. */
#define ARITH_EXP_CHAR(s) (s == '$' || s == '`' || s == CTLESC || s == '~')

/* If there are any characters in STRING that require full expansion,
   then call FUNC to expand STRING; otherwise just perform quote
   removal if necessary.  This returns a new string. */
char *
expand_string_if_necessary (char *string, int quoted, EXPFUNC *func)
{
  WORD_LIST *list;
  size_t slen;
  int i, saw_quote;
  char *ret;
  DECLARE_MBSTATE;

  /* Don't need string length for ADVANCE_CHAR unless multibyte chars possible. */
  slen = (MB_CUR_MAX > 1) ? strlen (string) : 0;
  i = saw_quote = 0;
  while (string[i])
    {
      if (EXP_CHAR (string[i]))
	break;
      else if (string[i] == '\'' || string[i] == '\\' || string[i] == '"')
	saw_quote = 1;
      ADVANCE_CHAR (string, slen, i);
    }

  if (string[i])
    {
      list = (*func) (string, quoted);
      if (list)
	{
	  ret = string_list (list);
	  dispose_words (list);
	}
      else
	ret = (char *)NULL;
    }
  else if (saw_quote && ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) == 0))
    ret = string_quote_removal (string, quoted);
  else
    ret = savestring (string);

  return ret;
}

char *
expand_string_to_string_internal (char *string, int quoted, EXPFUNC *func)
{
  WORD_LIST *list;
  char *ret;

  if (string == 0 || *string == '\0')
    return ((char *)NULL);

  list = (*func) (string, quoted);
  if (list)
    {
      ret = string_list (list);
      dispose_words (list);
    }
  else
    ret = (char *)NULL;

  return (ret);
}

char *
expand_string_to_string (char *string, int quoted)
{
  return (expand_string_to_string_internal (string, quoted, expand_string));
}

char *
expand_string_unsplit_to_string (char *string, int quoted)
{
  return (expand_string_to_string_internal (string, quoted, expand_string_unsplit));
}

char *
expand_assignment_string_to_string (char *string, int quoted)
{
  return (expand_string_to_string_internal (string, quoted, expand_string_assignment));
}

/* Kind of like a combination of dequote_string and quote_string_for_globbing;
   try to remove CTLESC quoting characters and convert CTLESC escaping a `&'
   or a backslash into a backslash. The output of this function must eventually
   be processed by strcreplace(). */
static char *
quote_string_for_repl (char *string, int flags)
{
  size_t slen;
  char *result, *t;
  const char *s, *send;
  DECLARE_MBSTATE;

  slen = strlen (string);
  send = string + slen;

  result = (char *)xmalloc (slen * 2 + 1);

  if (string[0] == CTLESC && string[1] == 0)
    {
      result[0] = CTLESC;
      result[1] = '\0';
      return (result);
    }

  /* This is awkward. We want to translate CTLESC-\ to \\ if we will
     eventually send this string through strcreplace(), which we will do
     only if shouldexp_replacement() determines that there is something
     to replace. We can either make sure to escape backslashes here and
     have shouldexp_replacement() signal that we should send the string to
     strcreplace() if it sees an escaped backslash, or we can scan the
     string before copying it and turn CTLESC-\ into \\ only if we encounter
     a CTLESC-& or a &. This does the former and changes shouldexp_replacement().
     If we double the backslashes  here, we'll get doubled backslashes in any
     result that doesn't get passed to strcreplace(). */

  for (s = string, t = result; *s; )
    {
      /* This function's result has to be processed by strcreplace() */
      if (*s == CTLESC && (s[1] == '&' || s[1] == '\\'))
        {
          *t++ = '\\';
          s++;
          *t++ = *s++;
          continue;
        }
      /* Dequote it */
      if (*s == CTLESC)
        {
	  s++;
	  if (*s == '\0')
	    break;
        }
      COPY_CHAR_P (t, s, send);
    }

  *t = '\0';
  return (result);
}
	
/* This does not perform word splitting on the WORD_LIST it returns and
   it treats $* as if it were quoted. It dequotes the WORD_LIST, adds
   backslash escapes before CTLESC-quoted backslash and `& if 
   patsub_replacement is enabled. */
char *
expand_string_for_patsub (char *string, int quoted)
{
  WORD_LIST *value;
  char *ret, *t;

  if (string == 0 || *string == '\0')
    return (char *)NULL;

  value = expand_string_for_pat (string, quoted, (int *)0, (int *)0);

  if (value && value->word)
    {
      remove_quoted_nulls (value->word->word);	/* XXX */
      value->word->flags &= ~W_HASQUOTEDNULL;
    }

  if (value)
    {
      t = (value->next) ? string_list (value) : value->word->word;
      ret = quote_string_for_repl (t, quoted);
      if (t != value->word->word)
	free (t);
      dispose_words (value);
    }
  else
    ret = (char *)NULL;

  return (ret);
}

char *
expand_arith_string (char *string, int quoted)
{
  WORD_DESC td;
  WORD_LIST *list, *tlist;
  size_t slen;
  int i, saw_quote;
  char *ret;
  DECLARE_MBSTATE;

  /* Don't need string length for ADVANCE_CHAR unless multibyte chars possible. */
  slen = (MB_CUR_MAX > 1) ? strlen (string) : 0;
  i = saw_quote = 0;
  while (string[i])
    {
      if (ARITH_EXP_CHAR (string[i]))
	break;
      else if (string[i] == '\'' || string[i] == '\\' || string[i] == '"')
	saw_quote = string[i];
      ADVANCE_CHAR (string, slen, i);
    }

  if (string[i])
    {
      /* This is expanded version of expand_string_internal as it's called by
	 expand_string_leave_quoted  */
      td.flags = W_NOPROCSUB|W_NOTILDE;	/* don't want process substitution or tilde expansion */
#if 0	/* TAG: bash-5.2 */
      if (quoted & Q_ARRAYSUB)
	td.flags |= W_NOCOMSUB;
#endif
      td.word = savestring (string);
      list = call_expand_word_internal (&td, quoted, 0, (int *)NULL, (int *)NULL);
      /* This takes care of the calls from expand_string_leave_quoted and
	 expand_string */
      if (list)
	{
	  tlist = word_list_split (list);
	  dispose_words (list);
	  list = tlist;
	  if (list)
	    dequote_list (list);
	}
      /* This comes from expand_string_if_necessary */
      if (list)
	{
	  ret = string_list (list);
	  dispose_words (list);
	}
      else
	ret = (char *)NULL;
      FREE (td.word);
    }
  else if (saw_quote && (quoted & Q_ARITH))
    ret = string_quote_removal (string, quoted);
  else if (saw_quote && ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) == 0))
    ret = string_quote_removal (string, quoted);
  else
    ret = savestring (string);

  return ret;
}

#if defined (COND_COMMAND)
/* Just remove backslashes in STRING.  Returns a new string. */
char *
remove_backslashes (char *string)
{
  char *r, *ret, *s;

  r = ret = (char *)xmalloc (strlen (string) + 1);
  for (s = string; s && *s; )
    {
      if (*s == '\\')
	s++;
      if (*s == 0)
	break;
      *r++ = *s++;
    }
  *r = '\0';
  return ret;
}

/* This needs better error handling. */
/* Expand W for use as an argument to a unary or binary operator in a
   [[...]] expression.  If SPECIAL is 1, this is the rhs argument
   to the != or == operator, and should be treated as a pattern.  In
   this case, we quote the string specially for the globbing code.  If
   SPECIAL is 2, this is an rhs argument for the =~ operator, and should
   be quoted appropriately for regcomp/regexec.  If SPECIAL is 3, this is
   an array subscript and should be quoted after expansion so it's only
   expanded once (Q_ARITH). The caller is responsible
   for removing the backslashes if the unquoted word is needed later. In
   any case, since we don't perform word splitting, we need to do quoted
   null character removal. */
char *
cond_expand_word (WORD_DESC *w, int special)
{
  char *r, *p;
  WORD_LIST *l;
  int qflags;

  if (w->word == 0 || w->word[0] == '\0')
    return ((char *)NULL);

  expand_no_split_dollar_star = 1;
  w->flags |= W_NOSPLIT2;
  qflags = (special == 3) ? Q_ARITH : 0;
  l = call_expand_word_internal (w, qflags, 0, (int *)0, (int *)0);
  expand_no_split_dollar_star = 0;
  if (l)
    {
      if (special == 0)			/* LHS */
	{
	  if (l->word)
	    word_list_remove_quoted_nulls (l);
	  dequote_list (l);
	  r = string_list (l);
	}
      else if (special == 3)		/* arithmetic expression, Q_ARITH */
	{
	  if (l->word)
	    word_list_remove_quoted_nulls (l);	/* for now */
	  dequote_list (l);
	  r = string_list (l);
	}
      else
	{
	  /* Need to figure out whether or not we should call dequote_escapes
	     or a new dequote_ctlnul function here, and under what
	     circumstances. */
	  qflags = QGLOB_CVTNULL|QGLOB_CTLESC;
	  if (special == 2)
	    qflags |= QGLOB_REGEXP;
	  word_list_remove_quoted_nulls (l);
	  p = string_list (l);
	  r = quote_string_for_globbing (p, qflags);
	  free (p);
	}
      dispose_words (l);
    }
  else
    r = (char *)NULL;

  return r;
}
#endif

/* Expand $'...' and $"..." in a string for code paths that don't do it. The
   FLAGS argument is 1 if this function should treat CTLESC as a quote
   character (e.g., for here-documents) or not (e.g., for shell_expand_line). */
char *
expand_string_dollar_quote (char *string, int flags)
{
  size_t slen, retind, retsize;
  int sindex, c, translen, peekc, news;
  char *ret, *trans, *send, *t;
  DECLARE_MBSTATE;

  slen = strlen (string);
  send = string + slen;
  sindex = 0;

  retsize = slen + 1;
  ret = xmalloc (retsize);
  retind = 0;

  while (c = string[sindex])
    {
      switch (c)
	{
	default:
	  RESIZE_MALLOCED_BUFFER (ret, retind, locale_mb_cur_max + 1, retsize, 64);
	  COPY_CHAR_I (ret, retind, string, send, sindex);
	  break;

	case '\\':
	  RESIZE_MALLOCED_BUFFER (ret, retind, locale_mb_cur_max + 2, retsize, 64);
	  ret[retind++] = string[sindex++];

	  if (string[sindex])
	    COPY_CHAR_I (ret, retind, string, send, sindex);
	  break;

	case '\'':
	case '"':
	  if (c == '\'')
	    news = skip_single_quoted (string, slen, ++sindex, SX_COMPLETE);
	  else
	    news = skip_double_quoted (string, slen, ++sindex, SX_COMPLETE);
	  translen = news - sindex - 1;
	  RESIZE_MALLOCED_BUFFER (ret, retind, translen + 3, retsize, 64);
	  ret[retind++] = c;
	  if (translen > 0)
	    {
	      strncpy (ret + retind, string + sindex, translen);
	      retind += translen;
	    }
	  if (news > sindex && string[news - 1] == c)
	    ret[retind++] = c;
	  sindex = news;
	  break;

	case CTLESC:
	  RESIZE_MALLOCED_BUFFER (ret, retind, locale_mb_cur_max + 2, retsize, 64);
	  if (flags)
	    ret[retind++] = string[sindex++];
	  if (string[sindex])
	    COPY_CHAR_I (ret, retind, string, send, sindex);
	  break;

	case '$':
	  peekc = string[++sindex];
#if defined (TRANSLATABLE_STRINGS)
	  if (peekc != '\'' && peekc != '"')
#else
	  if (peekc != '\'')
#endif
	    {
	      RESIZE_MALLOCED_BUFFER (ret, retind, 2, retsize, 16);
	      ret[retind++] = c;
	      break;
	    }
	  if (string[sindex + 1] == '\0')	/* don't bother */	
	    {
	      RESIZE_MALLOCED_BUFFER (ret, retind, 3, retsize, 16);
	      ret[retind++] = c;
	      ret[retind++] = peekc;
	      sindex++;
	      break;
	    }
	  if (peekc == '\'')
	    {
	      /* SX_COMPLETE is the  equivalent of ALLOWESC here */
	      /* We overload SX_COMPLETE below */
	      news = skip_single_quoted (string, slen, ++sindex, SX_COMPLETE);
	      /* Check for unclosed string and don't bother if so */
	      if (news > sindex && string[news] == '\0' && string[news-1] != peekc)
		{
		  RESIZE_MALLOCED_BUFFER (ret, retind, 3, retsize, 16);
		  ret[retind++] = c;
		  ret[retind++] = peekc;
		  continue;
		}
	      t = substring (string, sindex, news - 1);
	      trans = ansiexpand (t, 0, news-sindex-1, &translen);
	      free (t);
	      t = sh_single_quote (trans);
	      sindex = news;
	    }
#if defined (TRANSLATABLE_STRINGS)
	  else
	    {
	      news = ++sindex;
	      t = string_extract_double_quoted (string, &news, SX_COMPLETE);
	      /* Check for unclosed string and don't bother if so */
	      if (news > sindex && string[news] == '\0' && string[news-1] != peekc)
		{
		  RESIZE_MALLOCED_BUFFER (ret, retind, 3, retsize, 16);
		  ret[retind++] = c;
		  ret[retind++] = peekc;
		  free (t);
		  continue;
		}
	      trans = locale_expand (t, 0, news-sindex, 0, &translen);
	      free (t);
	      if (singlequote_translations &&
		    ((news-sindex-1) != translen || STREQN (t, trans, translen) == 0))
		t = sh_single_quote (trans);
	      else
		t = sh_mkdoublequoted (trans, translen, 0);
	      sindex = news;
	    }
#endif /* TRANSLATABLE_STRINGS */
	  free (trans);
	  trans = t;
	  translen = strlen (trans);

	  RESIZE_MALLOCED_BUFFER (ret, retind, translen + 1, retsize, 128);
	  strcpy (ret + retind, trans);
	  retind += translen;
	  FREE (trans);
	  break;
	}
    }

  ret[retind] = 0;
  return ret;
}

/* Call expand_word_internal to expand W and handle error returns.
   A convenience function for functions that don't want to handle
   any errors or free any memory before aborting. */
static WORD_LIST *
call_expand_word_internal (WORD_DESC *w, int q, int i, int *c, int *e)
{
  WORD_LIST *result;

  result = expand_word_internal (w, q, i, c, e);
  if (result == &expand_word_error || result == &expand_word_fatal)
    {
      /* By convention, each time this error is returned, w->word has
	 already been freed (it sometimes may not be in the fatal case,
	 but that doesn't result in a memory leak because we're going
	 to exit in most cases). */
      w->word = (char *)NULL;
      last_command_exit_value = EXECUTION_FAILURE;
      exp_jump_to_top_level ((result == &expand_word_error) ? DISCARD : FORCE_EOF);
      /* NOTREACHED */
      return (NULL);
    }
  else
    return (result);
}

/* Perform parameter expansion, command substitution, and arithmetic
   expansion on STRING, as if it were a word.  Leave the result quoted.
   Since this does not perform word splitting, it leaves quoted nulls
   in the result.  */
static WORD_LIST *
expand_string_internal (char *string, int quoted)
{
  WORD_DESC td;
  WORD_LIST *tresult;

  if (string == 0 || *string == 0)
    return ((WORD_LIST *)NULL);

  td.flags = 0;
  td.word = savestring (string);

  tresult = call_expand_word_internal (&td, quoted, 0, (int *)NULL, (int *)NULL);

  FREE (td.word);
  return (tresult);
}

/* Expand STRING by performing parameter expansion, command substitution,
   and arithmetic expansion.  Dequote the resulting WORD_LIST before
   returning it, but do not perform word splitting.  The call to
   remove_quoted_nulls () is in here because word splitting normally
   takes care of quote removal. */
WORD_LIST *
expand_string_unsplit (char *string, int quoted)
{
  WORD_LIST *value;

  if (string == 0 || *string == '\0')
    return ((WORD_LIST *)NULL);

  expand_no_split_dollar_star = 1;
  value = expand_string_internal (string, quoted);
  expand_no_split_dollar_star = 0;

  if (value)
    {
      if (value->word)
	{
	  remove_quoted_nulls (value->word->word);	/* XXX */
	  value->word->flags &= ~W_HASQUOTEDNULL;
	}
      dequote_list (value);
    }
  return (value);
}

/* Expand the rhs of an assignment statement */
WORD_LIST *
expand_string_assignment (char *string, int quoted)
{
  WORD_DESC td;
  WORD_LIST *value;

  if (string == 0 || *string == '\0')
    return ((WORD_LIST *)NULL);

  expand_no_split_dollar_star = 1;

#if 0
  /* Other shells (ksh93) do it this way, which affects how $@ is expanded
     in constructs like bar=${@#0} (preserves the spaces resulting from the
     expansion of $@ in a context where you don't do word splitting); Posix
     interp 888 makes the expansion of $@ in contexts where word splitting
     is not performed unspecified. */
  td.flags = W_ASSIGNRHS|W_NOSPLIT2;		/* Posix interp 888 */
#else
  td.flags = W_ASSIGNRHS;
#endif
  td.flags |= (W_NOGLOB|W_TILDEEXP);
  td.word = savestring (string);
  value = call_expand_word_internal (&td, quoted, 0, (int *)NULL, (int *)NULL);
  FREE (td.word);

  expand_no_split_dollar_star = 0;

  if (value)
    {
      if (value->word)
	{
	  remove_quoted_nulls (value->word->word);	/* XXX */
	  value->word->flags &= ~W_HASQUOTEDNULL;
	}
      dequote_list (value);
    }
  return (value);
}

/* Expand one of the PS? prompt strings. This is a sort of combination of
   expand_string_unsplit and expand_string_internal, but returns the
   passed string when an error occurs.  Might want to trap other calls
   to jump_to_top_level here so we don't endlessly loop. */
WORD_LIST *
expand_prompt_string (char *string, int quoted, int wflags)
{
  WORD_LIST *value;
  WORD_DESC td;

  if (string == 0 || *string == 0)
    return ((WORD_LIST *)NULL);

  td.flags = wflags;
  td.word = savestring (string);

  no_longjmp_on_fatal_error = 1;
  value = expand_word_internal (&td, quoted, 0, (int *)NULL, (int *)NULL);
  no_longjmp_on_fatal_error = 0;

  if (value == &expand_word_error || value == &expand_word_fatal)
    {
      value = make_word_list (make_bare_word (string), (WORD_LIST *)NULL);
      return value;
    }
  FREE (td.word);
  if (value)
    {
      if (value->word)
	{
	  remove_quoted_nulls (value->word->word);	/* XXX */
	  value->word->flags &= ~W_HASQUOTEDNULL;
	}
      dequote_list (value);
    }
  return (value);
}

/* Expand STRING just as if you were expanding a word, but do not dequote
   the resultant WORD_LIST.  This is called only from within this file,
   and is used to correctly preserve quoted characters when expanding
   things like ${1+"$@"}.  This does parameter expansion, command
   substitution, arithmetic expansion, and word splitting. */
static WORD_LIST *
expand_string_leave_quoted (char *string, int quoted)
{
  WORD_LIST *tlist;
  WORD_LIST *tresult;

  if (string == 0 || *string == '\0')
    return ((WORD_LIST *)NULL);

  tlist = expand_string_internal (string, quoted);

  if (tlist)
    {
      tresult = word_list_split (tlist);
      dispose_words (tlist);
      return (tresult);
    }
  return ((WORD_LIST *)NULL);
}

/* This does not perform word splitting or dequote the WORD_LIST
   it returns. */
static WORD_LIST *
expand_string_for_rhs (char *string, int quoted, int op, int pflags, int *dollar_at_p, int *expanded_p)
{
  WORD_DESC td;
  WORD_LIST *tresult;
  int old_nosplit;

  if (string == 0 || *string == '\0')
    return (WORD_LIST *)NULL;

  /* We want field splitting to be determined by what is going to be done with
     the entire ${parameterOPword} expansion, so we don't want to split the RHS
     we expand here.  However, the expansion of $* is determined by whether we
     are going to eventually perform word splitting, so we want to set this
     depending on whether or not are are going to be splitting: if the expansion
     is quoted, if the OP is `=', or if IFS is set to the empty string, we
     are not going to be splitting, so we set expand_no_split_dollar_star to
     note this to callees.
     We pass through PF_ASSIGNRHS as W_ASSIGNRHS if this is on the RHS of an
     assignment statement. */
  /* The updated treatment of $* is the result of Posix interp 888 */
  /* This was further clarified on the austin-group list in March, 2017 and
     in Posix bug 1129 */
  old_nosplit = expand_no_split_dollar_star;
  expand_no_split_dollar_star = (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) || op == '=' || ifs_is_null == 0;	/* XXX - was 1 */
  td.flags = W_EXPANDRHS;		/* expanding RHS of ${paramOPword} */
  td.flags |= W_NOSPLIT2;		/* no splitting, remove "" and '' */
  if (pflags & PF_ASSIGNRHS)		/* pass through */
    td.flags |= W_ASSIGNRHS;
  if (op == '=')
#if 0
    td.flags |= W_ASSIGNRHS;		/* expand b in ${a=b} like assignment */
#else
    td.flags |= W_ASSIGNRHS|W_NOASSNTILDE;		/* expand b in ${a=b} like assignment */
#endif
  td.word = savestring (string);
  tresult = call_expand_word_internal (&td, quoted, 1, dollar_at_p, expanded_p);
  expand_no_split_dollar_star = old_nosplit;
  free (td.word);

  return (tresult);
}

/* This does not perform word splitting or dequote the WORD_LIST
   it returns and it treats $* as if it were quoted. */
WORD_LIST *
expand_string_for_pat (char *string, int quoted, int *dollar_at_p, int *expanded_p)
{
  WORD_DESC td;
  WORD_LIST *tresult;
  int oexp;

  if (string == 0 || *string == '\0')
    return (WORD_LIST *)NULL;

  oexp = expand_no_split_dollar_star;
  expand_no_split_dollar_star = 1;
  td.flags = W_NOSPLIT2;		/* no splitting, remove "" and '' */
  td.word = savestring (string);
  tresult = call_expand_word_internal (&td, quoted, 1, dollar_at_p, expanded_p);
  expand_no_split_dollar_star = oexp;
  free (td.word);

  return (tresult);
}

/* Expand STRING just as if you were expanding a word.  This also returns
   a list of words.  Note that filename globbing is *NOT* done for word
   or string expansion, just when the shell is expanding a command.  This
   does parameter expansion, command substitution, arithmetic expansion,
   and word splitting.  Dequote the resultant WORD_LIST before returning. */
WORD_LIST *
expand_string (char *string, int quoted)
{
  WORD_LIST *result;

  if (string == 0 || *string == '\0')
    return ((WORD_LIST *)NULL);

  result = expand_string_leave_quoted (string, quoted);
  return (result ? dequote_list (result) : result);
}

/*******************************************
 *					   *
 *	Functions to expand WORD_DESCs	   *
 *					   *
 *******************************************/

/* Expand WORD, performing word splitting on the result.  This does
   parameter expansion, command substitution, arithmetic expansion,
   word splitting, and quote removal. */

WORD_LIST *
expand_word (WORD_DESC *word, int quoted)
{
  WORD_LIST *result, *tresult;

  tresult = call_expand_word_internal (word, quoted, 0, (int *)NULL, (int *)NULL);
  result = word_list_split (tresult);
  dispose_words (tresult);
  return (result ? dequote_list (result) : result);
}

/* Expand WORD, but do not perform word splitting on the result.  This
   does parameter expansion, command substitution, arithmetic expansion,
   and quote removal. */
WORD_LIST *
expand_word_unsplit (WORD_DESC *word, int quoted)
{
  WORD_LIST *result;

  result = expand_word_leave_quoted (word, quoted);
  return (result ? dequote_list (result) : result);
}

/* Perform shell expansions on WORD, but do not perform word splitting or
   quote removal on the result.  Virtually identical to expand_word_unsplit;
   could be combined if implementations don't diverge. */
WORD_LIST *
expand_word_leave_quoted (WORD_DESC *word, int quoted)
{
  WORD_LIST *result;

  expand_no_split_dollar_star = 1;
  if (ifs_is_null)
    word->flags |= W_NOSPLIT;
  word->flags |= W_NOSPLIT2;
  result = call_expand_word_internal (word, quoted, 0, (int *)NULL, (int *)NULL);
  expand_no_split_dollar_star = 0;

  return result;
}

/* Process substitution functions moved to subst_procsub.c */
#if defined (PROCESS_SUBSTITUTION)
#include "subst_procsub.h"
#endif /* PROCESS_SUBSTITUTION */


/********************************************************
 *							*
 *	Utility functions for parameter expansion	*
 *							*
 ********************************************************/

#if defined (ARRAY_VARS)

static arrayind_t
array_length_reference (char *s)
{
  int len;
  arrayind_t ind;
  char *akey;
  char *t, c;
  ARRAY *array;
  HASH_TABLE *h;
  SHELL_VAR *var;

  var = array_variable_part (s, 0, &t, &len);

  /* If unbound variables should generate an error, report one and return
     failure. */
  if ((var == 0 || invisible_p (var) || (assoc_p (var) == 0 && array_p (var) == 0)) && unbound_vars_is_error)
    {
      c = *--t;
      *t = '\0';
      set_exit_status (EXECUTION_FAILURE);
      err_unboundvar (s);
      *t = c;
      return (-1);
    }
  else if (var == 0 || invisible_p (var))
    return 0;

  /* We support a couple of expansions for variables that are not arrays.
     We'll return the length of the value for v[0], and 1 for v[@] or
     v[*].  Return 0 for everything else. */

  array = array_p (var) ? array_cell (var) : (ARRAY *)NULL;
  h = assoc_p (var) ? assoc_cell (var) : (HASH_TABLE *)NULL;

  if (ALL_ELEMENT_SUB (t[0]) && t[1] == RBRACK)
    {
      if (assoc_p (var))
	return (h ? assoc_num_elements (h) : 0);
      else if (array_p (var))
	return (array ? array_num_elements (array) : 0);
      else
	return (var_isset (var) ? 1 : 0);
    }

  if (assoc_p (var))
    {
      t[len - 1] = '\0';
      akey = expand_subscript_string (t, 0);	/* [ */
      t[len - 1] = RBRACK;
      if (akey == 0 || *akey == 0)
	{
	  err_badarraysub (t);
	  FREE (akey);
	  return (-1);
	}
      t = assoc_reference (assoc_cell (var), akey);
      free (akey);
    }
  else
    {
      ind = array_expand_index (var, t, len, 0);
      /* negative subscripts to indexed arrays count back from end */
      if (var && array_p (var) && ind < 0)
	ind = array_max_index (array_cell (var)) + 1 + ind;
      if (ind < 0)
	{
	  err_badarraysub (t);
	  return (-1);
	}
      if (array_p (var))
	t = array_reference (array, ind);
      else
	t = (ind == 0) ? value_cell (var) : (char *)NULL;
    }

  len = MB_STRLEN (t);
  return (len);
}
#endif /* ARRAY_VARS */

static int
valid_brace_expansion_word (const char *name, int var_is_special)
{
  if (DIGIT (*name) && all_digits (name))
    return 1;
  else if (var_is_special)
    return 1;
#if defined (ARRAY_VARS)
  else if (valid_array_reference (name, 0))
    return 1;
#endif /* ARRAY_VARS */
  else if (legal_identifier (name))
    return 1;
  else
    return 0;
}

static int
chk_atstar (char *name, int quoted, int pflags, int *quoted_dollar_atp, int *contains_dollar_at)
{
  char *temp1;

  if (name == 0)
    {
      if (quoted_dollar_atp)
	*quoted_dollar_atp = 0;
      if (contains_dollar_at)
	*contains_dollar_at = 0;
      return 0;
    }

  /* check for $@ and $* */
  if (name[0] == '@' && name[1] == 0)
    {
      if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && quoted_dollar_atp)
	*quoted_dollar_atp = 1;
      if (contains_dollar_at)
	*contains_dollar_at = 1;
      return 1;
    }
  else if (name[0] == '*' && name[1] == '\0' && quoted == 0)
    {
      /* Need more checks here that parallel what string_list_pos_params and
	 param_expand do. Check expand_no_split_dollar_star and ??? */
      if (contains_dollar_at && expand_no_split_dollar_star == 0)
	*contains_dollar_at = 1;
      return 1;
    }

  /* Now check for ${array[@]} and ${array[*]} */
#if defined (ARRAY_VARS)
  else if (valid_array_reference (name, 0))
    {
      temp1 = mbschr (name, LBRACK);
      if (temp1 && temp1[1] == '@' && temp1[2] == RBRACK)
	{
	  if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && quoted_dollar_atp)
	    *quoted_dollar_atp = 1;
	  if (contains_dollar_at)
	    *contains_dollar_at = 1;
	  return 1;
	}
      /* ${array[*]}, when unquoted, should be treated like ${array[@]},
	 which should result in separate words even when IFS is unset. */
      if (temp1 && temp1[1] == '*' && temp1[2] == RBRACK && quoted == 0)
	{
	  if (contains_dollar_at)
	    *contains_dollar_at = 1;
	  return 1;
	}
    }
#endif
  return 0;
}

/* Parameter expand NAME, and return a new string which is the expansion,
   or NULL if there was no expansion.  NAME is as given in ${NAMEcWORD}.
   VAR_IS_SPECIAL is non-zero if NAME is one of the special variables in
   the shell, e.g., "@", "$", "*", etc.  QUOTED, if non-zero, means that
   NAME was found inside of a double-quoted expression. */
static WORD_DESC *
parameter_brace_expand_word (char *name, int var_is_special, int quoted, int pflags, array_eltstate_t *estatep)
{
  WORD_DESC *ret;
  char *temp, *tt;
  intmax_t arg_index;
  SHELL_VAR *var;
  int rflags;
  array_eltstate_t es;

  ret = 0;
  temp = 0;
  rflags = 0;

#if defined (ARRAY_VARS)
  if (estatep)
    es = *estatep;	/* structure copy */
  else
    {
      init_eltstate (&es);
      es.ind = INTMAX_MIN;
    }
#endif

  /* Handle multiple digit arguments, as in ${11}. */  
  if (legal_number (name, &arg_index))
    {
      tt = get_dollar_var_value (arg_index);
      if (tt)
 	temp = (*tt && (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)))
 		  ? quote_string (tt)
 		  : quote_escapes (tt);
      else
        temp = (char *)NULL;
      FREE (tt);
    }
  else if (var_is_special)      /* ${@} */
    {
      int sindex;
      tt = (char *)xmalloc (2 + strlen (name));
      tt[sindex = 0] = '$';
      strcpy (tt + 1, name);

      ret = param_expand (tt, &sindex, quoted, (int *)NULL, (int *)NULL,
			  (int *)NULL, (int *)NULL, pflags);

      /* Make sure we note that we saw a quoted null string and pass the flag back
	 to the caller in addition to the value. */
      if ((quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) && STR_DOLLAR_AT_STAR (name) &&
	  ret && ret->word && QUOTED_NULL (ret->word))
	ret->flags |= W_HASQUOTEDNULL;

      free (tt);
    }
#if defined (ARRAY_VARS)
  else if (valid_array_reference (name, 0))
    {
expand_arrayref:
      var = array_variable_part (name, 0, &tt, (int *)0);
      /* These are the cases where word splitting will not be performed */
      if (pflags & PF_ASSIGNRHS)
	{
	  if (ALL_ELEMENT_SUB (tt[0]) && tt[1] == RBRACK)
	    {
	      /* Only treat as double quoted if array variable */
	      if (var && (array_p (var) || assoc_p (var)))
		temp = array_value (name, quoted|Q_DOUBLE_QUOTES, AV_ASSIGNRHS, &es);
	      else		
		temp = array_value (name, quoted, 0, &es);
	    }
	  else
	    temp = array_value (name, quoted, 0, &es);
	}
      /* Posix interp 888 */
      else if (pflags & PF_NOSPLIT2)
	{
	  /* Special cases, then general case, for each of A[@], A[*], A[n] */
#if defined (HANDLE_MULTIBYTE)
          if (tt[0] == '@' && tt[1] == RBRACK && var && quoted == 0 && ifs_is_set && ifs_is_null == 0 && ifs_firstc[0] != ' ')
#else
	  if (tt[0] == '@' && tt[1] == RBRACK && var && quoted == 0 && ifs_is_set && ifs_is_null == 0 && ifs_firstc != ' ')
#endif
	    temp = array_value (name, Q_DOUBLE_QUOTES, AV_ASSIGNRHS, &es);
	  else if (tt[0] == '@' && tt[1] == RBRACK)
	    temp = array_value (name, quoted, 0, &es);
	  else if (tt[0] == '*' && tt[1] == RBRACK && expand_no_split_dollar_star && ifs_is_null)
	    temp = array_value (name, Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT, 0, &es);
	  else if (tt[0] == '*' && tt[1] == RBRACK)
	    temp = array_value (name, quoted, 0, &es);
	  else
	    temp = array_value (name, quoted, 0, &es);
	}	  	  
      else if (tt[0] == '*' && tt[1] == RBRACK && expand_no_split_dollar_star && ifs_is_null)
	temp = array_value (name, Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT, 0, &es);
      else
	temp = array_value (name, quoted, 0, &es);
      if (es.subtype == 0 && temp)
	{
	  temp = (*temp && (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)))
		    ? quote_string (temp)
		    : quote_escapes (temp);
	  rflags |= W_ARRAYIND;
	}
      /* Note that array[*] and array[@] expanded to a quoted null string by
	 returning the W_HASQUOTEDNULL flag to the caller in addition to TEMP. */
      else if (es.subtype == 1 && temp && QUOTED_NULL (temp) && (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)))
	rflags |= W_HASQUOTEDNULL;
      else if (es.subtype == 2 && temp && QUOTED_NULL (temp) && (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)))
	rflags |= W_HASQUOTEDNULL;

      if (estatep)
	*estatep = es;	/* structure copy */
      else
	flush_eltstate (&es);
    }
#endif
  else if (var = find_variable (name))
    {
      if (var_isset (var) && invisible_p (var) == 0)
	{
#if defined (ARRAY_VARS)
	  /* We avoid a memory leak by saving TT as the memory allocated by
	     assoc_to_string or array_to_string and leaving it 0 otherwise,
	     then freeing TT after quoting temp. */
	  tt = (char *)NULL;
	  if ((pflags & PF_ALLINDS) && assoc_p (var))
	    tt = temp = assoc_empty (assoc_cell (var)) ? (char *)NULL : assoc_to_string (assoc_cell (var), " ", quoted);
	  else if ((pflags & PF_ALLINDS) && array_p (var))
	    tt = temp = array_empty (array_cell (var)) ? (char *)NULL : array_to_string (array_cell (var), " ", quoted);
	  else if (assoc_p (var))
	    temp = assoc_reference (assoc_cell (var), "0");
	  else if (array_p (var))
	    temp = array_reference (array_cell (var), 0);
	  else
	    temp = value_cell (var);
#else
	  temp = value_cell (var);
#endif

	  if (temp)
	    temp = (*temp && (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)))
		      ? quote_string (temp)
		      : ((pflags & PF_ASSIGNRHS) ? quote_rhs (temp)
						 : quote_escapes (temp));
	  FREE (tt);
	}
      else
	temp = (char *)NULL;
    }
  else if (var = find_variable_last_nameref (name, 0))
    {
      temp = nameref_cell (var);
#if defined (ARRAY_VARS)
      /* Handle expanding nameref whose value is x[n] */
      if (temp && *temp && valid_array_reference (temp, 0))
	{
	  name = temp;
	  goto expand_arrayref;
	}
      else
#endif
      /* y=2 ; typeset -n x=y; echo ${x} is not the same as echo ${2} in ksh */
      if (temp && *temp && legal_identifier (temp) == 0)
        {
	  set_exit_status (EXECUTION_FAILURE);
	  report_error (_("%s: invalid variable name for name reference"), temp);
	  temp = &expand_param_error;
        }
      else
	temp = (char *)NULL;
    }
  else
    temp = (char *)NULL;

  if (ret == 0)
    {
      ret = alloc_word_desc ();
      ret->word = temp;
      ret->flags |= rflags;
    }
  return ret;
}

static char *
parameter_brace_find_indir (char *name, int var_is_special, int quoted, int find_nameref)
{
  char *temp, *t;
  WORD_DESC *w;
  SHELL_VAR *v;
  int pflags, oldex;

  if (find_nameref && var_is_special == 0 && (v = find_variable_last_nameref (name, 0)) &&
      nameref_p (v) && (t = nameref_cell (v)) && *t)
    return (savestring (t));

  /* If var_is_special == 0, and name is not an array reference, this does
     more expansion than necessary.  It should really look up the variable's
     value and not try to expand it. */
  pflags = PF_IGNUNBOUND;
  /* Note that we're not going to be doing word splitting here */
  if (var_is_special)
    {
      pflags |= PF_ASSIGNRHS;	/* suppresses word splitting */
      oldex = expand_no_split_dollar_star;
      expand_no_split_dollar_star = 1;
    }
  w = parameter_brace_expand_word (name, var_is_special, quoted, pflags, 0);
  if (var_is_special)
    expand_no_split_dollar_star = oldex;

  t = w->word;
  /* Have to dequote here if necessary */
  if (t)
    {
      temp = ((quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) || var_is_special)
		? dequote_string (t)
		: dequote_escapes (t);
      free (t);
      t = temp;
    }
  dispose_word_desc (w);

  return t;
}
  
/* Expand an indirect reference to a variable: ${!NAME} expands to the
   value of the variable whose name is the value of NAME. */
static WORD_DESC *
parameter_brace_expand_indir (char *name, int var_is_special, int quoted, int pflags, int *quoted_dollar_atp, int *contains_dollar_at)
{
  char *t;
  WORD_DESC *w;
  SHELL_VAR *v;

  /* See if it's a nameref first, behave in ksh93-compatible fashion.
     There is at least one incompatibility: given ${!foo[0]} where foo=bar,
     bash performs an indirect lookup on foo[0] and expands the result;
     ksh93 expands bar[0].  We could do that here -- there are enough usable
     primitives to do that -- but do not at this point. */
  if (var_is_special == 0 && (v = find_variable_last_nameref (name, 0)))
    {
      if (nameref_p (v) && (t = nameref_cell (v)) && *t)
	{
	  w = alloc_word_desc ();
	  w->word = savestring (t);
	  w->flags = 0;
	  return w;
	}
    }

  /* An indirect reference to a positional parameter or a special parameter
     is ok.  Indirect references to array references, as explained above, are
     ok (currently).  Only references to unset variables are errors at this
     point. */
  if (legal_identifier (name) && v == 0)
    {
      report_error (_("%s: invalid indirect expansion"), name);
      w = alloc_word_desc ();
      w->word = &expand_param_error;
      w->flags = 0;
      return (w);
    }
      
  t = parameter_brace_find_indir (name, var_is_special, quoted, 0);

  chk_atstar (t, quoted, pflags, quoted_dollar_atp, contains_dollar_at);

#if defined (ARRAY_VARS)
  /* Array references to unset variables are also an error */
  if (t == 0 && valid_array_reference (name, 0))
    {
      v = array_variable_part (name, 0, (char **)0, (int *)0);
      if (v == 0)
	{
	  report_error (_("%s: invalid indirect expansion"), name);
	  w = alloc_word_desc ();
	  w->word = &expand_param_error;
	  w->flags = 0;
	  return (w);
	}
      else
        return (WORD_DESC *)NULL;      
    }
#endif

  if (t == 0)
    return (WORD_DESC *)NULL;

  if (valid_brace_expansion_word (t, SPECIAL_VAR (t, 0)) == 0)
    {
      report_error (_("%s: invalid variable name"), t);
      free (t);
      w = alloc_word_desc ();
      w->word = &expand_param_error;
      w->flags = 0;
      return (w);
    }
	
  w = parameter_brace_expand_word (t, SPECIAL_VAR(t, 0), quoted, pflags, 0);
  free (t);

  return w;
}

/* Expand the right side of a parameter expansion of the form ${NAMEcVALUE},
   depending on the value of C, the separating character.  C can be one of
   "-", "+", or "=".  QUOTED is true if the entire brace expression occurs
   between double quotes. */
static WORD_DESC *
parameter_brace_expand_rhs (char *name, char *value, int op, int quoted, int pflags, int *qdollaratp, int *hasdollarat)
{
  WORD_DESC *w;
  WORD_LIST *l, *tl;
  char *t, *t1, *temp, *vname, *newval;
  int l_hasdollat, sindex, arrayref;
  SHELL_VAR *v;
  array_eltstate_t es;

/*itrace("parameter_brace_expand_rhs: %s:%s pflags = %d", name, value, pflags);*/
  /* If the entire expression is between double quotes, we want to treat
     the value as a double-quoted string, with the exception that we strip
     embedded unescaped double quotes (for sh backwards compatibility). */
  if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && *value)
    {
      sindex = 0;
      temp = string_extract_double_quoted (value, &sindex, SX_STRIPDQ);
    }
  else
    temp = value;

  w = alloc_word_desc ();
  l_hasdollat = 0;
  l = *temp ? expand_string_for_rhs (temp, quoted, op, pflags, &l_hasdollat, (int *)NULL)
	    : (WORD_LIST *)0;
  if (hasdollarat)
    *hasdollarat = l_hasdollat || (l && l->next);
  if (temp != value)
    free (temp);

  /* list_string takes multiple CTLNULs and turns them into an empty word
     with W_SAWQUOTEDNULL set. Turn it back into a single CTLNUL for the
     rest of this function and the caller. */
  for (tl = l; tl; tl = tl->next)
    {
      if (tl->word && (tl->word->word == 0 || tl->word->word[0] == 0) &&
	    (tl->word->flags | W_SAWQUOTEDNULL))
	{
	  t = make_quoted_char ('\0');
	  FREE (tl->word->word);
	  tl->word->word = t;
	  tl->word->flags |= W_QUOTED|W_HASQUOTEDNULL;
	  tl->word->flags &= ~W_SAWQUOTEDNULL;
	}
    }

  if (l)
    {
      /* If l->next is not null, we know that TEMP contained "$@", since that
	 is the only expansion that creates more than one word. */
      if (qdollaratp && ((l_hasdollat && quoted) || l->next))
	{
/*itrace("parameter_brace_expand_rhs: %s:%s: l != NULL, set *qdollaratp", name, value);*/
	  *qdollaratp = 1;
	}

      /* The expansion of TEMP returned something.  We need to treat things
	  slightly differently if L_HASDOLLAT is non-zero.  If we have "$@",
	  the individual words have already been quoted.  We need to turn them
	  into a string with the words separated by the first character of
	  $IFS without any additional quoting, so string_list_dollar_at won't
	  do the right thing.  If IFS is null, we want "$@" to split into
	  separate arguments, not be concatenated, so we use string_list_internal
	  and mark the word to be split on spaces later.  We use
	  string_list_dollar_star for "$@" otherwise. */
      if (l->next && ifs_is_null)
	{
	  temp = string_list_internal (l, " ");
	  w->flags |= W_SPLITSPACE;
	}
      else if (l_hasdollat || l->next)
	temp = string_list_dollar_star (l, quoted, 0);
      else
	{
	  temp = string_list (l);
	  if (temp && (QUOTED_NULL (temp) == 0) && (l->word->flags & W_SAWQUOTEDNULL))
	    w->flags |= W_SAWQUOTEDNULL;	/* XXX */
	}

      /* If we have a quoted null result (QUOTED_NULL(temp)) and the word is
	 a quoted null (l->next == 0 && QUOTED_NULL(l->word->word)), the
	 flags indicate it (l->word->flags & W_HASQUOTEDNULL), and the
	 expansion is quoted (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
	 (which is more paranoia than anything else), we need to return the
	 quoted null string and set the flags to indicate it. */
      if (l->next == 0 && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && QUOTED_NULL (temp) && QUOTED_NULL (l->word->word) && (l->word->flags & W_HASQUOTEDNULL))
	{
	  w->flags |= W_HASQUOTEDNULL;
/*itrace("parameter_brace_expand_rhs (%s:%s): returning quoted null, turning off qdollaratp", name, value);*/
	  /* If we return a quoted null with L_HASDOLLARAT, we either have a
	     construct like "${@-$@}" or "${@-${@-$@}}" with no positional
	     parameters or a quoted expansion of "$@" with $1 == ''.  In either
	     case, we don't want to enable special handling of $@. */
	  if (qdollaratp && l_hasdollat)
	    *qdollaratp = 0;
	}
      dispose_words (l);
    }
  else if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && l_hasdollat)
    {
      /* Posix interp 221 changed the rules on this.  The idea is that
	 something like "$xxx$@" should expand the same as "${foo-$xxx$@}"
	 when foo and xxx are unset.  The problem is that it's not in any
	 way backwards compatible and few other shells do it.  We're eventually
	 going to try and split the difference (heh) a little bit here. */
      /* l_hasdollat == 1 means we saw a quoted dollar at.  */

      /* The brace expansion occurred between double quotes and there was
	 a $@ in TEMP.  It does not matter if the $@ is quoted, as long as
	 it does not expand to anything.  In this case, we want to return
	 a quoted empty string.  Posix interp 888 */
      temp = make_quoted_char ('\0');
      w->flags |= W_HASQUOTEDNULL;
/*itrace("parameter_brace_expand_rhs (%s:%s): returning quoted null", name, value);*/
    }
  else
    temp = (char *)NULL;

  if (op == '-' || op == '+')
    {
      w->word = temp;
      return w;
    }

  /* op == '=' */
  t1 = temp ? dequote_string (temp) : savestring ("");
  free (temp);

  /* bash-4.4/5.0 */
  vname = name;
  if (*name == '!' &&
      (legal_variable_starter ((unsigned char)name[1]) || DIGIT (name[1]) || VALID_INDIR_PARAM (name[1])))
    {
      vname = parameter_brace_find_indir (name + 1, SPECIAL_VAR (name, 1), quoted, 1);
      if (vname == 0 || *vname == 0)
	{
	  report_error (_("%s: invalid indirect expansion"), name);
	  free (vname);
	  free (t1);
	  dispose_word (w);
	  return &expand_wdesc_error;
	}
      if (legal_identifier (vname) == 0)
	{
	  report_error (_("%s: invalid variable name"), vname);
	  free (vname);
	  free (t1);
	  dispose_word (w);
	  return &expand_wdesc_error;
	}
    }
    
  arrayref = 0;
#if defined (ARRAY_VARS)
  if (valid_array_reference (vname, 0))
    {
      init_eltstate (&es);
      v = assign_array_element (vname, t1, ASS_ALLOWALLSUB, &es);
      arrayref = 1;
      newval = es.value;
    }
  else
#endif /* ARRAY_VARS */
  v = bind_variable (vname, t1, 0);

  if (v == 0 || readonly_p (v) || noassign_p (v))	/* expansion error  */
    {
      if ((v == 0 || readonly_p (v)) && interactive_shell == 0 && posixly_correct)
	{
	  last_command_exit_value = EXECUTION_FAILURE;
	  exp_jump_to_top_level (FORCE_EOF);
	}
      else
	{
	  if (vname != name)
	    free (vname);
	  last_command_exit_value = EX_BADUSAGE;
	  exp_jump_to_top_level (DISCARD);
	}
    }

  stupidly_hack_special_variables (vname);

  /* "In all cases, the final value of parameter shall be substituted." */
  if (shell_compatibility_level > 51)
    {
      FREE (t1);
#if defined (ARRAY_VARS)
      if (arrayref)
	{
	  t1 = newval;
	  flush_eltstate (&es);
	}
      else
        t1 = get_variable_value (v);
#else
      t1 = value_cell (v);
#endif
    }

  if (vname != name)
    free (vname);

  /* From Posix group discussion Feb-March 2010.  Issue 7 0000221 */

  /* If we are double-quoted or if we are not going to be performing word
     splitting, we want to quote the value we return appropriately, like
     the other expansions this function handles. */
  w->word = (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) ? quote_string (t1) : quote_escapes (t1);
  /* If we have something that's non-null, but not a quoted null string,
     and we're not going to be performing word splitting (we know we're not
     because the operator is `='), we can forget we saw a quoted null. */
  if (w->word && w->word[0] && QUOTED_NULL (w->word) == 0)
    w->flags &= ~W_SAWQUOTEDNULL;

  /* If we convert a null string into a quoted null, make sure the caller
     knows it. */
  if ((quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) && QUOTED_NULL (w->word))
    w->flags |= W_HASQUOTEDNULL;

  return w;
}

/* Deal with the right hand side of a ${name:?value} expansion in the case
   that NAME is null or not set.  If VALUE is non-null it is expanded and
   used as the error message to print, otherwise a standard message is
   printed. */
static void
parameter_brace_expand_error (char *name, char *value, int check_null)
{
  WORD_LIST *l;
  char *temp;

  set_exit_status (EXECUTION_FAILURE);	/* ensure it's non-zero */
  if (value && *value)
    {
      l = expand_string (value, 0);
      temp =  string_list (l);
      report_error ("%s: %s", name, temp ? temp : "");	/* XXX was value not "" */
      FREE (temp);
      dispose_words (l);
    }
  else if (check_null == 0)
    report_error (_("%s: parameter not set"), name);
  else
    report_error (_("%s: parameter null or not set"), name);

  /* Free the data we have allocated during this expansion, since we
     are about to longjmp out. */
  free (name);
  FREE (value);
}

/* Return 1 if NAME is something for which parameter_brace_expand_length is
   OK to do. */
static int
valid_length_expression (char *name)
{
  return (name[1] == '\0' ||					/* ${#} */
	  ((sh_syntaxtab[(unsigned char) name[1]] & CSPECVAR) && name[2] == '\0') ||  /* special param */
	  (DIGIT (name[1]) && all_digits (name + 1)) ||	/* ${#11} */
#if defined (ARRAY_VARS)
	  valid_array_reference (name + 1, 0) ||		/* ${#a[7]} */
#endif
	  legal_identifier (name + 1));				/* ${#PS1} */
}

/* Handle the parameter brace expansion that requires us to return the
   length of a parameter. */
static intmax_t
parameter_brace_expand_length (char *name)
{
  char *t, *newname;
  intmax_t number, arg_index;
  WORD_LIST *list;
  SHELL_VAR *var;

  var = (SHELL_VAR *)NULL;

  if (name[1] == '\0')			/* ${#} */
    number = number_of_args ();
  else if (DOLLAR_AT_STAR (name[1]) && name[2] == '\0')	/* ${#@}, ${#*} */
    number = number_of_args ();
  else if ((sh_syntaxtab[(unsigned char) name[1]] & CSPECVAR) && name[2] == '\0')
    {
      /* Take the lengths of some of the shell's special parameters. */
      switch (name[1])
	{
	case '-':
	  t = which_set_flags ();
	  break;
	case '?':
	  t = itos (last_command_exit_value);
	  break;
	case '$':
	  t = itos (dollar_dollar_pid);
	  break;
	case '!':
	  if (last_asynchronous_pid == NO_PID)
	    t = (char *)NULL;	/* XXX - error if set -u set? */
	  else
	    t = itos (last_asynchronous_pid);
	  break;
	case '#':
	  t = itos (number_of_args ());
	  break;
	}
      number = STRLEN (t);
      FREE (t);
    }
#if defined (ARRAY_VARS)
  else if (valid_array_reference (name + 1, 0))
    number = array_length_reference (name + 1);
#endif /* ARRAY_VARS */
  else
    {
      number = 0;

      if (legal_number (name + 1, &arg_index))		/* ${#1} */
	{
	  t = get_dollar_var_value (arg_index);
	  if (t == 0 && unbound_vars_is_error)
	    return INTMAX_MIN;
	  number = MB_STRLEN (t);
	  FREE (t);
	}
#if defined (ARRAY_VARS)
      else if ((var = find_variable (name + 1)) && (invisible_p (var) == 0) && (array_p (var) || assoc_p (var)))
	{
	  if (assoc_p (var))
	    t = assoc_reference (assoc_cell (var), "0");
	  else
	    t = array_reference (array_cell (var), 0);
	  if (t == 0 && unbound_vars_is_error)
	    return INTMAX_MIN;
	  number = MB_STRLEN (t);
	}
#endif
      /* Fast path for the common case of taking the length of a non-dynamic
	 scalar variable value. */
      else if ((var || (var = find_variable (name + 1))) &&
      		invisible_p (var) == 0 &&
		array_p (var) == 0 && assoc_p (var) == 0 &&
		var->dynamic_value == 0)
	number = value_cell (var) ? MB_STRLEN (value_cell (var)) : 0;
      else if (var == 0 && unbound_vars_is_error == 0)
	number = 0;
      else				/* ${#PS1} */
	{
	  newname = savestring (name);
	  newname[0] = '$';
	  list = expand_string (newname, Q_DOUBLE_QUOTES);
	  t = list ? string_list (list) : (char *)NULL;
	  free (newname);
	  if (list)
	    dispose_words (list);

	  number = t ? MB_STRLEN (t) : 0;
	  FREE (t);
	}
    }

  return (number);
}

/* Skip characters in SUBSTR until DELIM.  SUBSTR is an arithmetic expression,
   so we do some ad-hoc parsing of an arithmetic expression to find
   the first DELIM, instead of using strchr(3).  Two rules:
	1.  If the substring contains a `(', read until closing `)'.
	2.  If the substring contains a `?', read past one `:' for each `?'.
   The SD_ARITHEXP flag to skip_to_delim takes care of doing this.
*/

static char *
skiparith (char *substr, int delim)
{
  int i;
  char delims[2];

  delims[0] = delim;
  delims[1] = '\0';

  i = skip_to_delim (substr, 0, delims, SD_ARITHEXP);
  return (substr + i);
}

/* Verify and limit the start and end of the desired substring.  If
   VTYPE == 0, a regular shell variable is being used; if it is 1,
   then the positional parameters are being used; if it is 2, then
   VALUE is really a pointer to an array variable that should be used.
   Return value is 1 if both values were OK, 0 if there was a problem
   with an invalid expression, or -1 if the values were out of range. */
static int
verify_substring_values (SHELL_VAR *v, char *value, char *substr, int vtype, intmax_t *e1p, intmax_t *e2p)
{
  char *t, *temp1, *temp2;
  arrayind_t len;
  int expok, eflag;
#if defined (ARRAY_VARS)
 ARRAY *a;
 HASH_TABLE *h;
#endif

  /* duplicate behavior of strchr(3) */
  t = skiparith (substr, ':');
  if (*t && *t == ':')
    *t = '\0';
  else
    t = (char *)0;

  temp1 = expand_arith_string (substr, Q_DOUBLE_QUOTES|Q_ARITH);
  eflag = (shell_compatibility_level > 51) ? 0 : EXP_EXPANDED;

  *e1p = evalexp (temp1, eflag, &expok);
  free (temp1);
  if (expok == 0)
    return (0);

  len = -1;	/* paranoia */
  switch (vtype)
    {
    case VT_VARIABLE:
    case VT_ARRAYMEMBER:
      len = MB_STRLEN (value);
      break;
    case VT_POSPARMS:
      len = number_of_args () + 1;
      if (*e1p == 0)
	len++;		/* add one arg if counting from $0 */
      break;
#if defined (ARRAY_VARS)
    case VT_ARRAYVAR:
      /* For arrays, the first value deals with array indices.  Negative
	 offsets count from one past the array's maximum index.  Associative
	 arrays treat the number of elements as the maximum index. */
      if (assoc_p (v))
	{
	  h = assoc_cell (v);
	  len = assoc_num_elements (h) + (*e1p < 0);
	}
      else
	{
	  a = (ARRAY *)value;
	  len = array_max_index (a) + (*e1p < 0);	/* arrays index from 0 to n - 1 */
	}
      break;
#endif
    }

  if (len == -1)	/* paranoia */
    return -1;

  if (*e1p < 0)		/* negative offsets count from end */
    *e1p += len;

  if (*e1p > len || *e1p < 0)
    return (-1);

#if defined (ARRAY_VARS)
  /* For arrays, the second offset deals with the number of elements. */
  if (vtype == VT_ARRAYVAR)
    len = assoc_p (v) ? assoc_num_elements (h) : array_num_elements (a);
#endif

  if (t)
    {
      t++;
      temp2 = savestring (t);
      temp1 = expand_arith_string (temp2, Q_DOUBLE_QUOTES|Q_ARITH);
      free (temp2);
      t[-1] = ':';
      *e2p = evalexp (temp1, eflag, &expok);
      free (temp1);
      if (expok == 0)
	return (0);

      /* Should we allow positional parameter length < 0 to count backwards
	 from end of positional parameters? */
#if 1
      if ((vtype == VT_ARRAYVAR || vtype == VT_POSPARMS) && *e2p < 0)
#else /* XXX - postponed; this isn't really a valuable feature */
      if (vtype == VT_ARRAYVAR && *e2p < 0)
#endif
	{
	  internal_error (_("%s: substring expression < 0"), t);
	  return (0);
	}
#if defined (ARRAY_VARS)
      /* In order to deal with sparse arrays, push the intelligence about how
	 to deal with the number of elements desired down to the array-
	 specific functions.  */
      if (vtype != VT_ARRAYVAR)
#endif
	{
	  if (*e2p < 0)
	    {
	      *e2p += len;
	      if (*e2p < 0 || *e2p < *e1p)
		{
		  internal_error (_("%s: substring expression < 0"), t);
		  return (0);
		}
	    }
	  else
	    *e2p += *e1p;		/* want E2 chars starting at E1 */
	  if (*e2p > len)
	    *e2p = len;
	}
    }
  else
    *e2p = len;

  return (1);
}

/* Return the type of variable specified by VARNAME (simple variable,
   positional param, or array variable).  Also return the value specified
   by VARNAME (value of a variable or a reference to an array element).
   QUOTED is the standard description of quoting state, using Q_* defines.
   FLAGS is currently a set of flags to pass to array_value.  If IND is
   not INTMAX_MIN, and FLAGS includes AV_USEIND, IND is
   passed to array_value so the array index is not computed again.
   If this returns VT_VARIABLE, the caller assumes that CTLESC and CTLNUL
   characters in the value are quoted with CTLESC and takes appropriate
   steps.  For convenience, *VALP is set to the dequoted VALUE. */
int
get_var_and_type (char *varname, char *value, array_eltstate_t *estatep, int quoted, int flags, SHELL_VAR **varp, char **valp)
{
  int vtype, want_indir;
  char *temp, *vname;
  SHELL_VAR *v;

  want_indir = *varname == '!' &&
    (legal_variable_starter ((unsigned char)varname[1]) || DIGIT (varname[1])
					|| VALID_INDIR_PARAM (varname[1]));
  if (want_indir)
    vname = parameter_brace_find_indir (varname+1, SPECIAL_VAR (varname, 1), quoted, 1);
    /* XXX - what if vname == 0 || *vname == 0 ? */
  else
    vname = varname;

  if (vname == 0)
    {
      vtype = VT_VARIABLE;
      *varp = (SHELL_VAR *)NULL;
      *valp = (char *)NULL;
      return (vtype);
    }

  /* This sets vtype to VT_VARIABLE or VT_POSPARMS */
  vtype = STR_DOLLAR_AT_STAR (vname);
  if (vtype == VT_POSPARMS && vname[0] == '*')
    vtype |= VT_STARSUB;
  *varp = (SHELL_VAR *)NULL;

#if defined (ARRAY_VARS)
  if (valid_array_reference (vname, 0))
    {
      v = array_variable_part (vname, 0, &temp, (int *)0);
      /* If we want to signal array_value to use an already-computed index,
	 the caller will set ESTATEP->IND to that index and pass AV_USEIND in
	 FLAGS. */
      if (estatep && (flags & AV_USEIND) == 0)
	estatep->ind = INTMAX_MIN;

      if (v && invisible_p (v))
	{
	  vtype = VT_ARRAYMEMBER;
	  *varp = (SHELL_VAR *)NULL;
	  *valp = (char *)NULL;
	}
      if (v && (array_p (v) || assoc_p (v)))
	{
	  if (ALL_ELEMENT_SUB (temp[0]) && temp[1] == RBRACK)
	    {
	      /* Callers have to differentiate between indexed and associative */
	      vtype = VT_ARRAYVAR;
	      if (temp[0] == '*')
		vtype |= VT_STARSUB;
	      *valp = array_p (v) ? (char *)array_cell (v) : (char *)assoc_cell (v);
	    }
	  else
	    {
	      vtype = VT_ARRAYMEMBER;
	      *valp = array_value (vname, Q_DOUBLE_QUOTES, flags, estatep);
	    }
	  *varp = v;
	}
      else if (v && (ALL_ELEMENT_SUB (temp[0]) && temp[1] == RBRACK))
	{
	  vtype = VT_VARIABLE;
	  *varp = v;
	  if (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT))
	    *valp = value ? dequote_string (value) : (char *)NULL;
	  else
	    *valp = value ? dequote_escapes (value) : (char *)NULL;
	}
      else
	{
	  vtype = VT_ARRAYMEMBER;
	  *varp = v;
	  *valp = array_value (vname, Q_DOUBLE_QUOTES, flags, estatep);
	}
    }
  else if ((v = find_variable (vname)) && (invisible_p (v) == 0) && (assoc_p (v) || array_p (v)))
    {
      vtype = VT_ARRAYMEMBER;
      *varp = v;
      *valp = assoc_p (v) ? assoc_reference (assoc_cell (v), "0") : array_reference (array_cell (v), 0);
    }
  else
#endif
    {
      if (value && vtype == VT_VARIABLE)
	{
	  *varp = find_variable (vname);
	  if (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT))
	    *valp = dequote_string (value);
	  else
	    *valp = dequote_escapes (value);
	}
      else
	*valp = value;
    }

  if (want_indir)
    free (vname);

  return vtype;
}

/***********************************************************/
/*						           */
/* Functions to perform transformations on variable values */
/*						           */
/***********************************************************/

static char *
string_var_assignment (SHELL_VAR *v, char *s)
{
  char flags[MAX_ATTRIBUTES], *ret, *val;
  int i;

  val = (v && (invisible_p (v) || var_isset (v) == 0)) ? (char *)NULL : sh_quote_reusable (s, 0);
  i = var_attribute_string (v, 0, flags);
  if (i == 0 && val == 0)
    return (char *)NULL;

  ret = (char *)xmalloc (i + STRLEN (val) + strlen (v->name) + 16 + MAX_ATTRIBUTES);
  if (i > 0 && val == 0)
    sprintf (ret, "declare -%s %s", flags, v->name);
  else if (i > 0)
    sprintf (ret, "declare -%s %s=%s", flags, v->name, val);
  else
    sprintf (ret, "%s=%s", v->name, val);
  free (val);
  return ret;
}

#if defined (ARRAY_VARS)
static char *
array_var_assignment (SHELL_VAR *v, int itype, int quoted, int atype)
{
  char *ret, *val, flags[MAX_ATTRIBUTES];
  int i;

  if (v == 0)
    return (char *)NULL;
  if (atype == 2)
    val = array_p (v) ? array_to_kvpair (array_cell (v), 0)
		      : assoc_to_kvpair (assoc_cell (v), 0);
  else
    val = array_p (v) ? array_to_assign (array_cell (v), 0)
		      : assoc_to_assign (assoc_cell (v), 0);

  if (val == 0 && (invisible_p (v) || var_isset (v) == 0))
    ;	/* placeholder */
  else if (val == 0)
    {
      val = (char *)xmalloc (3);
      val[0] = LPAREN;
      val[1] = RPAREN;
      val[2] = 0;
    }
  else
    {
      ret = (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) ? quote_string (val) : quote_escapes (val);
      free (val);
      val = ret;
    }

  if (atype == 2)
    return val;

  i = var_attribute_string (v, 0, flags);
  ret = (char *)xmalloc (i + STRLEN (val) + strlen (v->name) + 16);
  if (val)
    sprintf (ret, "declare -%s %s=%s", flags, v->name, val);
  else
    sprintf (ret, "declare -%s %s", flags, v->name);
  free (val);
  return ret;
}
#endif

static char *
pos_params_assignment (WORD_LIST *list, int itype, int quoted)
{
  char *temp, *ret;

  /* first, we transform the list to quote each word. */
  temp = list_transform ('Q', (SHELL_VAR *)0, list, itype, quoted);
  ret = (char *)xmalloc (strlen (temp) + 8);
  strcpy (ret, "set -- ");
  strcpy (ret + 7, temp);
  free (temp);
  return ret;
}

static char *
string_transform (int xc, SHELL_VAR *v, char *s)
{
  char *ret, flags[MAX_ATTRIBUTES], *t;
  int i;

  if (((xc == 'A' || xc == 'a') && v == 0))
    return (char *)NULL;
  else if (xc != 'a' && xc != 'A' && s == 0)
    return (char *)NULL;

  switch (xc)
    {
      /* Transformations that interrogate the variable */
      case 'a':
	i = var_attribute_string (v, 0, flags);
	ret = (i > 0) ? savestring (flags) : (char *)NULL;
	break;
      case 'A':
	ret = string_var_assignment (v, s);
	break;
      case 'K':
      case 'k':
	ret = sh_quote_reusable (s, 0);
	break;
      /* Transformations that modify the variable's value */
      case 'E':
	t = ansiexpand (s, 0, strlen (s), (int *)0);
	ret = dequote_escapes (t);
	free (t);
	break;
      case 'P':
	ret = decode_prompt_string (s);
	break;
      case 'Q':
	ret = sh_quote_reusable (s, 0);
	break;
      case 'U':
	ret = sh_modcase (s, 0, CASE_UPPER);
	break;
      case 'u':
	ret = sh_modcase (s, 0, CASE_UPFIRST);	/* capitalize */
 	break;
      case 'L':
 	ret = sh_modcase (s, 0, CASE_LOWER);
 	break;
      default:
	ret = (char *)NULL;
	break;
    }
  return ret;
}

static char *
list_transform (int xc, SHELL_VAR *v, WORD_LIST *list, int itype, int quoted)
{
  WORD_LIST *new, *l;
  WORD_DESC *w;
  char *tword;
  int qflags;

  for (new = (WORD_LIST *)NULL, l = list; l; l = l->next)
    {
      tword = string_transform (xc, v, l->word->word);
      w = alloc_word_desc ();
      w->word = tword ? tword : savestring ("");	/* XXX */
      new = make_word_list (w, new);
    }
  l = REVERSE_LIST (new, WORD_LIST *);

  qflags = quoted;
  /* If we are expanding in a context where word splitting will not be
     performed, treat as quoted.  This changes how $* will be expanded. */
  if (itype == '*' && expand_no_split_dollar_star && ifs_is_null)
    qflags |= Q_DOUBLE_QUOTES;		/* Posix interp 888 */

  tword = string_list_pos_params (itype, l, qflags, 0);
  dispose_words (l);

  return (tword);
}

static char *
parameter_list_transform (int xc, int itype, int quoted)
{
  char *ret;
  WORD_LIST *list;

  list = list_rest_of_args ();
  if (list == 0)
    return ((char *)NULL);
  if (xc == 'A')
    ret = pos_params_assignment (list, itype, quoted);
  else
    ret = list_transform (xc, (SHELL_VAR *)0, list, itype, quoted);
  dispose_words (list);
  return (ret);
}

#if defined (ARRAY_VARS)
static char *
array_transform (int xc, SHELL_VAR *var, int starsub, int quoted)
{
  ARRAY *a;
  HASH_TABLE *h;
  int itype, qflags;
  char *ret;
  WORD_LIST *list;
  SHELL_VAR *v;

  v = var;	/* XXX - for now */

  itype = starsub ? '*' : '@';

  if (xc == 'A')
    return (array_var_assignment (v, itype, quoted, 1));
  else if (xc == 'K')
    return (array_var_assignment (v, itype, quoted, 2));

  /* special case for unset arrays and attributes */
  if (xc == 'a' && (invisible_p (v) || var_isset (v) == 0))
    {
      char flags[MAX_ATTRIBUTES];
      int i;

      i = var_attribute_string (v, 0, flags);
      return ((i > 0) ? savestring (flags) : (char *)NULL);
    }

  a = (v && array_p (v)) ? array_cell (v) : 0;
  h = (v && assoc_p (v)) ? assoc_cell (v) : 0;

  /* XXX - for now */
  if (xc == 'k')
    {
      if (v == 0)
	return ((char *)NULL);
      list = array_p (v) ? array_to_kvpair_list (a) : assoc_to_kvpair_list (h);
      qflags = quoted;
      /* If we are expanding in a context where word splitting will not be
	 performed, treat as quoted.  This changes how $* will be expanded. */
      if (itype == '*' && expand_no_split_dollar_star && ifs_is_null)
	qflags |= Q_DOUBLE_QUOTES;		/* Posix interp 888 */

      ret = string_list_pos_params (itype, list, qflags, 0);
      dispose_words (list);
      return ret;
    }

  list = a ? array_to_word_list (a) : (h ? assoc_to_word_list (h) : 0);
  if (list == 0)
   return ((char *)NULL);
  ret = list_transform (xc, v, list, itype, quoted);
  dispose_words (list);

  return ret;
}
#endif /* ARRAY_VARS */

static int
valid_parameter_transform (char *xform)
{
  if (xform[1])
    return 0;

  /* check for valid values of xform[0] */
  switch (xform[0])
    {
    case 'a':		/* expand to a string with just attributes */
    case 'A':		/* expand as an assignment statement with attributes */
    case 'K':		/* expand assoc array to list of key/value pairs */
    case 'k':		/* XXX - for now */
    case 'E':		/* expand like $'...' */
    case 'P':		/* expand like prompt string */
    case 'Q':		/* quote reusably */
    case 'U':		/* transform to uppercase */
    case 'u':		/* transform by capitalizing */
    case 'L':		/* transform to lowercase */
      return 1;
    default:
      return 0;
    }
}
      
static char *
parameter_brace_transform (char *varname, char *value, array_eltstate_t *estatep, char *xform, int rtype, int quoted, int pflags, int flags)
{
  int vtype, xc, starsub;
  char *temp1, *val, *oname;
  SHELL_VAR *v;

  xc = xform[0];
  if (value == 0 && xc != 'A' && xc != 'a')
    return ((char *)NULL);

  oname = this_command_name;
  this_command_name = varname;

  vtype = get_var_and_type (varname, value, estatep, quoted, flags, &v, &val);
  if (vtype == -1)
    {
      this_command_name = oname;
      return ((char *)NULL);
    }

  if (xform[0] == 0 || valid_parameter_transform (xform) == 0)
    {
      this_command_name = oname;
      if (vtype == VT_VARIABLE)
	FREE (val);
      return (interactive_shell ? &expand_param_error : &expand_param_fatal);
    }

  starsub = vtype & VT_STARSUB;
  vtype &= ~VT_STARSUB;

  /* If we are asked to display the attributes of an unset variable, V will
     be NULL after the call to get_var_and_type. Double-check here. */
  if ((xc == 'a' || xc == 'A') && vtype == VT_VARIABLE && varname && v == 0)
    v = find_variable (varname);

  temp1 = (char *)NULL;		/* shut up gcc */
  switch (vtype)
    {
    case VT_VARIABLE:
    case VT_ARRAYMEMBER:
      temp1 = string_transform (xc, v, val);
      if (vtype == VT_VARIABLE)
	FREE (val);
      if (temp1)
	{
	  val = (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
			? quote_string (temp1)
			: quote_escapes (temp1);
	  free (temp1);
	  temp1 = val;
	}
      break;
#if defined (ARRAY_VARS)
    case VT_ARRAYVAR:
      temp1 = array_transform (xc, v, starsub, quoted);
      if (temp1 && quoted == 0 && ifs_is_null)
	{
		/* Posix interp 888 */
	}
      else if (temp1 && ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) == 0))
	{
	  val = quote_escapes (temp1);
	  free (temp1);
	  temp1 = val;
	}
      break;
#endif
    case VT_POSPARMS:
      temp1 = parameter_list_transform (xc, varname[0], quoted);
      if (temp1 && quoted == 0 && ifs_is_null)
	{
		/* Posix interp 888 */
	}
      else if (temp1 && ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) == 0))
	{
	  val = quote_escapes (temp1);
	  free (temp1);
	  temp1 = val;
	}
      break;
    }

  this_command_name = oname;
  return temp1;
}

/******************************************************/
/*						      */
/* Functions to extract substrings of variable values */
/*						      */
/******************************************************/

#if defined (HANDLE_MULTIBYTE)
/* Character-oriented rather than strictly byte-oriented substrings.  S and
   E, rather being strict indices into STRING, indicate character (possibly
   multibyte character) positions that require calculation.
   Used by the ${param:offset[:length]} expansion. */
static char *
mb_substring (char *string, int s, int e)
{
  char *tt;
  int start, stop, i;
  size_t slen;
  DECLARE_MBSTATE;

  start = 0;
  /* Don't need string length in ADVANCE_CHAR unless multibyte chars possible. */
  slen = (MB_CUR_MAX > 1) ? STRLEN (string) : 0;

  i = s;
  while (string[start] && i--)
    ADVANCE_CHAR (string, slen, start);
  stop = start;
  i = e - s;
  while (string[stop] && i--)
    ADVANCE_CHAR (string, slen, stop);
  tt = substring (string, start, stop);
  return tt;
}
#endif
  
/* Process a variable substring expansion: ${name:e1[:e2]}.  If VARNAME
   is `@', use the positional parameters; otherwise, use the value of
   VARNAME.  If VARNAME is an array variable, use the array elements. */

static char *
parameter_brace_substring (char *varname, char *value, array_eltstate_t *estatep, char *substr, int quoted, int pflags, int flags)
{
  intmax_t e1, e2;
  int vtype, r, starsub;
  char *temp, *val, *tt, *oname;
  SHELL_VAR *v;

  if (value == 0 && ((varname[0] != '@' && varname[0] != '*') || varname[1]))
    return ((char *)NULL);

  oname = this_command_name;
  this_command_name = varname;

  vtype = get_var_and_type (varname, value, estatep, quoted, flags, &v, &val);
  if (vtype == -1)
    {
      this_command_name = oname;
      return ((char *)NULL);
    }

  starsub = vtype & VT_STARSUB;
  vtype &= ~VT_STARSUB;

  r = verify_substring_values (v, val, substr, vtype, &e1, &e2);
  this_command_name = oname;
  if (r <= 0)
    {
      if (vtype == VT_VARIABLE)
	FREE (val);
      return ((r == 0) ? &expand_param_error : (char *)NULL);
    }

  switch (vtype)
    {
    case VT_VARIABLE:
    case VT_ARRAYMEMBER:
#if defined (HANDLE_MULTIBYTE)
      if (MB_CUR_MAX > 1)
	tt = mb_substring (val, e1, e2);
      else
#endif
      tt = substring (val, e1, e2);

      if (vtype == VT_VARIABLE)
	FREE (val);
      if (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT))
	temp = quote_string (tt);
      else
	temp = tt ? quote_escapes (tt) : (char *)NULL;
      FREE (tt);
      break;
    case VT_POSPARMS:
    case VT_ARRAYVAR:
      if (vtype == VT_POSPARMS)
	tt = pos_params (varname, e1, e2, quoted, pflags);
#if defined (ARRAY_VARS)
        /* assoc_subrange and array_subrange both call string_list_pos_params,
	   so we can treat this case just like VT_POSPARAMS. */
      else if (assoc_p (v))
	/* we convert to list and take first e2 elements starting at e1th
	   element -- officially undefined for now */	
	tt = assoc_subrange (assoc_cell (v), e1, e2, starsub, quoted, pflags);
      else
	/* We want E2 to be the number of elements desired (arrays can be
	   sparse, so verify_substring_values just returns the numbers
	   specified and we rely on array_subrange to understand how to
	   deal with them). */
	tt = array_subrange (array_cell (v), e1, e2, starsub, quoted, pflags);
#endif
      /* We want to leave this alone in every case where pos_params/
	 string_list_pos_params quotes the list members */
      if (tt && quoted == 0 && ifs_is_null)
	{
	  temp = tt;	/* Posix interp 888 */
	}
      else if (tt && quoted == 0 && (pflags & PF_ASSIGNRHS))
	{
	  temp = tt;	/* Posix interp 888 */
	}
      else if ((quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) == 0)
	{
	  temp = tt ? quote_escapes (tt) : (char *)NULL;
	  FREE (tt);
	}
      else
	temp = tt;
      break;

    default:
      temp = (char *)NULL;
    }

  return temp;
}

/****************************************************************/
/*								*/
/*   Functions to perform case modification on variable values  */
/*								*/
/****************************************************************/

/* Do case modification on the positional parameters. */

static char *
pos_params_modcase (char *string, char *pat, int modop, int mflags)
{
  WORD_LIST *save, *params;
  WORD_DESC *w;
  char *ret;
  int pchar, qflags, pflags;

  save = params = list_rest_of_args ();
  if (save == 0)
    return ((char *)NULL);

  for ( ; params; params = params->next)
    {
      ret = sh_modcase (params->word->word, pat, modop);
      w = alloc_word_desc ();
      w->word = ret ? ret : savestring ("");
      dispose_word (params->word);
      params->word = w;
    }

  pchar = (mflags & MATCH_STARSUB) == MATCH_STARSUB ? '*' : '@';
  qflags = (mflags & MATCH_QUOTED) == MATCH_QUOTED ? Q_DOUBLE_QUOTES : 0;
  pflags = (mflags & MATCH_ASSIGNRHS) == MATCH_ASSIGNRHS ? PF_ASSIGNRHS : 0;

  /* If we are expanding in a context where word splitting will not be
     performed, treat as quoted.  This changes how $* will be expanded. */
  if (pchar == '*' && (mflags & MATCH_ASSIGNRHS) && ifs_is_null)
    qflags |= Q_DOUBLE_QUOTES;		/* Posix interp 888 */

  ret = string_list_pos_params (pchar, save, qflags, pflags);
  dispose_words (save);

  return (ret);
}

/* Perform case modification on VALUE, which is the expansion of
   VARNAME.  MODSPEC is an expression supplying the type of modification
   to perform.  QUOTED is a flags word containing the type of quoting
   currently in effect. */
static char *
parameter_brace_casemod (char *varname, char *value, array_eltstate_t *estatep, int modspec, char *patspec, int quoted, int pflags, int flags)
{
  int vtype, starsub, modop, mflags, x;
  char *val, *temp, *pat, *p, *lpat, *tt, *oname;
  SHELL_VAR *v;

  if (value == 0)
    return ((char *)NULL);

  oname = this_command_name;
  this_command_name = varname;

  vtype = get_var_and_type (varname, value, estatep, quoted, flags, &v, &val);
  if (vtype == -1)
    {
      this_command_name = oname;
      return ((char *)NULL);
    }

  starsub = vtype & VT_STARSUB;
  vtype &= ~VT_STARSUB;

  modop = 0;
  mflags = 0;
  if (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
    mflags |= MATCH_QUOTED;
  if (starsub)
    mflags |= MATCH_STARSUB;
  if (pflags & PF_ASSIGNRHS)
    mflags |= MATCH_ASSIGNRHS;
  
  p = patspec;
  if (modspec == '^')
    {
      x = p && p[0] == modspec;
      modop = x ? CASE_UPPER : CASE_UPFIRST;
      p += x;
    }
  else if (modspec == ',')
    {
      x = p && p[0] == modspec;
      modop = x ? CASE_LOWER : CASE_LOWFIRST;
      p += x;
    }
  else if (modspec == '~')
    {
      x = p && p[0] == modspec;
      modop = x ? CASE_TOGGLEALL : CASE_TOGGLE;
      p += x;
    }
    
  lpat = p ? savestring (p) : 0;
  /* Perform the same expansions on the pattern as performed by the
     pattern removal expansions. */
  pat = lpat ? getpattern (lpat, quoted, 1) : 0;

  /* OK, now we do the case modification. */
  switch (vtype)
    {
    case VT_VARIABLE:
    case VT_ARRAYMEMBER:
      temp = sh_modcase (val, pat, modop);
      if (vtype == VT_VARIABLE)
	FREE (val);
      if (temp)
	{
	  tt = (mflags & MATCH_QUOTED) ? quote_string (temp) : quote_escapes (temp);
	  free (temp);
	  temp = tt;
	}
      break;

    case VT_POSPARMS:
      temp = pos_params_modcase (val, pat, modop, mflags);
      if (temp && quoted == 0 && ifs_is_null)
	{
	  /* Posix interp 888 */
	}
      else if (temp && (mflags & MATCH_QUOTED) == 0)
	{
	  tt = quote_escapes (temp);
	  free (temp);
	  temp = tt;
	}
      break;

#if defined (ARRAY_VARS)
    case VT_ARRAYVAR:
      /* If we are expanding in a context where word splitting will not be
	 performed, treat as quoted.  This changes how ${A[*]} will be
	 expanded to make it identical to $*. */
      if ((mflags & MATCH_STARSUB) && (mflags & MATCH_ASSIGNRHS) && ifs_is_null)
	mflags |= MATCH_QUOTED;		/* Posix interp 888 */

      temp = assoc_p (v) ? assoc_modcase (assoc_cell (v), pat, modop, mflags)
			 : array_modcase (array_cell (v), pat, modop, mflags);

      if (temp && quoted == 0 && ifs_is_null)
	{
	  /* Posix interp 888 */
	}
      else if (temp && (mflags & MATCH_QUOTED) == 0)
	{
	  tt = quote_escapes (temp);
	  free (temp);
	  temp = tt;
	}

      break;
#endif
    }

  FREE (pat);
  free (lpat);

  this_command_name = oname;

  return temp;
}

/* Check for unbalanced parens in S, which is the contents of $(( ... )).  If
   any occur, this must be a nested command substitution, so return 0.
   Otherwise, return 1.  A valid arithmetic expression must always have a
   ( before a matching ), so any cases where there are more right parens
   means that this must not be an arithmetic expression, though the parser
   will not accept it without a balanced total number of parens. */
static int
chk_arithsub (const char *s, int len)
{
  int i, count;
  DECLARE_MBSTATE;

  i = count = 0;
  while (i < len)
    {
      if (s[i] == LPAREN)
	count++;
      else if (s[i] == RPAREN)
	{
	  count--;
	  if (count < 0)
	    return 0;
	}

      switch (s[i])
	{
	default:
	  ADVANCE_CHAR (s, len, i);
	  break;

	case '\\':
	  i++;
	  if (s[i])
	    ADVANCE_CHAR (s, len, i);
	  break;

	case '\'':
	  i = skip_single_quoted (s, len, ++i, 0);
	  break;

	case '"':
	  i = skip_double_quoted ((char *)s, len, ++i, 0);
	  break;
	}
    }

  return (count == 0);
}

/****************************************************************/
/*								*/
/*	Functions to perform parameter expansion on a string	*/
/*								*/
/****************************************************************/

/* ------------------------------------------------------------------ */
/* pbe_dispatch_operation -- dispatch the operation part of ${...}     */
/*   Handles substring, patsub, casemod, transforms, pattern removal, */
/*   and null/unset operators.  Returns a WORD_DESC * for early-return */
/*   cases.  When the result is the sentinel `&expand_param_error`,    */
/*   the caller should fall through to common cleanup code.  The       */
/*   helper updates *tempp, *retp, *tflagp, and *quotedp as needed.   */
/* ------------------------------------------------------------------ */
#define PBE_DISPATCH_FALLTHROUGH (&expand_param_error) /* reused sentinel */

static WORD_DESC *
pbe_dispatch_operation (char *string, char *name, char **tempp, char *value,
			array_eltstate_t *esp, int c, int *quotedp, int pflags,
			int *quoted_dollar_atp, int *contains_dollar_at,
			int want_substring, int want_patsub, int want_casemod,
			int modspec, int var_is_set, int var_is_null,
			int var_is_special, int check_nullness,
			int tflag_in, int *tflagp, WORD_DESC **retp)
{
  char *temp = *tempp;
  char *temp1;
  WORD_DESC *ret = *retp;
  int quoted = *quotedp;
  int tflag = tflag_in;

  /* If this is a substring spec, process it and add the result. */
  if (want_substring)
    {
      temp1 = parameter_brace_substring (name, temp, esp, value, quoted, pflags, (tflag & W_ARRAYIND) ? AV_USEIND : 0);
      FREE (value);
      FREE (temp);
#if defined (ARRAY_VARS)
      flush_eltstate (esp);
#endif

      if (temp1 == &expand_param_error || temp1 == &expand_param_fatal)
        {
          FREE (name);
	  return (temp1 == &expand_param_error ? &expand_wdesc_error : &expand_wdesc_fatal);
        }

      ret = alloc_word_desc ();
      ret->word = temp1;
      if (temp1 &&
          (quoted_dollar_atp == 0 || *quoted_dollar_atp == 0) &&
	  QUOTED_NULL (temp1) && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
	ret->flags |= W_QUOTED|W_HASQUOTEDNULL;
      else if (temp1 && (name[0] == '*' && name[1] == 0) && quoted == 0 &&
		(pflags & PF_ASSIGNRHS))
	ret->flags |= W_SPLITSPACE;	/* Posix interp 888 */
      else if (temp1 && (name[0] == '*' && name[1] == 0) && quoted == 0 && ifs_is_null)
	ret->flags |= W_SPLITSPACE;	/* Posix interp 888 */

      FREE (name);
      return ret;
    }
  else if (want_patsub)
    {
      temp1 = parameter_brace_patsub (name, temp, esp, value, quoted, pflags, (tflag & W_ARRAYIND) ? AV_USEIND : 0);
      FREE (value);
      FREE (temp);
#if defined (ARRAY_VARS)
      flush_eltstate (esp);
#endif

      if (temp1 == &expand_param_error || temp1 == &expand_param_fatal)
        {
          FREE (name);
	  return (temp1 == &expand_param_error ? &expand_wdesc_error : &expand_wdesc_fatal);
        }

      ret = alloc_word_desc ();
      ret->word = temp1;
      if (temp1 &&
          (quoted_dollar_atp == 0 || *quoted_dollar_atp == 0) &&
	  QUOTED_NULL (temp1) && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
	ret->flags |= W_QUOTED|W_HASQUOTEDNULL;
      else if (temp1 && (name[0] == '*' && name[1] == 0) && quoted == 0 && ifs_is_null)
	ret->flags |= W_SPLITSPACE;	/* Posix interp 888 */

      FREE (name);
      return ret;
    }
#if defined (CASEMOD_EXPANSIONS)
  else if (want_casemod)
    {
      temp1 = parameter_brace_casemod (name, temp, esp, modspec, value, quoted, pflags, (tflag & W_ARRAYIND) ? AV_USEIND : 0);
      FREE (value);
      FREE (temp);
#if defined (ARRAY_VARS)
      flush_eltstate (esp);
#endif

      if (temp1 == &expand_param_error || temp1 == &expand_param_fatal)
        {
          FREE (name);
	  return (temp1 == &expand_param_error ? &expand_wdesc_error : &expand_wdesc_fatal);
        }

      ret = alloc_word_desc ();
      ret->word = temp1;
      if (temp1 &&
          (quoted_dollar_atp == 0 || *quoted_dollar_atp == 0) &&
	  QUOTED_NULL (temp1) && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
	ret->flags |= W_QUOTED|W_HASQUOTEDNULL;
      else if (temp1 && (name[0] == '*' && name[1] == 0) && quoted == 0 && ifs_is_null)
	ret->flags |= W_SPLITSPACE;	/* Posix interp 888 */

      FREE (name);
      return ret;
    }
#endif

  /* Do the right thing based on which character ended the variable name. */
  switch (c)
    {
    default:
    case '\0':
      set_exit_status (EXECUTION_FAILURE);
      report_error (_("%s: bad substitution"), string ? string : "??");
      FREE (value);
      FREE (temp);
      free (name);
#if defined (ARRAY_VARS)
      flush_eltstate (esp);
#endif
      if (shell_compatibility_level <= 43)
	return &expand_wdesc_error;
      else
	return ((posixly_correct && interactive_shell == 0) ? &expand_wdesc_fatal : &expand_wdesc_error);

    case RBRACE:
      break;

    case '@':
      temp1 = parameter_brace_transform (name, temp, esp, value, c, quoted, pflags, (tflag & W_ARRAYIND) ? AV_USEIND : 0);
      free (temp);
      free (value);
#if defined (ARRAY_VARS)
      flush_eltstate (esp);
#endif

      if (temp1 == &expand_param_error || temp1 == &expand_param_fatal)
	{
	  free (name);
	  set_exit_status (EXECUTION_FAILURE);
	  report_error (_("%s: bad substitution"), string ? string : "??");
	  return (temp1 == &expand_param_error ? &expand_wdesc_error : &expand_wdesc_fatal);
	}

      ret = alloc_word_desc ();
      ret->word = temp1;
      if (temp1 && QUOTED_NULL (temp1) && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
	ret->flags |= W_QUOTED|W_HASQUOTEDNULL;
      else if (temp1 && (name[0] == '*' && name[1] == 0) && quoted == 0 && ifs_is_null)
	ret->flags |= W_SPLITSPACE;	/* Posix interp 888 */

      free (name);
      return ret;

    case '#':	/* ${param#[#]pattern} */
    case '%':	/* ${param%[%]pattern} */
      if (value == 0 || *value == '\0' || temp == 0 || *temp == '\0')
	{
	  FREE (value);
	  break;
	}
      temp1 = parameter_brace_remove_pattern (name, temp, esp, value, c, quoted, (tflag & W_ARRAYIND) ? AV_USEIND : 0);
      free (temp);
      free (value);
#if defined (ARRAY_VARS)
      flush_eltstate (esp);
#endif

      ret = alloc_word_desc ();
      ret->word = temp1;
      if (temp1 && QUOTED_NULL (temp1) && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
	ret->flags |= W_QUOTED|W_HASQUOTEDNULL;
      else if (temp1 && (name[0] == '*' && name[1] == 0) && quoted == 0 && ifs_is_null)
	ret->flags |= W_SPLITSPACE;	/* Posix interp 888 */

      free (name);
      return ret;

    case '-':
    case '=':
    case '?':
    case '+':
      if (var_is_set && var_is_null == 0)
	{
	  /* If the operator is `+', we don't want the value of the named
	     variable for anything, just the value of the right hand side. */
	  if (c == '+')
	    {
	      /* XXX -- if we're double-quoted and the named variable is "$@",
			we want to turn off any special handling of "$@" --
			we're not using it, so whatever is on the rhs applies. */
	      if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && quoted_dollar_atp)
		*quoted_dollar_atp = 0;
	      if (contains_dollar_at)
		*contains_dollar_at = 0;

	      FREE (temp);
	      if (value)
		{
		  /* From Posix discussion on austin-group list.  Issue 221
		     requires that backslashes escaping `}' inside
		     double-quoted ${...} be removed. */
		  if (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
		    quoted |= Q_DOLBRACE;
		  ret = parameter_brace_expand_rhs (name, value, c,
						    quoted,
						    pflags,
						    quoted_dollar_atp,
						    contains_dollar_at);
		  /* XXX - fix up later, esp. noting presence of
			   W_HASQUOTEDNULL in ret->flags */
		  free (value);
		}
	      else
		temp = (char *)NULL;
	    }
	  else
	    {
	      FREE (value);
	    }
	  /* Otherwise do nothing; just use the value in TEMP. */
	}
      else	/* VAR not set or VAR is NULL. */
	{
	  /* If we're freeing a quoted null here, we need to remember we saw
	     it so we can restore it later if needed, or the caller can note it.
	     The check against `+' doesn't really matter, since the other cases
	     don't use or return TFLAG, but it's good for clarity. */
	  if (c == '+' && temp && QUOTED_NULL (temp) &&
	      (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)))
	    tflag |= W_HASQUOTEDNULL;

	  FREE (temp);
	  temp = (char *)NULL;
	  if (c == '=' && var_is_special)
	    {
	      set_exit_status (EXECUTION_FAILURE);
	      report_error (_("$%s: cannot assign in this way"), name);
	      free (name);
	      free (value);
#if defined (ARRAY_VARS)
	      flush_eltstate (esp);
#endif
	      return &expand_wdesc_error;
	    }
	  else if (c == '?')
	    {
	      parameter_brace_expand_error (name, value, check_nullness);
#if defined (ARRAY_VARS)
	      flush_eltstate (esp);
#endif
	      return (interactive_shell ? &expand_wdesc_error : &expand_wdesc_fatal);
	    }
	  else if (c != '+')
	    {
	      /* XXX -- if we're double-quoted and the named variable is "$@",
			we want to turn off any special handling of "$@" --
			we're not using it, so whatever is on the rhs applies. */
	      if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && quoted_dollar_atp)
		*quoted_dollar_atp = 0;
	      if (contains_dollar_at)
		*contains_dollar_at = 0;

	      /* From Posix discussion on austin-group list.  Issue 221 requires
		 that backslashes escaping `}' inside double-quoted ${...} be
		 removed. */
	      if (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
		quoted |= Q_DOLBRACE;
	      ret = parameter_brace_expand_rhs (name, value, c, quoted, pflags,
						quoted_dollar_atp,
						contains_dollar_at);
	      /* XXX - fix up later, esp. noting presence of
		       W_HASQUOTEDNULL in tdesc->flags */
	    }
	  free (value);
	}

      break;
    }

  /* Signal the caller to use the common cleanup path. */
  *tempp = temp;
  *retp = ret;
  *tflagp = tflag;
  *quotedp = quoted;
  return PBE_DISPATCH_FALLTHROUGH;
}

/* ${[#][!]name[[:][^[^]][,[,]]#[#]%[%]-=?+[word][:e1[:e2]]]} */
static WORD_DESC *
parameter_brace_expand (char *string, int *indexp, int quoted, int pflags, int *quoted_dollar_atp, int *contains_dollar_at)
{
  int check_nullness, var_is_set, var_is_null, var_is_special;
  int want_substring, want_indir, want_patsub, want_casemod, want_attributes;
  char *name, *value, *temp, *temp1;
  WORD_DESC *tdesc, *ret;
  int t_index, sindex, c, tflag, modspec, local_pflags, all_element_arrayref;
  intmax_t number;
  array_eltstate_t es;

  temp = temp1 = value = (char *)NULL;
  var_is_set = var_is_null = var_is_special = check_nullness = 0;
  want_substring = want_indir = want_patsub = want_casemod = want_attributes = 0;

  local_pflags = 0;
  all_element_arrayref = 0;

  sindex = *indexp;
  t_index = ++sindex;
  /* ${#var} doesn't have any of the other parameter expansions on it. */
  if (string[t_index] == '#' && legal_variable_starter (string[t_index+1]))		/* {{ */
    name = string_extract (string, &t_index, "}", SX_VARNAME);
  else
#if defined (CASEMOD_EXPANSIONS)
    /* To enable case-toggling expansions using the `~' operator character
       define CASEMOD_TOGGLECASE in config-top.h */
#  if defined (CASEMOD_TOGGLECASE)
    name = string_extract (string, &t_index, "#%^,~:-=?+/@}", SX_VARNAME);
#  else
    name = string_extract (string, &t_index, "#%^,:-=?+/@}", SX_VARNAME);
#  endif /* CASEMOD_TOGGLECASE */
#else
    name = string_extract (string, &t_index, "#%:-=?+/@}", SX_VARNAME);
#endif /* CASEMOD_EXPANSIONS */

  /* Handle ${@[stuff]} now that @ is a word expansion operator.  Not exactly
     the cleanest code ever. */
  if (*name == 0 && sindex == t_index && string[sindex] == '@')
    {
      name = (char *)xrealloc (name, 2);
      name[0] = '@';
      name[1] = '\0';
      t_index++;
    }
  else if (*name == '!' && t_index > sindex && string[t_index] == '@' && string[t_index+1] == RBRACE)
    {
      name = (char *)xrealloc (name, t_index - sindex + 2);
      name[t_index - sindex] = '@';
      name[t_index - sindex + 1] = '\0';
      t_index++;
    }

  ret = 0;
  tflag = 0;

#if defined (ARRAY_VARS)
  init_eltstate (&es);
#endif
  es.ind = INTMAX_MIN;	/* XXX */

  /* If the name really consists of a special variable, then make sure
     that we have the entire name.  We don't allow indirect references
     to special variables except `#', `?', `@' and `*'.  This clause is
     designed to handle ${#SPECIAL} and ${!SPECIAL}, not anything more
     general. */
  if ((sindex == t_index && VALID_SPECIAL_LENGTH_PARAM (string[t_index])) ||
      (sindex == t_index && string[sindex] == '#' && VALID_SPECIAL_LENGTH_PARAM (string[sindex + 1])) ||
      (sindex == t_index - 1 && string[sindex] == '!' && VALID_INDIR_PARAM (string[t_index])))
    {
      t_index++;
      temp1 = string_extract (string, &t_index, "#%:-=?+/@}", 0);
      name = (char *)xrealloc (name, 3 + (strlen (temp1)));
      *name = string[sindex];
      if (string[sindex] == '!')
	{
	  /* indirect reference of $#, $?, $@, or $* */
	  name[1] = string[sindex + 1];
	  strcpy (name + 2, temp1);
	}
      else	
	strcpy (name + 1, temp1);
      free (temp1);
    }
  sindex = t_index;

  /* Find out what character ended the variable name.  Then
     do the appropriate thing. */
  if (c = string[sindex])
    sindex++;

  /* If c is followed by one of the valid parameter expansion
     characters, move past it as normal.  If not, assume that
     a substring specification is being given, and do not move
     past it. */
  if (c == ':' && VALID_PARAM_EXPAND_CHAR (string[sindex]))
    {
      check_nullness++;
      if (c = string[sindex])
	sindex++;
    }
  else if (c == ':' && string[sindex] != RBRACE)
    want_substring = 1;
  else if (c == '/' /* && string[sindex] != RBRACE */)	/* XXX */
    want_patsub = 1;
#if defined (CASEMOD_EXPANSIONS)
  else if (c == '^' || c == ',' || c == '~')
    {
      modspec = c;
      want_casemod = 1;
    }
#endif
  else if (c == '@' && (string[sindex] == 'a' || string[sindex] == 'A') && string[sindex+1] == RBRACE)
    {
      /* special case because we do not want to shortcut foo as foo[0] here */
      want_attributes = 1;
      local_pflags |= PF_ALLINDS;
    }

  /* Catch the valid and invalid brace expressions that made it through the
     tests above. */
  /* ${#-} is a valid expansion and means to take the length of $-.
     Similarly for ${#?} and ${##}... */
  if (name[0] == '#' && name[1] == '\0' && check_nullness == 0 &&
	VALID_SPECIAL_LENGTH_PARAM (c) && string[sindex] == RBRACE)
    {
      name = (char *)xrealloc (name, 3);
      name[1] = c;
      name[2] = '\0';
      c = string[sindex++];
    }

  /* ...but ${#%}, ${#:}, ${#=}, ${#+}, and ${#/} are errors. */
  if (name[0] == '#' && name[1] == '\0' && check_nullness == 0 &&
	member (c, "%:=+/") && string[sindex] == RBRACE)
    {
      temp = (char *)NULL;
      goto bad_substitution;	/* XXX - substitution error */
    }

  /* Indirect expansion begins with a `!'.  A valid indirect expansion is
     either a variable name, one of the positional parameters or a special
     variable that expands to one of the positional parameters. */
  want_indir = *name == '!' &&
    (legal_variable_starter ((unsigned char)name[1]) || DIGIT (name[1])
					|| VALID_INDIR_PARAM (name[1]));

  /* Determine the value of this variable whose name is NAME. */

  /* Check for special variables, directly referenced. */
  if (SPECIAL_VAR (name, want_indir))
    var_is_special++;

  /* Check for special expansion things, like the length of a parameter */
  if (*name == '#' && name[1])
    {
      /* If we are not pointing at the character just after the
	 closing brace, then we haven't gotten all of the name.
	 Since it begins with a special character, this is a bad
	 substitution.  Also check NAME for validity before trying
	 to go on. */
      if (string[sindex - 1] != RBRACE || (valid_length_expression (name) == 0))
	{
	  temp = (char *)NULL;
	  goto bad_substitution;	/* substitution error */
	}

      number = parameter_brace_expand_length (name);
      if (number == INTMAX_MIN && unbound_vars_is_error)
	{
	  set_exit_status (EXECUTION_FAILURE);
	  err_unboundvar (name+1);
	  free (name);
	  return (interactive_shell ? &expand_wdesc_error : &expand_wdesc_fatal);
	}
      free (name);

      *indexp = sindex;
      if (number < 0)
        return (&expand_wdesc_error);
      else
	{
	  ret = alloc_word_desc ();
	  ret->word = itos (number);
	  return ret;
	}
    }

  /* ${@} is identical to $@. */
  if (name[0] == '@' && name[1] == '\0')
    {
      if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && quoted_dollar_atp)
	*quoted_dollar_atp = 1;

      if (contains_dollar_at)
	*contains_dollar_at = 1;

      tflag |= W_DOLLARAT;
    }

  /* Process ${!PREFIX*} expansion. */
  if (want_indir && string[sindex - 1] == RBRACE &&
      (string[sindex - 2] == '*' || string[sindex - 2] == '@') &&
      legal_variable_starter ((unsigned char) name[1]))
    {
      char **x;
      WORD_LIST *xlist;

      temp1 = savestring (name + 1);
      number = strlen (temp1);
      temp1[number - 1] = '\0';
      x = all_variables_matching_prefix (temp1);
      xlist = strvec_to_word_list (x, 0, 0);
      if (string[sindex - 2] == '*')
	temp = string_list_dollar_star (xlist, quoted, 0);
      else
	{
	  temp = string_list_dollar_at (xlist, quoted, 0);
	  if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && quoted_dollar_atp)
	    *quoted_dollar_atp = 1;
	  if (contains_dollar_at)
	    *contains_dollar_at = 1;

	  tflag |= W_DOLLARAT;
	}
      free (x);
      dispose_words (xlist);
      free (temp1);
      *indexp = sindex;

      free (name);

      ret = alloc_word_desc ();
      ret->word = temp;
      ret->flags = tflag;	/* XXX */
      return ret;
    }

#if defined (ARRAY_VARS)      
  /* Process ${!ARRAY[@]} and ${!ARRAY[*]} expansion. */
  if (want_indir && string[sindex - 1] == RBRACE &&
      string[sindex - 2] == RBRACK && valid_array_reference (name+1, 0))
    {
      char *x, *x1;

      temp1 = savestring (name + 1);
      x = array_variable_name (temp1, 0, &x1, (int *)0);
      FREE (x);
      if (ALL_ELEMENT_SUB (x1[0]) && x1[1] == RBRACK)
	{
	  temp = array_keys (temp1, quoted, pflags);	/* handles assoc vars too */
	  if (x1[0] == '@')
	    {
	      if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && quoted_dollar_atp)
		*quoted_dollar_atp = 1;
	      if (contains_dollar_at)
		*contains_dollar_at = 1;

	      tflag |= W_DOLLARAT;
	    }	    

	  free (name);
	  free (temp1);
	  *indexp = sindex;

	  ret = alloc_word_desc ();
	  ret->word = temp;
	  ret->flags = tflag;	/* XXX */
	  return ret;
	}

      free (temp1);
    }
#endif /* ARRAY_VARS */
      
  /* Make sure that NAME is valid before trying to go on. */
  if (valid_brace_expansion_word (want_indir ? name + 1 : name,
					var_is_special) == 0)
    {
      temp = (char *)NULL;
      goto bad_substitution;		/* substitution error */
    }

  if (want_indir)
    {
      tdesc = parameter_brace_expand_indir (name + 1, var_is_special, quoted, pflags|local_pflags, quoted_dollar_atp, contains_dollar_at);
      if (tdesc == &expand_wdesc_error || tdesc == &expand_wdesc_fatal)
	{
	  temp = (char *)NULL;
	  goto bad_substitution;
	}

      /* Turn off the W_ARRAYIND flag because there is no way for this function
	 to return the index we're supposed to be using. */
      if (tdesc && tdesc->flags)
	tdesc->flags &= ~W_ARRAYIND;

      /* If the indir expansion contains $@/$*, extend the special treatment
	 of the case of no positional parameters and `set -u' to it. */
      if (contains_dollar_at && *contains_dollar_at)
	all_element_arrayref = 1;
    }
  else
    {
      local_pflags |= PF_IGNUNBOUND|(pflags&(PF_NOSPLIT2|PF_ASSIGNRHS));
      tdesc = parameter_brace_expand_word (name, var_is_special, quoted, local_pflags, &es);
    }

  if (tdesc == &expand_wdesc_error || tdesc == &expand_wdesc_fatal)
    {
      tflag = 0;
      tdesc = 0;
    }

  if (tdesc)
    {
      temp = tdesc->word;
      tflag = tdesc->flags;
      dispose_word_desc (tdesc);
    }
  else
    temp = (char *)0;

  if (temp == &expand_param_error || temp == &expand_param_fatal)
    {
      FREE (name);
      FREE (value);
      return (temp == &expand_param_error ? &expand_wdesc_error : &expand_wdesc_fatal);
    }

#if defined (ARRAY_VARS)
  if (valid_array_reference (name, 0))
    {
      int qflags;
      char *t;

      qflags = quoted;
      /* If in a context where word splitting will not take place, treat as
	 if double-quoted.  Has effects with $* and ${array[*]} */

      if (pflags & PF_ASSIGNRHS)
	qflags |= Q_DOUBLE_QUOTES;
      /* We duplicate a little code here */
      t = mbschr (name, LBRACK);
      if (t && ALL_ELEMENT_SUB (t[1]) && t[2] == RBRACK)
	{
	  all_element_arrayref = 1;
	  if (expand_no_split_dollar_star && t[1] == '*')	/* XXX */
	    qflags |= Q_DOUBLE_QUOTES;
	}
      chk_atstar (name, qflags, pflags, quoted_dollar_atp, contains_dollar_at);
    }
#endif

  var_is_set = temp != (char *)0;
  var_is_null = check_nullness && (var_is_set == 0 || *temp == 0);
  /* XXX - this may not need to be restricted to special variables */
  if (check_nullness)
    var_is_null |= var_is_set && var_is_special && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && QUOTED_NULL (temp);
#if defined (ARRAY_VARS)
  if (check_nullness)
    var_is_null |= var_is_set && 
		   (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) &&
		   QUOTED_NULL (temp) &&
		   valid_array_reference (name, 0) &&
		   chk_atstar (name, 0, 0, (int *)0, (int *)0);
#endif

  /* Get the rest of the stuff inside the braces. */
  if (c && c != RBRACE)
    {
      /* Extract the contents of the ${ ... } expansion
	 according to the Posix.2 rules. */
      value = extract_dollar_brace_string (string, &sindex, quoted, (c == '%' || c == '#' || c =='/' || c == '^' || c == ',' || c ==':') ? SX_POSIXEXP|SX_WORD : SX_WORD);
      if (string[sindex] == RBRACE)
	sindex++;
      else
	goto bad_substitution;		/* substitution error */
    }
  else
    value = (char *)NULL;

  *indexp = sindex;

  /* All the cases where an expansion can possibly generate an unbound
     variable error. */
  if (want_substring || want_patsub || want_casemod || c == '@' || c == '#' || c == '%' || c == RBRACE)
    {
      if (var_is_set == 0 && unbound_vars_is_error && ((name[0] != '@' && name[0] != '*') || name[1]) && all_element_arrayref == 0)
	{
	  set_exit_status (EXECUTION_FAILURE);
	  err_unboundvar (name);
	  FREE (value);
	  FREE (temp);
	  free (name);
	  return (interactive_shell ? &expand_wdesc_error : &expand_wdesc_fatal);
	}
    }
    
  /* Dispatch the operation (substring, patsub, casemod, null/unset, etc.) */
  {
    WORD_DESC *dispatch_result;

    dispatch_result = pbe_dispatch_operation (string, name, &temp, value,
					     &es, c, &quoted, pflags,
					     quoted_dollar_atp, contains_dollar_at,
					     want_substring, want_patsub, want_casemod,
					     modspec, var_is_set, var_is_null,
					     var_is_special, check_nullness,
					     tflag, &tflag, &ret);
    if (dispatch_result != PBE_DISPATCH_FALLTHROUGH)
      return dispatch_result;
  }

  /* The bad_substitution label must remain here because it is the target
     of goto from extract_dollar_brace_string error handling above. */
  if (0)
    {
bad_substitution:
      set_exit_status (EXECUTION_FAILURE);
      report_error (_("%s: bad substitution"), string ? string : "??");
      FREE (value);
      FREE (temp);
      free (name);
#if defined (ARRAY_VARS)
      flush_eltstate (&es);
#endif
      if (shell_compatibility_level <= 43)
	return &expand_wdesc_error;
      else
	return ((posixly_correct && interactive_shell == 0) ? &expand_wdesc_fatal : &expand_wdesc_error);
    }

  free (name);
#if defined (ARRAY_VARS)
  flush_eltstate (&es);
#endif

  if (ret == 0)
    {
      ret = alloc_word_desc ();
      ret->flags = tflag;
      ret->word = temp;
    }
  return (ret);
}

/* Expand a single ${xxx} expansion.  The braces are optional.  When
   the braces are used, parameter_brace_expand() does the work,
   possibly calling param_expand recursively. */
static WORD_DESC *
param_expand (string, sindex, quoted, expanded_something,
	      contains_dollar_at, quoted_dollar_at_p, had_quoted_null_p,
	      pflags)
     char *string;
     int *sindex, quoted, *expanded_something, *contains_dollar_at;
     int *quoted_dollar_at_p, *had_quoted_null_p, pflags;
{
  char *temp, *temp1, uerror[3], *savecmd;
  int zindex, t_index, expok, eflag;
  unsigned char c;
  intmax_t number;
  SHELL_VAR *var;
  WORD_LIST *list, *l;
  WORD_DESC *tdesc, *ret;
  int tflag, nullarg;

/*itrace("param_expand: `%s' pflags = %d", string+*sindex, pflags);*/
  zindex = *sindex;
  c = string[++zindex];

  temp = (char *)NULL;
  ret = tdesc = (WORD_DESC *)NULL;
  tflag = 0;

  /* Do simple cases first. Switch on what follows '$'. */
  switch (c)
    {
    /* $0 .. $9? */
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
      temp1 = dollar_vars[TODIGIT (c)];
      /* This doesn't get called when (pflags&PF_IGNUNBOUND) != 0 */
      if (unbound_vars_is_error && temp1 == (char *)NULL)
	{
	  uerror[0] = '$';
	  uerror[1] = c;
	  uerror[2] = '\0';
	  set_exit_status (EXECUTION_FAILURE);
	  err_unboundvar (uerror);
	  return (interactive_shell ? &expand_wdesc_error : &expand_wdesc_fatal);
	}
      if (temp1)
	temp = (*temp1 && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
		  ? quote_string (temp1)
		  : quote_escapes (temp1);
      else
	temp = (char *)NULL;

      break;

    /* $$ -- pid of the invoking shell. */
    case '$':
      temp = itos (dollar_dollar_pid);
      break;

    /* $# -- number of positional parameters. */
    case '#':
      temp = itos (number_of_args ());
      break;

    /* $? -- return value of the last synchronous command. */
    case '?':
      temp = itos (last_command_exit_value);
      break;

    /* $- -- flags supplied to the shell on invocation or by `set'. */
    case '-':
      temp = which_set_flags ();
      break;

      /* $! -- Pid of the last asynchronous command. */
    case '!':
      /* If no asynchronous pids have been created, expand to nothing.
	 If `set -u' has been executed, and no async processes have
	 been created, this is an expansion error. */
      if (last_asynchronous_pid == NO_PID)
	{
	  if (expanded_something)
	    *expanded_something = 0;
	  temp = (char *)NULL;
	  if (unbound_vars_is_error && (pflags & PF_IGNUNBOUND) == 0)
	    {
	      uerror[0] = '$';
	      uerror[1] = c;
	      uerror[2] = '\0';
	      set_exit_status (EXECUTION_FAILURE);
	      err_unboundvar (uerror);
	      return (interactive_shell ? &expand_wdesc_error : &expand_wdesc_fatal);
	    }
	}
      else
	temp = itos (last_asynchronous_pid);
      break;

    /* The only difference between this and $@ is when the arg is quoted. */
    case '*':		/* `$*' */
      list = list_rest_of_args ();

#if 0
      /* According to austin-group posix proposal by Geoff Clare in
	 <20090505091501.GA10097@squonk.masqnet> of 5 May 2009:

 	"The shell shall write a message to standard error and
 	 immediately exit when it tries to expand an unset parameter
 	 other than the '@' and '*' special parameters."
      */

      if (list == 0 && unbound_vars_is_error && (pflags & PF_IGNUNBOUND) == 0)
	{
	  uerror[0] = '$';
	  uerror[1] = '*';
	  uerror[2] = '\0';
	  set_exit_status (EXECUTION_FAILURE);
	  err_unboundvar (uerror);
	  return (interactive_shell ? &expand_wdesc_error : &expand_wdesc_fatal);
	}
#endif

      /* If there are no command-line arguments, this should just
	 disappear if there are other characters in the expansion,
	 even if it's quoted. */
      if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && list == 0)
	temp = (char *)NULL;
      else if (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES|Q_PATQUOTE))
	{
	  /* If we have "$*" we want to make a string of the positional
	     parameters, separated by the first character of $IFS, and
	     quote the whole string, including the separators.  If IFS
	     is unset, the parameters are separated by ' '; if $IFS is
	     null, the parameters are concatenated. */
	  temp = (quoted & (Q_DOUBLE_QUOTES|Q_PATQUOTE)) ? string_list_dollar_star (list, quoted, 0) : string_list (list);
	  if (temp)
	    {
	      temp1 = (quoted & Q_DOUBLE_QUOTES) ? quote_string (temp) : temp;
	      if (*temp == 0)
		tflag |= W_HASQUOTEDNULL;
	      if (temp != temp1)
		free (temp);
	      temp = temp1;
	    }
	}
      else
	{
	  /* We check whether or not we're eventually going to split $* here,
	     for example when IFS is empty and we are processing the rhs of
	     an assignment statement.  In that case, we don't separate the
	     arguments at all.  Otherwise, if the $* is not quoted it is
	     identical to $@ */
	  if (expand_no_split_dollar_star && quoted == 0 && ifs_is_set == 0 && (pflags & PF_ASSIGNRHS))
	    {
	      /* Posix interp 888: RHS of assignment, IFS unset: no splitting,
		 separate with space */
	      temp1 = string_list_dollar_star (list, quoted, pflags);
	      temp = temp1 ? quote_string (temp1) : temp1;
	      /* XXX - tentative - note that we saw a quoted null here */
	      if (temp1 && *temp1 == 0 && QUOTED_NULL (temp))
		tflag |= W_SAWQUOTEDNULL;
	      FREE (temp1);
	    }
	  else if (expand_no_split_dollar_star && quoted == 0 && ifs_is_null && (pflags & PF_ASSIGNRHS))
	    {
	      /* Posix interp 888: RHS of assignment, IFS set to '' */
	      temp1 = string_list_dollar_star (list, quoted, pflags);
	      temp = temp1 ? quote_escapes (temp1) : temp1;
	      FREE (temp1);
	    }
	  else if (expand_no_split_dollar_star && quoted == 0 && ifs_is_set && ifs_is_null == 0 && (pflags & PF_ASSIGNRHS))
	    {
	      /* Posix interp 888: RHS of assignment, IFS set to non-null value */
	      temp1 = string_list_dollar_star (list, quoted, pflags);
	      temp = temp1 ? quote_string (temp1) : temp1;

	      /* XXX - tentative - note that we saw a quoted null here */
	      if (temp1 && *temp1 == 0 && QUOTED_NULL (temp))
		tflag |= W_SAWQUOTEDNULL;
	      FREE (temp1);
	    }
	  /* XXX - should we check ifs_is_set here as well? */
#  if defined (HANDLE_MULTIBYTE)
	  else if (expand_no_split_dollar_star && ifs_firstc[0] == 0)
#  else
	  else if (expand_no_split_dollar_star && ifs_firstc == 0)
#  endif
	    /* Posix interp 888: not RHS, no splitting, IFS set to '' */
	    temp = string_list_dollar_star (list, quoted, 0);
	  else
	    {
	      temp = string_list_dollar_at (list, quoted, 0);
	      /* Set W_SPLITSPACE to make sure the individual positional
		 parameters are split into separate arguments */
#if 0
	      if (quoted == 0 && (ifs_is_set == 0 || ifs_is_null))
#else	/* change with bash-5.0 */
	      if (quoted == 0 && ifs_is_null)
#endif
		tflag |= W_SPLITSPACE;
	      /* If we're not quoted but we still don't want word splitting, make
		 we quote the IFS characters to protect them from splitting (e.g.,
		 when $@ is in the string as well). */
	      else if (temp && quoted == 0 && ifs_is_set && (pflags & PF_ASSIGNRHS))
		{
		  temp1 = quote_string (temp);
		  free (temp);
		  temp = temp1;
		}
	    }

	  if (expand_no_split_dollar_star == 0 && contains_dollar_at)
	    *contains_dollar_at = 1;
	}

      dispose_words (list);
      break;

    /* When we have "$@" what we want is "$1" "$2" "$3" ... This
       means that we have to turn quoting off after we split into
       the individually quoted arguments so that the final split
       on the first character of $IFS is still done.  */
    case '@':		/* `$@' */
      list = list_rest_of_args ();

#if 0
      /* According to austin-group posix proposal by Geoff Clare in
	 <20090505091501.GA10097@squonk.masqnet> of 5 May 2009:

 	"The shell shall write a message to standard error and
 	 immediately exit when it tries to expand an unset parameter
 	 other than the '@' and '*' special parameters."
      */

      if (list == 0 && unbound_vars_is_error && (pflags & PF_IGNUNBOUND) == 0)
	{
	  uerror[0] = '$';
	  uerror[1] = '@';
	  uerror[2] = '\0';
	  set_exit_status (EXECUTION_FAILURE);
	  err_unboundvar (uerror);
	  return (interactive_shell ? &expand_wdesc_error : &expand_wdesc_fatal);
	}
#endif

      for (nullarg = 0, l = list; l; l = l->next)
	{
	  if (l->word && (l->word->word == 0 || l->word->word[0] == 0))
	    nullarg = 1;
	}

      /* We want to flag the fact that we saw this.  We can't turn
	 off quoting entirely, because other characters in the
	 string might need it (consider "\"$@\""), but we need some
	 way to signal that the final split on the first character
	 of $IFS should be done, even though QUOTED is 1. */
      /* XXX - should this test include Q_PATQUOTE? */
      if (quoted_dollar_at_p && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
	*quoted_dollar_at_p = 1;
      if (contains_dollar_at)
	*contains_dollar_at = 1;

      /* We want to separate the positional parameters with the first
	 character of $IFS in case $IFS is something other than a space.
	 We also want to make sure that splitting is done no matter what --
	 according to POSIX.2, this expands to a list of the positional
	 parameters no matter what IFS is set to. */
      /* XXX - what to do when in a context where word splitting is not
	 performed? Even when IFS is not the default, posix seems to imply
	 that we have to expand $@ to all the positional parameters and
	 separate them with spaces, which are preserved because word splitting
	 doesn't take place.  See below for how we use PF_NOSPLIT2 here. */

      /* These are the cases where word splitting will not be performed. */
      if (pflags & PF_ASSIGNRHS)
	{
	  temp = string_list_dollar_at (list, (quoted|Q_DOUBLE_QUOTES), pflags);
	  if (nullarg)
	    tflag |= W_HASQUOTEDNULL;	/* we know quoting produces quoted nulls */
	}

      /* This needs to match what expand_word_internal does with non-quoted $@
	 does with separating with spaces.  Passing Q_DOUBLE_QUOTES means that
	 the characters in LIST will be quoted, and PF_ASSIGNRHS ensures that
	 they will separated by spaces. After doing this, we need the special
	 handling for PF_NOSPLIT2 in expand_word_internal to remove the CTLESC
	 quotes. */
      else if (pflags & PF_NOSPLIT2)
        {
#if defined (HANDLE_MULTIBYTE)
	  if (quoted == 0 && ifs_is_set && ifs_is_null == 0 && ifs_firstc[0] != ' ')
#else
	  if (quoted == 0 && ifs_is_set && ifs_is_null == 0 && ifs_firstc != ' ')
#endif
	    /* Posix interp 888 */
	    temp = string_list_dollar_at (list, Q_DOUBLE_QUOTES, pflags);
	  else
	    temp = string_list_dollar_at (list, quoted, pflags);
	}
      else
	temp = string_list_dollar_at (list, quoted, pflags);

      tflag |= W_DOLLARAT;
      dispose_words (list);
      break;

    case LBRACE:
      tdesc = parameter_brace_expand (string, &zindex, quoted, pflags,
				      quoted_dollar_at_p,
				      contains_dollar_at);

      if (tdesc == &expand_wdesc_error || tdesc == &expand_wdesc_fatal)
	return (tdesc);
      temp = tdesc ? tdesc->word : (char *)0;

      /* XXX */
      /* Quoted nulls should be removed if there is anything else
	 in the string. */
      /* Note that we saw the quoted null so we can add one back at
	 the end of this function if there are no other characters
	 in the string, discard TEMP, and go on.  The exception to
	 this is when we have "${@}" and $1 is '', since $@ needs
	 special handling. */
      if (tdesc && tdesc->word && (tdesc->flags & W_HASQUOTEDNULL) && QUOTED_NULL (temp))
	{
	  if (had_quoted_null_p)
	    *had_quoted_null_p = 1;
	  if (*quoted_dollar_at_p == 0)
	    {
	      free (temp);
	      tdesc->word = temp = (char *)NULL;
	    }
	    
	}

      ret = tdesc;
      goto return0;

    /* Do command or arithmetic substitution. */
    case LPAREN:
      /* We have to extract the contents of this paren substitution. */
      t_index = zindex + 1;
      /* XXX - might want to check for string[t_index+2] == LPAREN and parse
	 as arithmetic substitution immediately. */
      temp = extract_command_subst (string, &t_index, (pflags&PF_COMPLETE) ? SX_COMPLETE : 0);
      zindex = t_index;

      /* For Posix.2-style `$(( ))' arithmetic substitution,
	 extract the expression and pass it to the evaluator. */
      if (temp && *temp == LPAREN)
	{
	  char *temp2;
	  temp1 = temp + 1;
	  temp2 = savestring (temp1);
	  t_index = strlen (temp2) - 1;

	  if (temp2[t_index] != RPAREN)
	    {
	      free (temp2);
	      goto comsub;
	    }

	  /* Cut off ending `)' */
	  temp2[t_index] = '\0';

	  if (chk_arithsub (temp2, t_index) == 0)
	    {
	      free (temp2);
#if 0
	      internal_warning (_("future versions of the shell will force evaluation as an arithmetic substitution"));
#endif
	      goto comsub;
	    }

	  /* Expand variables found inside the expression. */
	  temp1 = expand_arith_string (temp2, Q_DOUBLE_QUOTES|Q_ARITH);
	  free (temp2);

arithsub:
	  /* No error messages. */
	  savecmd = this_command_name;
	  this_command_name = (char *)NULL;

	  eflag = (shell_compatibility_level > 51) ? 0 : EXP_EXPANDED;
	  number = evalexp (temp1, eflag, &expok);
	  this_command_name = savecmd;
	  free (temp);
	  free (temp1);
	  if (expok == 0)
	    {
	      if (interactive_shell == 0 && posixly_correct)
		{
		  set_exit_status (EXECUTION_FAILURE);
		  return (&expand_wdesc_fatal);
		}
	      else
		return (&expand_wdesc_error);
	    }
	  temp = itos (number);
	  break;
	}

comsub:
      if (pflags & PF_NOCOMSUB)
	/* we need zindex+1 because string[zindex] == RPAREN */
	temp1 = substring (string, *sindex, zindex+1);
      else
	{
	  tdesc = command_substitute (temp, quoted, pflags&PF_ASSIGNRHS);
	  temp1 = tdesc ? tdesc->word : (char *)NULL;
	  if (tdesc)
	    dispose_word_desc (tdesc);
	}
      FREE (temp);
      temp = temp1;
      break;

    /* Do POSIX.2d9-style arithmetic substitution.  This will probably go
       away in a future bash release. */
    case '[':		/*]*/
      /* Extract the contents of this arithmetic substitution. */
      t_index = zindex + 1;
      temp = extract_arithmetic_subst (string, &t_index);
      zindex = t_index;
      if (temp == 0)
	{
	  temp = savestring (string);
	  if (expanded_something)
	    *expanded_something = 0;
	  goto return0;
	}	  

       /* Do initial variable expansion. */
      temp1 = expand_arith_string (temp, Q_DOUBLE_QUOTES|Q_ARITH);

      goto arithsub;

    default:
      /* Find the variable in VARIABLE_LIST. */
      temp = (char *)NULL;

      for (t_index = zindex; (c = string[zindex]) && legal_variable_char (c); zindex++)
	;
      temp1 = (zindex > t_index) ? substring (string, t_index, zindex) : (char *)NULL;

      /* If this isn't a variable name, then just output the `$'. */
      if (temp1 == 0 || *temp1 == '\0')
	{
	  FREE (temp1);
	  temp = (char *)xmalloc (2);
	  temp[0] = '$';
	  temp[1] = '\0';
	  if (expanded_something)
	    *expanded_something = 0;
	  goto return0;
	}

      /* If the variable exists, return its value cell. */
      var = find_variable (temp1);

      if (var && invisible_p (var) == 0 && var_isset (var))
	{
#if defined (ARRAY_VARS)
	  if (assoc_p (var) || array_p (var))
	    {
	      temp = array_p (var) ? array_reference (array_cell (var), 0)
				   : assoc_reference (assoc_cell (var), "0");
	      if (temp)
		temp = (*temp && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
			  ? quote_string (temp)
			  : quote_escapes (temp);
	      else if (unbound_vars_is_error)
		goto unbound_variable;
	    }
	  else
#endif
	    {
	      temp = value_cell (var);

	      temp = (*temp && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
			? quote_string (temp)
			: ((pflags & PF_ASSIGNRHS) ? quote_rhs (temp)
						   : quote_escapes (temp));
	    }

	  free (temp1);

	  goto return0;
	}
      else if (var && (invisible_p (var) || var_isset (var) == 0))
	temp = (char *)NULL;
      else if ((var = find_variable_last_nameref (temp1, 0)) && var_isset (var) && invisible_p (var) == 0)
	{
	  temp = nameref_cell (var);
#if defined (ARRAY_VARS)
	  if (temp && *temp && valid_array_reference (temp, 0))
	    {
	      chk_atstar (temp, quoted, pflags, quoted_dollar_at_p, contains_dollar_at);
	      tdesc = parameter_brace_expand_word (temp, SPECIAL_VAR (temp, 0), quoted, pflags, 0);
	      if (tdesc == &expand_wdesc_error || tdesc == &expand_wdesc_fatal)
		return (tdesc);
	      ret = tdesc;
	      goto return0;
	    }
	  else
#endif
	  /* y=2 ; typeset -n x=y; echo $x is not the same as echo $2 in ksh */
	  if (temp && *temp && legal_identifier (temp) == 0)
	    {
	      set_exit_status (EXECUTION_FAILURE);
	      report_error (_("%s: invalid variable name for name reference"), temp);
	      return (&expand_wdesc_error);	/* XXX */
	    }
	  else
	    temp = (char *)NULL;
	}

      temp = (char *)NULL;

unbound_variable:
      if (unbound_vars_is_error)
	{
	  set_exit_status (EXECUTION_FAILURE);
	  err_unboundvar (temp1);
	}
      else
	{
	  free (temp1);
	  goto return0;
	}

      free (temp1);
      set_exit_status (EXECUTION_FAILURE);
      return ((unbound_vars_is_error && interactive_shell == 0)
		? &expand_wdesc_fatal
		: &expand_wdesc_error);
    }

  if (string[zindex])
    zindex++;

return0:
  *sindex = zindex;

  if (ret == 0)
    {
      ret = alloc_word_desc ();
      ret->flags = tflag;	/* XXX */
      ret->word = temp;
    }
  return ret;
}

#if defined (ARRAY_VARS)
/* Characters that need to be backslash-quoted after expanding array subscripts */
static char abstab[256] = { '\1' };

/* Run an array subscript through the appropriate word expansions. */
char *
expand_subscript_string (char *string, int quoted)
{
  WORD_DESC td;
  WORD_LIST *tlist;
  int oe;
  char *ret;

  if (string == 0 || *string == 0)
    return (char *)NULL;

  oe = expand_no_split_dollar_star;
  ret = (char *)NULL;

  td.flags = W_NOPROCSUB|W_NOTILDE|W_NOSPLIT2;	/* XXX - W_NOCOMSUB? */
  td.word = savestring (string);		/* in case it's freed on error */

  expand_no_split_dollar_star = 1;
  tlist = call_expand_word_internal (&td, quoted, 0, (int *)NULL, (int *)NULL);
  expand_no_split_dollar_star = oe;

  if (tlist)
    {
      if (tlist->word)
	{
	  remove_quoted_nulls (tlist->word->word);
	  tlist->word->flags &= ~W_HASQUOTEDNULL;
	}
      dequote_list (tlist);
      ret = string_list (tlist);
      dispose_words (tlist);
    }

  free (td.word);
  return (ret);
}

/* Expand the subscript in STRING, which is an array reference. To ensure we
   only expand it once, we quote the characters that would start another
   expansion and the bracket characters that are special to array subscripts. */
static char *
expand_array_subscript (char *string, int *sindex, int quoted, int flags)
{
  char *ret, *exp, *t;
  size_t slen;
  int si, ni;

  si = *sindex;
  slen = STRLEN (string);

  if (abstab[0] == '\1')
    {
      /* These are basically the characters that start shell expansions plus
	 the characters that delimit subscripts. */
      memset (abstab, '\0', sizeof (abstab));
      abstab[LBRACK] = abstab[RBRACK] = 1;
      abstab['$'] = abstab['`'] = abstab['~'] = 1;
      abstab['\\'] = abstab['\''] = 1;
      abstab['"'] = 1;	/* XXX */
      /* We don't quote `@' or `*' in the subscript at all. */
    }

  /* string[si] == LBRACK */
  ni = skipsubscript (string, si, 0);
  /* These checks mirror the ones in valid_array_reference. The check for
     (ni - si) == 1 checks for empty subscripts. We don't check that the
     subscript is a separate word if we're parsing an arithmetic expression. */
  if (ni >= slen || string[ni] != RBRACK || (ni - si) == 1 ||
      (string[ni+1] != '\0' && (quoted & Q_ARITH) == 0))
    {
      /* let's check and see what fails this check */
      INTERNAL_DEBUG (("expand_array_subscript: bad subscript string: `%s'", string+si));
      ret = (char *)xmalloc (2);	/* badly-formed subscript */
      ret[0] = string[si];
      ret[1] = '\0';
      *sindex = si + 1;
      return ret;
    }

  /* STRING[ni] == RBRACK */
  exp = substring (string, si+1, ni);
  t = expand_subscript_string (exp, quoted & ~(Q_ARITH|Q_DOUBLE_QUOTES));
  free (exp);
  exp = t ? sh_backslash_quote (t, abstab, 0) : savestring ("");
  free (t);

  slen = STRLEN (exp);
  ret = xmalloc (slen + 2 + 1);
  ret[0] ='[';
  strcpy (ret + 1, exp);
  ret[slen + 1] = ']';
  ret[slen + 2] = '\0';

  free (exp);
  *sindex = ni + 1;

  return ret;
}
#endif

void
invalidate_cached_quoted_dollar_at ()
{
  dispose_words (cached_quoted_dollar_at);
  cached_quoted_dollar_at = 0;
}

/* Make a word list which is the result of parameter and variable
   expansion, command substitution, arithmetic substitution, and
   quote removal of WORD.  Return a pointer to a WORD_LIST which is
   the result of the expansion.  If WORD contains a null word, the
   word list returned is also null.

   QUOTED contains flag values defined in shell.h.

   ISEXP is used to tell expand_word_internal that the word should be
   treated as the result of an expansion.  This has implications for
   how IFS characters in the word are treated.

   CONTAINS_DOLLAR_AT and EXPANDED_SOMETHING are return values; when non-null
   they point to an integer value which receives information about expansion.
   CONTAINS_DOLLAR_AT gets non-zero if WORD contained "$@", else zero.
   EXPANDED_SOMETHING get non-zero if WORD contained any parameter expansions,
   else zero.

   This only does word splitting in the case of $@ expansion.  In that
   case, we split on ' '. */

/* ======================================================================
   Helper types and functions for expand_word_internal decomposition.
   These helpers extract major code blocks from the main function while
   preserving exact behavior.  Each helper operates on a shared context
   struct and returns an action enum that the caller maps to the
   appropriate goto label.
   ====================================================================== */

/* Return values from ewi_* helpers, mapped to goto labels in the caller. */
enum ewi_action {
  EWI_ADD_STRING,		/* goto add_string */
  EWI_ADD_CHARACTER,		/* goto add_character */
  EWI_ADD_QUOTED_STRING,	/* goto add_quoted_string */
  EWI_BREAK,			/* break from switch */
  EWI_CONTINUE,			/* continue the for loop */
  EWI_RETURN			/* early return -- result in ctx->list */
};

/* Shared mutable state for expand_word_internal and its helpers. */
struct ewi_context
{
  /* The intermediate string that we build while expanding. */
  char *istring;
  size_t istring_size;
  size_t istring_index;

  /* Temporary string storage. */
  char *temp;

  /* The text of the word being expanded and its size/index. */
  char *string;
  size_t string_size;
  int sindex;

  /* Current character. */
  unsigned char c;

  /* For calls to string_extract_xxx. */
  int t_index;

  /* State flags. */
  int quoted_dollar_at;
  int quoted_state;
  int had_quoted_null;
  int has_quoted_ifs;
  int has_dollar_at;
  int temp_has_dollar_at;
  int split_on_spaces;
  int local_expanded;
  int tflag;
  int pflags;

  /* Word list results. */
  WORD_LIST *list;
  WORD_DESC *tword;

  /* Function parameters (non-owned pointers). */
  WORD_DESC *word;
  int quoted;
  int *contains_dollar_at;
  int *expanded_something;
};

/* Populate an ewi_context from the local variables of expand_word_internal.
   This macro is used before calling any ewi_* helper function. */
#define EWI_CTX_SAVE(ctx) do { \
  (ctx).istring = istring; \
  (ctx).istring_size = istring_size; \
  (ctx).istring_index = istring_index; \
  (ctx).temp = temp; \
  (ctx).string = string; \
  (ctx).string_size = string_size; \
  (ctx).sindex = sindex; \
  (ctx).c = c; \
  (ctx).t_index = t_index; \
  (ctx).quoted_dollar_at = quoted_dollar_at; \
  (ctx).quoted_state = quoted_state; \
  (ctx).had_quoted_null = had_quoted_null; \
  (ctx).has_quoted_ifs = has_quoted_ifs; \
  (ctx).has_dollar_at = has_dollar_at; \
  (ctx).temp_has_dollar_at = temp_has_dollar_at; \
  (ctx).split_on_spaces = split_on_spaces; \
  (ctx).local_expanded = local_expanded; \
  (ctx).tflag = tflag; \
  (ctx).pflags = pflags; \
  (ctx).tword = tword; \
  (ctx).word = word; \
  (ctx).quoted = quoted; \
  (ctx).contains_dollar_at = contains_dollar_at; \
  (ctx).expanded_something = expanded_something; \
} while (0)

/* Restore local variables from an ewi_context after calling an ewi_* helper. */
#define EWI_CTX_RESTORE(ctx) do { \
  istring = (ctx).istring; \
  istring_size = (ctx).istring_size; \
  istring_index = (ctx).istring_index; \
  temp = (ctx).temp; \
  string = (ctx).string; \
  string_size = (ctx).string_size; \
  sindex = (ctx).sindex; \
  c = (ctx).c; \
  t_index = (ctx).t_index; \
  quoted_dollar_at = (ctx).quoted_dollar_at; \
  quoted_state = (ctx).quoted_state; \
  had_quoted_null = (ctx).had_quoted_null; \
  has_quoted_ifs = (ctx).has_quoted_ifs; \
  has_dollar_at = (ctx).has_dollar_at; \
  temp_has_dollar_at = (ctx).temp_has_dollar_at; \
  split_on_spaces = (ctx).split_on_spaces; \
  local_expanded = (ctx).local_expanded; \
  tflag = (ctx).tflag; \
  pflags = (ctx).pflags; \
  tword = (ctx).tword; \
} while (0)

/* ------------------------------------------------------------------ */
/* ewi_handle_dollar -- handle `case '$':` dispatch (param expansion) */
/* ------------------------------------------------------------------ */
static enum ewi_action
ewi_handle_dollar (struct ewi_context *ctx)
{
  if (ctx->expanded_something)
    *ctx->expanded_something = 1;
  ctx->local_expanded = 1;

  ctx->temp_has_dollar_at = 0;
  ctx->pflags = (ctx->word->flags & W_NOCOMSUB) ? PF_NOCOMSUB : 0;
  if (ctx->word->flags & W_NOSPLIT2)
    ctx->pflags |= PF_NOSPLIT2;
  if (ctx->word->flags & W_ASSIGNRHS)
    ctx->pflags |= PF_ASSIGNRHS;
  if (ctx->word->flags & W_COMPLETE)
    ctx->pflags |= PF_COMPLETE;

  ctx->tword = param_expand (ctx->string, &ctx->sindex, ctx->quoted,
			     ctx->expanded_something,
			     &ctx->temp_has_dollar_at,
			     &ctx->quoted_dollar_at,
			     &ctx->had_quoted_null, ctx->pflags);
  ctx->has_dollar_at += ctx->temp_has_dollar_at;
  ctx->split_on_spaces += (ctx->tword->flags & W_SPLITSPACE);

  if (ctx->tword == &expand_wdesc_error || ctx->tword == &expand_wdesc_fatal)
    {
      free (ctx->string);
      free (ctx->istring);
      ctx->list = ((ctx->tword == &expand_wdesc_error) ? &expand_word_error
						        : &expand_word_fatal);
      return EWI_RETURN;
    }
  if (ctx->contains_dollar_at && ctx->has_dollar_at)
    *ctx->contains_dollar_at = 1;

  if (ctx->tword && (ctx->tword->flags & W_HASQUOTEDNULL))
    ctx->had_quoted_null = 1;		/* note for later */
  if (ctx->tword && (ctx->tword->flags & W_SAWQUOTEDNULL))
    ctx->had_quoted_null = 1;		/* XXX */

  ctx->temp = ctx->tword ? ctx->tword->word : (char *)NULL;
  dispose_word_desc (ctx->tword);

  /* Kill quoted nulls; we will add them back at the end of
     expand_word_internal if nothing else in the string */
  if (ctx->had_quoted_null && ctx->temp && QUOTED_NULL (ctx->temp))
    {
      FREE (ctx->temp);
      ctx->temp = (char *)NULL;
    }

  return EWI_ADD_STRING;
}

/* ------------------------------------------------------------------ */
/* ewi_handle_double_quote -- handle `case '"':` (double-quote)       */
/* ------------------------------------------------------------------ */
static enum ewi_action
ewi_handle_double_quote (struct ewi_context *ctx)
{
  WORD_LIST *list;

  /* XXX - revisit this */
  if ((ctx->quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) && ((ctx->quoted & Q_ARITH) == 0))
    return EWI_ADD_CHARACTER;

  ctx->t_index = ++ctx->sindex;
  ctx->temp = string_extract_double_quoted (ctx->string, &ctx->sindex,
					    (ctx->word->flags & W_COMPLETE) ? SX_COMPLETE : 0);

  /* If the quotes surrounded the entire string, then the
     whole word was quoted. */
  ctx->quoted_state = (ctx->t_index == 1 && ctx->string[ctx->sindex] == '\0')
			  ? WHOLLY_QUOTED
			  : PARTIALLY_QUOTED;

  if (ctx->temp && *ctx->temp)
    {
      ctx->tword = alloc_word_desc ();
      ctx->tword->word = ctx->temp;

      if (ctx->word->flags & W_ASSIGNARG)
	ctx->tword->flags |= ctx->word->flags & (W_ASSIGNARG|W_ASSIGNRHS); /* affects $@ */
      if (ctx->word->flags & W_COMPLETE)
	ctx->tword->flags |= W_COMPLETE;	/* for command substitutions */
      if (ctx->word->flags & W_NOCOMSUB)
	ctx->tword->flags |= W_NOCOMSUB;
      if (ctx->word->flags & W_NOPROCSUB)
	ctx->tword->flags |= W_NOPROCSUB;

      if (ctx->word->flags & W_ASSIGNRHS)
	ctx->tword->flags |= W_ASSIGNRHS;

      ctx->temp = (char *)NULL;

      ctx->temp_has_dollar_at = 0;	/* does this quoted (sub)string include $@? */
      /* Need to get W_HASQUOTEDNULL flag through this function. */
      /* XXX - preserve Q_ARITH here? */
      list = expand_word_internal (ctx->tword, Q_DOUBLE_QUOTES|(ctx->quoted&Q_ARITH), 0, &ctx->temp_has_dollar_at, (int *)NULL);
      ctx->has_dollar_at += ctx->temp_has_dollar_at;

      if (list == &expand_word_error || list == &expand_word_fatal)
	{
	  free (ctx->istring);
	  free (ctx->string);
	  /* expand_word_internal has already freed temp_word->word
	     for us because of the way it prints error messages. */
	  ctx->tword->word = (char *)NULL;
	  dispose_word (ctx->tword);
	  ctx->list = list;
	  return EWI_RETURN;
	}

      dispose_word (ctx->tword);

      /* "$@" (a double-quoted dollar-at) expands into nothing,
	 not even a NULL word, when there are no positional
	 parameters.  Posix interp 888 says that other parts of the
	 word that expand to quoted nulls result in quoted nulls, so
	 we can't just throw the entire word away if we have "$@"
	 anywhere in it.  We use had_quoted_null to keep track */
      if (list == 0 && ctx->temp_has_dollar_at)	/* XXX - was has_dollar_at */
	{
	  ctx->quoted_dollar_at++;
	  return EWI_BREAK;
	}

      /* If this list comes back with a quoted null from expansion,
	 we have either "$x" or "$@" with $1 == ''. In either case,
	 we need to make sure we add a quoted null argument and
	 disable the special handling that "$@" gets. */
      if (list && list->word && list->next == 0 && (list->word->flags & W_HASQUOTEDNULL))
	{
	  if (ctx->had_quoted_null && ctx->temp_has_dollar_at)
	    ctx->quoted_dollar_at++;
	  ctx->had_quoted_null = 1;		/* XXX */
	}

      /* If we get "$@", we know we have expanded something, so we
	 need to remember it for the final split on $IFS.  This is
	 a special case; it's the only case where a quoted string
	 can expand into more than one word.  It's going to come back
	 from the above call to expand_word_internal as a list with
	 multiple words. */
      if (list)
	dequote_list (list);

      if (ctx->temp_has_dollar_at)		/* XXX - was has_dollar_at */
	{
	  ctx->quoted_dollar_at++;
	  if (ctx->contains_dollar_at)
	    *ctx->contains_dollar_at = 1;
	  if (ctx->expanded_something)
	    *ctx->expanded_something = 1;
	  ctx->local_expanded = 1;
	}
    }
  else
    {
      /* What we have is "".  This is a minor optimization. */
      FREE (ctx->temp);
      list = (WORD_LIST *)NULL;
      ctx->had_quoted_null = 1;	/* note for later */
    }

  /* The code above *might* return a list (consider the case of "$@",
     where it returns "$1", "$2", etc.).  We can't throw away the
     rest of the list, and we have to make sure each word gets added
     as quoted.  We test on tresult->next:  if it is non-NULL, we
     quote the whole list, save it to a string with string_list, and
     add that string. We don't need to quote the results of this
     (and it would be wrong, since that would quote the separators
     as well), so we go directly to add_string. */
  if (list)
    {
      if (list->next)
	{
	  /* Testing quoted_dollar_at makes sure that "$@" is
	     split correctly when $IFS does not contain a space. */
	  ctx->temp = ctx->quoted_dollar_at
			      ? string_list_dollar_at (list, Q_DOUBLE_QUOTES, 0)
			      : string_list (quote_list (list));
	  dispose_words (list);
	  return EWI_ADD_STRING;
	}
      else
	{
	  ctx->temp = savestring (list->word->word);
	  ctx->tflag = list->word->flags;
	  dispose_words (list);

	  /* If the string is not a quoted null string, we want
	     to remove any embedded unquoted CTLNUL characters.
	     We do not want to turn quoted null strings back into
	     the empty string, though.  We do this because we
	     want to remove any quoted nulls from expansions that
	     contain other characters.  For example, if we have
	     x"$*"y or "x$*y" and there are no positional parameters,
	     the $* should expand into nothing. */
	  /* We use the W_HASQUOTEDNULL flag to differentiate the
	     cases:  a quoted null character as above and when
	     CTLNUL is contained in the (non-null) expansion
	     of some variable.  We use the had_quoted_null flag to
	     pass the value through this function to its caller. */
	  if ((ctx->tflag & W_HASQUOTEDNULL) && QUOTED_NULL (ctx->temp) == 0)
	    remove_quoted_nulls (ctx->temp);	/* XXX */
	}
    }
  else
    ctx->temp = (char *)NULL;

  if (ctx->temp == 0 && ctx->quoted_state == PARTIALLY_QUOTED)
    ctx->had_quoted_null = 1;	/* note for later */

  /* We do not want to add quoted nulls to strings that are only
     partially quoted; we can throw them away.  The exception to
     this is when we are going to be performing word splitting,
     since we have to preserve a null argument if the next character
     will cause word splitting. */
  if (ctx->temp == 0 && ctx->quoted_state == PARTIALLY_QUOTED && ctx->quoted == 0 && (ctx->word->flags & (W_NOSPLIT|W_EXPANDRHS|W_ASSIGNRHS)) == W_EXPANDRHS)
    {
      ctx->c = CTLNUL;
      ctx->sindex--;
      ctx->had_quoted_null = 1;
      return EWI_ADD_CHARACTER;
    }
  if (ctx->temp == 0 && ctx->quoted_state == PARTIALLY_QUOTED && (ctx->word->flags & (W_NOSPLIT|W_NOSPLIT2)))
    return EWI_CONTINUE;

  /* Fall through to add_quoted_string logic. */
  return EWI_ADD_QUOTED_STRING;
}

/* ------------------------------------------------------------------ */
/* ewi_assemble_result -- post-loop result assembly                   */
/*   (the `finished_with_string:` label block)                        */
/* ------------------------------------------------------------------ */
static WORD_LIST *
ewi_assemble_result (struct ewi_context *ctx)
{
  WORD_LIST *list;
  WORD_DESC *tword;

  list = (WORD_LIST *)NULL;

  if (*ctx->istring == '\0')
    {
#if 0
      if (ctx->quoted_dollar_at == 0 && (ctx->had_quoted_null || ctx->quoted_state == PARTIALLY_QUOTED))
#else
      if (ctx->had_quoted_null || (ctx->quoted_dollar_at == 0 && ctx->quoted_state == PARTIALLY_QUOTED))
#endif
	{
	  ctx->istring[0] = CTLNUL;
	  ctx->istring[1] = '\0';
	  tword = alloc_word_desc ();
	  tword->word = ctx->istring;
	  ctx->istring = 0;		/* avoid later free() */
	  tword->flags |= W_HASQUOTEDNULL;		/* XXX */
	  list = make_word_list (tword, (WORD_LIST *)NULL);
	  if (ctx->quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
	    tword->flags |= W_QUOTED;
	}
      /* According to sh, ksh, and Posix.2, if a word expands into nothing
	 and a double-quoted "$@" appears anywhere in it, then the entire
	 word is removed. */
      /* XXX - exception appears to be that quoted null strings result in
	 null arguments */
      else  if (ctx->quoted_state == UNQUOTED || ctx->quoted_dollar_at)
	list = (WORD_LIST *)NULL;
      else
	list = (WORD_LIST *)NULL;
    }
  else if (ctx->word->flags & W_NOSPLIT)
    {
      tword = alloc_word_desc ();
      tword->word = ctx->istring;
      if (ctx->had_quoted_null && QUOTED_NULL (ctx->istring))
	tword->flags |= W_HASQUOTEDNULL;
      ctx->istring = 0;		/* avoid later free() */
      if (ctx->word->flags & W_ASSIGNMENT)
	tword->flags |= W_ASSIGNMENT;	/* XXX */
      if (ctx->word->flags & W_COMPASSIGN)
	tword->flags |= W_COMPASSIGN;	/* XXX */
      if (ctx->word->flags & W_NOGLOB)
	tword->flags |= W_NOGLOB;	/* XXX */
      if (ctx->word->flags & W_NOBRACE)
	tword->flags |= W_NOBRACE;	/* XXX */
      if (ctx->word->flags & W_ARRAYREF)
	tword->flags |= W_ARRAYREF;
      if (ctx->quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
	tword->flags |= W_QUOTED;
      list = make_word_list (tword, (WORD_LIST *)NULL);
    }
  else if (ctx->word->flags & W_ASSIGNRHS)
    {
      list = list_string (ctx->istring, "", ctx->quoted);
      tword = list->word;
      if (ctx->had_quoted_null && QUOTED_NULL (ctx->istring))
	tword->flags |= W_HASQUOTEDNULL;
      free (list);
      free (ctx->istring);
      ctx->istring = 0;			/* avoid later free() */
      goto set_word_flags;
    }
  else
    {
      char *ifs_chars;

      ifs_chars = (ctx->quoted_dollar_at || ctx->has_dollar_at) ? ifs_value : (char *)NULL;

      /* If we have $@, we need to split the results no matter what.  If
	 IFS is unset or NULL, string_list_dollar_at has separated the
	 positional parameters with a space, so we split on space (we have
	 set ifs_chars to " \t\n" above if ifs is unset).  If IFS is set,
	 string_list_dollar_at has separated the positional parameters
	 with the first character of $IFS, so we split on $IFS.  If
	 SPLIT_ON_SPACES is set, we expanded $* (unquoted) with IFS either
	 unset or null, and we want to make sure that we split on spaces
	 regardless of what else has happened to IFS since the expansion,
	 or we expanded "$@" with IFS null and we need to split the positional
	 parameters into separate words. */
      if (ctx->split_on_spaces)
	{
	  /* If IFS is not set, and the word is not quoted, we want to split
	     the individual words on $' \t\n'. We rely on previous steps to
	     quote the portions of the word that should not be split */
	  if (ifs_is_set == 0)
	    list = list_string (ctx->istring, " \t\n", 1);	/* XXX quoted == 1? */
	  else
	    list = list_string (ctx->istring, " ", 1);	/* XXX quoted == 1? */
	}

      /* If we have $@ (has_dollar_at != 0) and we are in a context where we
	 don't want to split the result (W_NOSPLIT2), and we are not quoted,
	 we have already separated the arguments with the first character of
	 $IFS.  In this case, we want to return a list with a single word
	 with the separator possibly replaced with a space (it's what other
	 shells seem to do).
	 quoted_dollar_at is internal to this function and is set if we are
	 passed an argument that is unquoted (quoted == 0) but we encounter a
	 double-quoted $@ while expanding it. */
      else if (ctx->has_dollar_at && ctx->quoted_dollar_at == 0 && ifs_chars && ctx->quoted == 0 && (ctx->word->flags & W_NOSPLIT2))
	{
	  tword = alloc_word_desc ();
	  /* Only split and rejoin if we have to */
	  if (*ifs_chars && *ifs_chars != ' ')
	    {
	      /* list_string dequotes CTLESCs in the string it's passed, so we
		 need it to get the space separation right if space isn't the
		 first character in IFS (but is present) and to remove the
		 quoting we added back in param_expand(). */
	      list = list_string (ctx->istring, *ifs_chars ? ifs_chars : " ", 1);
	      /* This isn't exactly right in the case where we're expanding
		 the RHS of an expansion like ${var-$@} where IFS=: (for
		 example). The W_NOSPLIT2 means we do the separation with :;
		 the list_string removes the quotes and breaks the string into
		 a list, and the string_list rejoins it on spaces. When we
		 return, we expect to be able to split the results, but the
		 space separation means the right split doesn't happen. */
	      tword->word = string_list (list);
	    }
	  else
	    tword->word = ctx->istring;
	  if (ctx->had_quoted_null && QUOTED_NULL (ctx->istring))
	    tword->flags |= W_HASQUOTEDNULL;	/* XXX */
	  if (tword->word != ctx->istring)
	    free (ctx->istring);
	  ctx->istring = 0;			/* avoid later free() */
	  goto set_word_flags;
	}
      else if (ctx->has_dollar_at && ifs_chars)
	list = list_string (ctx->istring, *ifs_chars ? ifs_chars : " ", 1);
      else
	{
	  tword = alloc_word_desc ();
	  if (ctx->expanded_something && *ctx->expanded_something == 0 && ctx->has_quoted_ifs)
	    tword->word = remove_quoted_ifs (ctx->istring);
	  else
	    tword->word = ctx->istring;
	  if (ctx->had_quoted_null && QUOTED_NULL (ctx->istring))	/* should check for more than one */
	    tword->flags |= W_HASQUOTEDNULL;	/* XXX */
	  else if (ctx->had_quoted_null)
	    tword->flags |= W_SAWQUOTEDNULL;	/* XXX */
	  if (tword->word != ctx->istring)
	    free (ctx->istring);
	  ctx->istring = 0;			/* avoid later free() */
set_word_flags:
	  if ((ctx->quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) || (ctx->quoted_state == WHOLLY_QUOTED))
	    tword->flags |= W_QUOTED;
	  if (ctx->word->flags & W_ASSIGNMENT)
	    tword->flags |= W_ASSIGNMENT;
	  if (ctx->word->flags & W_COMPASSIGN)
	    tword->flags |= W_COMPASSIGN;
	  if (ctx->word->flags & W_NOGLOB)
	    tword->flags |= W_NOGLOB;
	  if (ctx->word->flags & W_NOBRACE)
	    tword->flags |= W_NOBRACE;
	  if (ctx->word->flags & W_ARRAYREF)
	    tword->flags |= W_ARRAYREF;
	  list = make_word_list (tword, (WORD_LIST *)NULL);
	}
    }

  /* Do NOT free ctx->istring here; the caller is responsible for freeing
     it after we return, using the updated ctx->istring value. */
  return (list);
}

/* ====================================================================== */

static WORD_LIST *
expand_word_internal (WORD_DESC *word, int quoted, int isexp, int *contains_dollar_at, int *expanded_something)
{
  WORD_LIST *list;
  WORD_DESC *tword;

  /* The intermediate string that we build while expanding. */
  char *istring;

  /* The current size of the above object. */
  size_t istring_size;

  /* Index into ISTRING. */
  size_t istring_index;

  /* Temporary string storage. */
  char *temp, *temp1;

  /* The text of WORD. */
  register char *string;

  /* The size of STRING. */
  size_t string_size;

  /* The index into STRING. */
  int sindex;

  /* This gets 1 if we see a $@ while quoted. */
  int quoted_dollar_at;

  /* One of UNQUOTED, PARTIALLY_QUOTED, or WHOLLY_QUOTED, depending on
     whether WORD contains no quoting characters, a partially quoted
     string (e.g., "xx"ab), or is fully quoted (e.g., "xxab"). */
  int quoted_state;

  /* State flags */
  int had_quoted_null;
  int has_quoted_ifs;		/* did we add a quoted $IFS character here? */
  int has_dollar_at, temp_has_dollar_at;
  int internal_tilde;
  int split_on_spaces;
  int local_expanded;
  int tflag;
  int pflags;			/* flags passed to param_expand */
  int mb_cur_max;

  int assignoff;		/* If assignment, offset of `=' */

  register unsigned char c;	/* Current character. */
  int t_index;			/* For calls to string_extract_xxx. */

  char twochars[2];

  struct ewi_context ctx;
  enum ewi_action ewi_act;

  DECLARE_MBSTATE;

  /* OK, let's see if we can optimize a common idiom: "$@". This needs to make sure
     that all of the flags callers care about (e.g., W_HASQUOTEDNULL) are set in
     list->flags. */
  if (STREQ (word->word, "\"$@\"") &&
      (word->flags == (W_HASDOLLAR|W_QUOTED)) &&
      dollar_vars[1])		/* XXX - check IFS here as well? */
    {
      if (contains_dollar_at)
	*contains_dollar_at = 1;
      if (expanded_something)
	*expanded_something = 1;
      if (cached_quoted_dollar_at)
	return (copy_word_list (cached_quoted_dollar_at));
      list = list_rest_of_args ();
      list = quote_list (list);
      cached_quoted_dollar_at = copy_word_list (list);
      return (list);
    }

  istring = (char *)xmalloc (istring_size = DEFAULT_INITIAL_ARRAY_SIZE);
  istring[istring_index = 0] = '\0';
  quoted_dollar_at = had_quoted_null = has_dollar_at = 0;
  has_quoted_ifs = 0;
  split_on_spaces = 0;
  internal_tilde = 0;		/* expanding =~ or :~ */
  quoted_state = UNQUOTED;

  string = word->word;
  if (string == 0)
    goto finished_with_string;
  mb_cur_max = MB_CUR_MAX;

  /* Don't need the string length for the SADD... and COPY_ macros unless
     multibyte characters are possible, but do need it for bounds checking. */
  string_size = (mb_cur_max > 1) ? strlen (string) : 1;

  if (contains_dollar_at)
    *contains_dollar_at = 0;

  assignoff = -1;

  /* Begin the expansion. */

  for (sindex = 0; ;)
    {
      c = string[sindex];

      /* Case on top-level character. */
      switch (c)
	{
	case '\0':
	  goto finished_with_string;

	case CTLESC:
	  sindex++;
#if HANDLE_MULTIBYTE
	  if (mb_cur_max > 1 && string[sindex])
	    {
	      SADD_MBQCHAR_BODY(temp, string, sindex, string_size);
	    }
	  else
#endif
	    {
	      temp = (char *)xmalloc (3);
	      temp[0] = CTLESC;
	      temp[1] = c = string[sindex];
	      temp[2] = '\0';
	    }

dollar_add_string:
	  if (string[sindex])
	    sindex++;

add_string:
	  if (temp)
	    {
	      istring = sub_append_string (temp, istring, &istring_index, &istring_size);
	      temp = (char *)0;
	    }

	  break;

#if defined (PROCESS_SUBSTITUTION)
	  /* Process substitution. */
	case '<':
	case '>':
	  {
	       /* XXX - technically this should only be expanded at the start
	       of a word */
	    if (string[++sindex] != LPAREN || (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) || (word->flags & W_NOPROCSUB))
	      {
		sindex--;	/* add_character: label increments sindex */
		goto add_character;
	      }
	    else
	      t_index = sindex + 1; /* skip past both '<' and LPAREN */

	    temp1 = extract_process_subst (string, (c == '<') ? "<(" : ">(", &t_index, 0); /*))*/
	    sindex = t_index;

	    /* If the process substitution specification is `<()', we want to
	       open the pipe for writing in the child and produce output; if
	       it is `>()', we want to open the pipe for reading in the child
	       and consume input. */
	    temp = temp1 ? process_substitute (temp1, (c == '>')) : (char *)0;

	    FREE (temp1);

	    goto dollar_add_string;
	  }
#endif /* PROCESS_SUBSTITUTION */

#if defined (ARRAY_VARS)
	case '[':		/*]*/
	  if ((quoted & Q_ARITH) == 0 || shell_compatibility_level <= 51)
	    {
	      if (isexp == 0 && (word->flags & (W_NOSPLIT|W_NOSPLIT2)) == 0 && isifs (c) && (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) == 0)
		goto add_ifs_character;
	      else
		goto add_character;
	    }
	  else
	    {
	      temp = expand_array_subscript (string, &sindex, quoted, word->flags);
	      goto add_string;
	    }
#endif

	case '=':
	  /* Posix.2 section 3.6.1 says that tildes following `=' in words
	     which are not assignment statements are not expanded.  If the
	     shell isn't in posix mode, though, we perform tilde expansion
	     on `likely candidate' unquoted assignment statements (flags
	     include W_ASSIGNMENT but not W_QUOTED).  A likely candidate
	     contains an unquoted :~ or =~.  Something to think about: we
	     now have a flag that says  to perform tilde expansion on arguments
	     to `assignment builtins' like declare and export that look like
	     assignment statements.  We now do tilde expansion on such words
	     even in POSIX mode. */	
	  if (word->flags & (W_ASSIGNRHS|W_NOTILDE))
	    {
	      if (isexp == 0 && (word->flags & (W_NOSPLIT|W_NOSPLIT2)) == 0 && isifs (c))
		goto add_ifs_character;
	      else
		goto add_character;
	    }
	  /* If we're not in posix mode or forcing assignment-statement tilde
	     expansion, note where the first `=' appears in the word and prepare
	     to do tilde expansion following the first `='. We have to keep
	     track of the first `=' (using assignoff) to avoid being confused
	     by an `=' in the rhs of the assignment statement. */
	  if ((word->flags & W_ASSIGNMENT) &&
	      (posixly_correct == 0 || (word->flags & W_TILDEEXP)) &&
	      assignoff == -1 && sindex > 0)
	    assignoff = sindex;
	  if (sindex == assignoff && string[sindex+1] == '~')	/* XXX */
	    internal_tilde = 1;

	  if (word->flags & W_ASSIGNARG)
	    word->flags |= W_ASSIGNRHS;		/* affects $@ */

	  if (isexp == 0 && (word->flags & (W_NOSPLIT|W_NOSPLIT2)) == 0 && isifs (c))
	    {
	      has_quoted_ifs++;
	      goto add_ifs_character;
	    }
	  else
	    goto add_character;

	case ':':
	  if (word->flags & (W_NOTILDE|W_NOASSNTILDE))
	    {
	      if (isexp == 0 && (word->flags & (W_NOSPLIT|W_NOSPLIT2)) == 0 && isifs (c))
		goto add_ifs_character;
	      else
		goto add_character;
	    }

	  if ((word->flags & (W_ASSIGNMENT|W_ASSIGNRHS)) &&
	      (posixly_correct == 0 || (word->flags & W_TILDEEXP)) &&
	      string[sindex+1] == '~')
	    internal_tilde = 1;

	  if (isexp == 0 && (word->flags & (W_NOSPLIT|W_NOSPLIT2)) == 0 && isifs (c))
	    goto add_ifs_character;
	  else
	    goto add_character;

	case '~':
	  /* If the word isn't supposed to be tilde expanded, or we're not
	     at the start of a word or after an unquoted : or = in an
	     assignment statement, we don't do tilde expansion.  We don't
	     do tilde expansion if quoted or in an arithmetic context. */

	  if ((word->flags & W_NOTILDE) ||
	      (sindex > 0 && (internal_tilde == 0)) ||
	      (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)))
	    {
	      internal_tilde = 0;
	      if (isexp == 0 && (word->flags & (W_NOSPLIT|W_NOSPLIT2)) == 0 && isifs (c) && (quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)) == 0)
		goto add_ifs_character;
	      else
		goto add_character;
	    }

	  if (word->flags & W_ASSIGNRHS)
	    tflag = 2;
	  else if (word->flags & (W_ASSIGNMENT|W_TILDEEXP))
	    tflag = 1;
	  else
	    tflag = 0;

	  temp = bash_tilde_find_word (string + sindex, tflag, &t_index);
	    
	  internal_tilde = 0;

	  if (temp && *temp && t_index > 0)
	    {
	      temp1 = bash_tilde_expand (temp, tflag);
	      if  (temp1 && *temp1 == '~' && STREQ (temp, temp1))
		{
		  FREE (temp);
		  FREE (temp1);
		  goto add_character;		/* tilde expansion failed */
		}
	      free (temp);
	      temp = temp1;
	      sindex += t_index;
	      goto add_quoted_string;		/* XXX was add_string */
	    }
	  else
	    {
	      FREE (temp);
	      goto add_character;
	    }
	
	case '$':
	  {
	    enum ewi_action act;
	    EWI_CTX_SAVE(ctx);
	    act = ewi_handle_dollar (&ctx);
	    EWI_CTX_RESTORE(ctx);
	    if (act == EWI_RETURN)
	      return ctx.list;
	    goto add_string;
	  }
	  break;

	case '`':		/* Backquoted command substitution. */
	  {
	    t_index = sindex++;

	    temp = string_extract (string, &sindex, "`", (word->flags & W_COMPLETE) ? SX_COMPLETE : SX_REQMATCH);
	    /* The test of sindex against t_index is to allow bare instances of
	       ` to pass through, for backwards compatibility. */
	    if (temp == &extract_string_error || temp == &extract_string_fatal)
	      {
		if (sindex - 1 == t_index)
		  {
		    sindex = t_index;
		    goto add_character;
		  }
		set_exit_status (EXECUTION_FAILURE);
		report_error (_("bad substitution: no closing \"`\" in %s") , string+t_index);
		free (string);
		free (istring);
		return ((temp == &extract_string_error) ? &expand_word_error
							: &expand_word_fatal);
	      }
		
	    if (expanded_something)
	      *expanded_something = 1;
	    local_expanded = 1;

	    if (word->flags & W_NOCOMSUB)
	      /* sindex + 1 because string[sindex] == '`' */
	      temp1 = substring (string, t_index, sindex + 1);
	    else
	      {
		de_backslash (temp);
		tword = command_substitute (temp, quoted, PF_BACKQUOTE);
		temp1 = tword ? tword->word : (char *)NULL;
		if (tword)
		  dispose_word_desc (tword);
	      }
	    FREE (temp);
	    temp = temp1;
	    goto dollar_add_string;
	  }

	case '\\':
	  if (string[sindex + 1] == '\n')
	    {
	      sindex += 2;
	      continue;
	    }

	  c = string[++sindex];

	  /* "However, the double-quote character ( '"' ) shall not be treated
	     specially within a here-document, except when the double-quote
	     appears within "$()", "``", or "${}"." */
	  if ((quoted & Q_HERE_DOCUMENT) && (quoted & Q_DOLBRACE) && c == '"')
	    tflag = CBSDQUOTE;		/* special case */
	  else if (quoted & Q_HERE_DOCUMENT)
	    tflag = CBSHDOC;
	  else if (quoted & Q_DOUBLE_QUOTES)
	    tflag = CBSDQUOTE;
	  else
	    tflag = 0;

	  /* From Posix discussion on austin-group list:  Backslash escaping
	     a } in ${...} is removed.  Issue 0000221 */
	  if ((quoted & Q_DOLBRACE) && c == RBRACE)
	    {
	      SCOPY_CHAR_I (twochars, CTLESC, c, string, sindex, string_size);
	    }
	  /* This is the fix for " $@\ " */
	  else if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && ((sh_syntaxtab[c] & tflag) == 0) && isexp == 0 && isifs (c))
	    {
	      RESIZE_MALLOCED_BUFFER (istring, istring_index, 2, istring_size,
				      DEFAULT_ARRAY_SIZE);
	      istring[istring_index++] = CTLESC;
	      istring[istring_index++] = '\\';
	      istring[istring_index] = '\0';

	      SCOPY_CHAR_I (twochars, CTLESC, c, string, sindex, string_size);
	    }
	  else if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && c == 0)
	    {
	      RESIZE_MALLOCED_BUFFER (istring, istring_index, 2, istring_size,
				      DEFAULT_ARRAY_SIZE);
	      istring[istring_index++] = CTLESC;
	      istring[istring_index++] = '\\';
	      istring[istring_index] = '\0';
	      break;	      
	    }
	  else if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && ((sh_syntaxtab[c] & tflag) == 0))
	    {
	      SCOPY_CHAR_I (twochars, '\\', c, string, sindex, string_size);
	    }
	  else if (c == 0)
	    {
	      c = CTLNUL;
	      sindex--;		/* add_character: label increments sindex */
	      goto add_character;
	    }
	  else
	    {
	      SCOPY_CHAR_I (twochars, CTLESC, c, string, sindex, string_size);
	    }

	  sindex++;
add_twochars:
	  /* BEFORE jumping here, we need to increment sindex if appropriate */
	  RESIZE_MALLOCED_BUFFER (istring, istring_index, 2, istring_size,
				  DEFAULT_ARRAY_SIZE);
	  istring[istring_index++] = twochars[0];
	  istring[istring_index++] = twochars[1];
	  istring[istring_index] = '\0';

	  break;

	case '"':
	  {
	    enum ewi_action act;
	    EWI_CTX_SAVE(ctx);
	    act = ewi_handle_double_quote (&ctx);
	    EWI_CTX_RESTORE(ctx);
	    switch (act)
	      {
	      case EWI_ADD_CHARACTER:	goto add_character;
	      case EWI_RETURN:		return ctx.list;
	      case EWI_BREAK:		break;
	      case EWI_ADD_STRING:	goto add_string;
	      case EWI_CONTINUE:	continue;
	      case EWI_ADD_QUOTED_STRING:
	      default:			goto add_quoted_string;
	      }
	    break;
	  }

	add_quoted_string:

	  if (temp)
	    {
	      temp1 = temp;
	      temp = quote_string (temp);
	      free (temp1);
	      goto add_string;
	    }
	  else
	    {
	      /* Add NULL arg. */
	      c = CTLNUL;
	      sindex--;		/* add_character: label increments sindex */
	      had_quoted_null = 1;	/* note for later */
	      goto add_character;
	    }

	  /* break; */

	case '\'':
	  if ((quoted & (Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT)))
	    goto add_character;

	  t_index = ++sindex;
	  temp = string_extract_single_quoted (string, &sindex, 0);

	  /* If the entire STRING was surrounded by single quotes,
	     then the string is wholly quoted. */
	  quoted_state = (t_index == 1 && string[sindex] == '\0')
			    ? WHOLLY_QUOTED
			    : PARTIALLY_QUOTED;

	  /* If all we had was '', it is a null expansion. */
	  if (*temp == '\0')
	    {
	      free (temp);
	      temp = (char *)NULL;
	    }
	  else
	    remove_quoted_escapes (temp);	/* ??? */

	  if (temp == 0 && quoted_state == PARTIALLY_QUOTED)
	    had_quoted_null = 1;	/* note for later */

	  /* We do not want to add quoted nulls to strings that are only
	     partially quoted; such nulls are discarded.  See above for the
	     exception, which is when the string is going to be split.
	     Posix interp 888/1129 */
	  if (temp == 0 && quoted_state == PARTIALLY_QUOTED && quoted == 0 && (word->flags & (W_NOSPLIT|W_EXPANDRHS|W_ASSIGNRHS)) == W_EXPANDRHS)
	    {
	      c = CTLNUL;
	      sindex--;
	      goto add_character;
	    }

	  if (temp == 0 && (quoted_state == PARTIALLY_QUOTED) && (word->flags & (W_NOSPLIT|W_NOSPLIT2)))
	    continue;

	  /* If we have a quoted null expansion, add a quoted NULL to istring. */
	  if (temp == 0)
	    {
	      c = CTLNUL;
	      sindex--;		/* add_character: label increments sindex */
	      goto add_character;
	    }
	  else
	    goto add_quoted_string;

	  /* break; */

	case ' ':
	  /* If we are in a context where the word is not going to be split, but
	     we need to account for $@ and $* producing one word for each
	     positional parameter, add quoted spaces so the spaces in the
	     expansion of "$@", if any, behave correctly. We still may need to
	     split if we are expanding the rhs of a word expansion. */
	  if (ifs_is_null || split_on_spaces || ((word->flags & (W_NOSPLIT|W_NOSPLIT2|W_ASSIGNRHS)) && (word->flags & W_EXPANDRHS) == 0))
	    {
	      if (string[sindex])
		sindex++;
	      twochars[0] = CTLESC;
	      twochars[1] = c;
	      goto add_twochars;
	    }
	  /* FALLTHROUGH */
	  
	default:
	  /* This is the fix for " $@ " */
add_ifs_character:
	  if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) || (isexp == 0 && isifs (c) && (word->flags & (W_NOSPLIT|W_NOSPLIT2)) == 0))
	    {
	      if ((quoted&(Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) == 0)
		has_quoted_ifs++;
add_quoted_character:
	      if (string[sindex])	/* from old goto dollar_add_string */
		sindex++;
	      if (c == 0)
		{
		  c = CTLNUL;
		  goto add_character;
		}
	      else
		{
#if HANDLE_MULTIBYTE
		  /* XXX - should make sure that c is actually multibyte,
		     otherwise we can use the twochars branch */
		  if (mb_cur_max > 1)
		    sindex--;

		  if (mb_cur_max > 1)
		    {
		      SADD_MBQCHAR_BODY(temp, string, sindex, string_size);
		    }
		  else
#endif
		    {
		      twochars[0] = CTLESC;
		      twochars[1] = c;
		      goto add_twochars;
		    }
		}
	    }

	  SADD_MBCHAR (temp, string, sindex, string_size);

add_character:
	  RESIZE_MALLOCED_BUFFER (istring, istring_index, 1, istring_size,
				  DEFAULT_ARRAY_SIZE);
	  istring[istring_index++] = c;
	  istring[istring_index] = '\0';

	  /* Next character. */
	  sindex++;
	}
    }

finished_with_string:
  /* Assemble the final result from the expanded istring.  Handles quoting
     state, $@ splitting, word flags, and IFS-based splitting. */
  EWI_CTX_SAVE(ctx);
  list = ewi_assemble_result (&ctx);
  /* ewi_assemble_result may have set istring to 0 to prevent double-free */
  istring = ctx.istring;
  free (istring);
  return (list);
}

/* **************************************************************** */
/*								    */
/*		   Functions for Quote Removal			    */
/*								    */
/* **************************************************************** */

/* Perform quote removal on STRING.  If QUOTED > 0, assume we are obeying the
   backslash quoting rules for within double quotes or a here document. */
char *
string_quote_removal (char *string, int quoted)
{
  size_t slen;
  char *r, *result_string, *temp, *send;
  int sindex, tindex, dquote;
  unsigned char c;
  DECLARE_MBSTATE;

  /* The result can be no longer than the original string. */
  slen = strlen (string);
  send = string + slen;

  r = result_string = (char *)xmalloc (slen + 1);

  for (dquote = sindex = 0; c = string[sindex];)
    {
      switch (c)
	{
	case '\\':
	  c = string[++sindex];
	  if (c == 0)
	    {
	      *r++ = '\\';
	      break;
	    }
	  if (((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) || dquote) && (sh_syntaxtab[c] & CBSDQUOTE) == 0)
	    *r++ = '\\';
	  /* FALLTHROUGH */

	default:
	  SCOPY_CHAR_M (r, string, send, sindex);
	  break;

	case '\'':
	  if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) || dquote)
	    {
	      *r++ = c;
	      sindex++;
	      break;
	    }
	  tindex = sindex + 1;
	  temp = string_extract_single_quoted (string, &tindex, 0);
	  if (temp)
	    {
	      strcpy (r, temp);
	      r += strlen (r);
	      free (temp);
	    }
	  sindex = tindex;
	  break;

	case '"':
	  dquote = 1 - dquote;
	  sindex++;
	  break;
	}
    }
    *r = '\0';
    return (result_string);
}

#if 0
/* UNUSED */
/* Perform quote removal on word WORD.  This allocates and returns a new
   WORD_DESC *. */
WORD_DESC *
word_quote_removal (WORD_DESC *word, int quoted)
{
  WORD_DESC *w;
  char *t;

  t = string_quote_removal (word->word, quoted);
  w = alloc_word_desc ();
  w->word = t ? t : savestring ("");
  return (w);
}

/* Perform quote removal on all words in LIST.  If QUOTED is non-zero,
   the members of the list are treated as if they are surrounded by
   double quotes.  Return a new list, or NULL if LIST is NULL. */
WORD_LIST *
word_list_quote_removal (WORD_LIST *list, int quoted)
{
  WORD_LIST *result, *t, *tresult, *e;

  for (t = list, result = (WORD_LIST *)NULL; t; t = t->next)
    {
      tresult = make_word_list (word_quote_removal (t->word, quoted), (WORD_LIST *)NULL);
#if 0
      result = (WORD_LIST *) list_append (result, tresult);
#else
      if (result == 0)
	result = e = tresult;
      else
	{
	  e->next = tresult;
	  while (e->next)
	    e = e->next;
	}
#endif
    }
  return (result);
}
#endif

/*******************************************
 *					   *
 *    Functions to perform word splitting  *
 *					   *
 *******************************************/

void
setifs (SHELL_VAR *v)
{
  char *t;
  unsigned char uc;

  ifs_var = v;
  ifs_value = (v && value_cell (v)) ? value_cell (v) : " \t\n";

  ifs_is_set = ifs_var != 0;
  ifs_is_null = ifs_is_set && (*ifs_value == 0);

  /* Should really merge ifs_cmap with sh_syntaxtab.  XXX - doesn't yet
     handle multibyte chars in IFS */
  memset (ifs_cmap, '\0', sizeof (ifs_cmap));
  for (t = ifs_value ; t && *t; t++)
    {
      uc = *t;
      ifs_cmap[uc] = 1;
    }

#if defined (HANDLE_MULTIBYTE)
  if (ifs_value == 0)
    {
      ifs_firstc[0] = '\0';	/* XXX - ? */
      ifs_firstc_len = 1;
    }
  else
    {
      if (locale_utf8locale && UTF8_SINGLEBYTE (*ifs_value))
	ifs_firstc_len = (*ifs_value != 0) ? 1 : 0;
      else
	{
	  size_t ifs_len;
	  ifs_len = strnlen (ifs_value, MB_CUR_MAX);
	  ifs_firstc_len = MBLEN (ifs_value, ifs_len);
	}
      if (ifs_firstc_len == 1 || ifs_firstc_len == 0 || MB_INVALIDCH (ifs_firstc_len))
	{
	  ifs_firstc[0] = ifs_value[0];
	  ifs_firstc[1] = '\0';
	  ifs_firstc_len = 1;
	}
      else
	memcpy (ifs_firstc, ifs_value, ifs_firstc_len);
    }
#else
  ifs_firstc = ifs_value ? *ifs_value : 0;
#endif
}

char *
getifs ()
{
  return ifs_value;
}

/* This splits a single word into a WORD LIST on $IFS, but only if the word
   is not quoted.  list_string () performs quote removal for us, even if we
   don't do any splitting. */
WORD_LIST *
word_split (WORD_DESC *w, char *ifs_chars)
{
  WORD_LIST *result;

  if (w)
    {
      char *xifs;

      xifs = ((w->flags & W_QUOTED) || ifs_chars == 0) ? "" : ifs_chars;
      result = list_string (w->word, xifs, w->flags & W_QUOTED);
    }
  else
    result = (WORD_LIST *)NULL;

  return (result);
}

/* Perform word splitting on LIST and return the RESULT.  It is possible
   to return (WORD_LIST *)NULL. */
static WORD_LIST *
word_list_split (WORD_LIST *list)
{
  WORD_LIST *result, *t, *tresult, *e;
  WORD_DESC *w;

  for (t = list, result = (WORD_LIST *)NULL; t; t = t->next)
    {
      tresult = word_split (t->word, ifs_value);
      /* POSIX 2.6: "If the complete expansion appropriate for a word results
	 in an empty field, that empty field shall be deleted from the list
	 of fields that form the completely expanded command, unless the
	 original word contained single-quote or double-quote characters."
	 This is where we handle these words that contain quoted null strings
	 and other characters that expand to nothing after word splitting. */
      if (tresult == 0 && t->word && (t->word->flags & W_SAWQUOTEDNULL))	/* XXX */
	{
	  w = alloc_word_desc ();
	  w->word = (char *)xmalloc (1);
	  w->word[0] = '\0';
	  tresult = make_word_list (w, (WORD_LIST *)NULL);
	}
#if defined (ARRAY_VARS)
      /* pass W_ARRAYREF through for words that are not split and are
	 identical to the original word. */
      if (tresult && tresult->next == 0 && t->next == 0 && (t->word->flags & W_ARRAYREF) && STREQ (t->word->word, tresult->word->word))
	tresult->word->flags |= W_ARRAYREF;
#endif
      if (result == 0)
        result = e = tresult;
      else
	{
	  e->next = tresult;
	  while (e->next)
	    e = e->next;
	}
    }
  return (result);
}

/**************************************************
 * 						  *
 *    Functions to expand an entire WORD_LIST	  *
 *						  *
 **************************************************/

/* Do any word-expansion-specific cleanup and jump to top_level */
void
exp_jump_to_top_level (int v)
{
  set_pipestatus_from_exit (last_command_exit_value);

  /* Cleanup code goes here. */
  expand_no_split_dollar_star = 0;	/* XXX */
  if (expanding_redir)
    undo_partial_redirects ();
  expanding_redir = 0;
  assigning_in_environment = 0;

  if (parse_and_execute_level == 0)
    top_level_cleanup ();			/* from sig.c */

  jump_to_top_level (v);
}

/* Put NLIST (which is a WORD_LIST * of only one element) at the front of
   ELIST, and set ELIST to the new list. */
#define PREPEND_LIST(nlist, elist) \
	do { nlist->next = elist; elist = nlist; } while (0)

/* Separate out any initial variable assignments from TLIST.  If set -k has
   been executed, remove all assignment statements from TLIST.  Initial
   variable assignments and other environment assignments are placed
   on SUBST_ASSIGN_VARLIST. */
static WORD_LIST *
separate_out_assignments (WORD_LIST *tlist)
{
  register WORD_LIST *vp, *lp;

  if (tlist == 0)
    return ((WORD_LIST *)NULL);

  if (subst_assign_varlist)
    dispose_words (subst_assign_varlist);	/* Clean up after previous error */

  subst_assign_varlist = (WORD_LIST *)NULL;
  vp = lp = tlist;

  /* Separate out variable assignments at the start of the command.
     Loop invariant: vp->next == lp
     Loop postcondition:
	lp = list of words left after assignment statements skipped
	tlist = original list of words
  */
  while (lp && (lp->word->flags & W_ASSIGNMENT))
    {
      vp = lp;
      lp = lp->next;
    }

  /* If lp != tlist, we have some initial assignment statements.
     We make SUBST_ASSIGN_VARLIST point to the list of assignment
     words and TLIST point to the remaining words.  */
  if (lp != tlist)
    {
      subst_assign_varlist = tlist;
      /* ASSERT(vp->next == lp); */
      vp->next = (WORD_LIST *)NULL;	/* terminate variable list */
      tlist = lp;			/* remainder of word list */
    }

  /* vp == end of variable list */
  /* tlist == remainder of original word list without variable assignments */
  if (!tlist)
    /* All the words in tlist were assignment statements */
    return ((WORD_LIST *)NULL);

  /* ASSERT(tlist != NULL); */
  /* ASSERT((tlist->word->flags & W_ASSIGNMENT) == 0); */

  /* If the -k option is in effect, we need to go through the remaining
     words, separate out the assignment words, and place them on
     SUBST_ASSIGN_VARLIST. */
  if (place_keywords_in_env)
    {
      WORD_LIST *tp;	/* tp == running pointer into tlist */

      tp = tlist;
      lp = tlist->next;

      /* Loop Invariant: tp->next == lp */
      /* Loop postcondition: tlist == word list without assignment statements */
      while (lp)
	{
	  if (lp->word->flags & W_ASSIGNMENT)
	    {
	      /* Found an assignment statement, add this word to end of
		 subst_assign_varlist (vp). */
	      if (!subst_assign_varlist)
		subst_assign_varlist = vp = lp;
	      else
		{
		  vp->next = lp;
		  vp = lp;
		}

	      /* Remove the word pointed to by LP from TLIST. */
	      tp->next = lp->next;
	      /* ASSERT(vp == lp); */
	      lp->next = (WORD_LIST *)NULL;
	      lp = tp->next;
	    }
	  else
	    {
	      tp = lp;
	      lp = lp->next;
	    }
	}
    }
  return (tlist);
}

#define WEXP_VARASSIGN	0x001
#define WEXP_BRACEEXP	0x002
#define WEXP_TILDEEXP	0x004
#define WEXP_PARAMEXP	0x008
#define WEXP_PATHEXP	0x010

/* All of the expansions, including variable assignments at the start of
   the list. */
#define WEXP_ALL	(WEXP_VARASSIGN|WEXP_BRACEEXP|WEXP_TILDEEXP|WEXP_PARAMEXP|WEXP_PATHEXP)

/* All of the expansions except variable assignments at the start of
   the list. */
#define WEXP_NOVARS	(WEXP_BRACEEXP|WEXP_TILDEEXP|WEXP_PARAMEXP|WEXP_PATHEXP)

/* All of the `shell expansions': brace expansion, tilde expansion, parameter
   expansion, command substitution, arithmetic expansion, word splitting, and
   quote removal. */
#define WEXP_SHELLEXP	(WEXP_BRACEEXP|WEXP_TILDEEXP|WEXP_PARAMEXP)

/* Take the list of words in LIST and do the various substitutions.  Return
   a new list of words which is the expanded list, and without things like
   variable assignments. */

WORD_LIST *
expand_words (WORD_LIST *list)
{
  return (expand_word_list_internal (list, WEXP_ALL));
}

/* Same as expand_words (), but doesn't hack variable or environment
   variables. */
WORD_LIST *
expand_words_no_vars (WORD_LIST *list)
{
  return (expand_word_list_internal (list, WEXP_NOVARS));
}

WORD_LIST *
expand_words_shellexp (WORD_LIST *list)
{
  return (expand_word_list_internal (list, WEXP_SHELLEXP));
}

static WORD_LIST *
glob_expand_word_list (WORD_LIST *tlist, int eflags)
{
  char **glob_array, *temp_string;
  register int glob_index;
  WORD_LIST *glob_list, *output_list, *disposables, *next;
  WORD_DESC *tword;
  int x;

  output_list = disposables = (WORD_LIST *)NULL;
  glob_array = (char **)NULL;
  while (tlist)
    {
      /* For each word, either globbing is attempted or the word is
	 added to orig_list.  If globbing succeeds, the results are
	 added to orig_list and the word (tlist) is added to the list
	 of disposable words.  If globbing fails and failed glob
	 expansions are left unchanged (the shell default), the
	 original word is added to orig_list.  If globbing fails and
	 failed glob expansions are removed, the original word is
	 added to the list of disposable words.  orig_list ends up
	 in reverse order and requires a call to REVERSE_LIST to
	 be set right.  After all words are examined, the disposable
	 words are freed. */
      next = tlist->next;

      /* If the word isn't an assignment and contains an unquoted
	 pattern matching character, then glob it. */
      if ((tlist->word->flags & W_NOGLOB) == 0 &&
	  unquoted_glob_pattern_p (tlist->word->word))
	{
	  glob_array = shell_glob_filename (tlist->word->word, QGLOB_CTLESC);	/* XXX */

	  /* Handle error cases.
	     I don't think we should report errors like "No such file
	     or directory".  However, I would like to report errors
	     like "Read failed". */

	  if (glob_array == 0 || GLOB_FAILED (glob_array))
	    {
	      glob_array = (char **)xmalloc (sizeof (char *));
	      glob_array[0] = (char *)NULL;
	    }

	  /* Dequote the current word in case we have to use it. */
	  if (glob_array[0] == NULL)
	    {
	      temp_string = dequote_string (tlist->word->word);
	      free (tlist->word->word);
	      tlist->word->word = temp_string;
	    }

	  /* Make the array into a word list. */
	  glob_list = (WORD_LIST *)NULL;
	  for (glob_index = 0; glob_array[glob_index]; glob_index++)
	    {
	      tword = make_bare_word (glob_array[glob_index]);
	      glob_list = make_word_list (tword, glob_list);
	    }

	  if (glob_list)
	    {
	      output_list = (WORD_LIST *)list_append (glob_list, output_list);
	      PREPEND_LIST (tlist, disposables);
	    }
	  else if (fail_glob_expansion != 0)
	    {
	      last_command_exit_value = EXECUTION_FAILURE;
	      report_error (_("no match: %s"), tlist->word->word);
	      exp_jump_to_top_level (DISCARD);
	    }
	  else if (allow_null_glob_expansion == 0)
	    {
	      /* Failed glob expressions are left unchanged. */
	      PREPEND_LIST (tlist, output_list);
	    }
	  else
	    {
	      /* Failed glob expressions are removed. */
	      PREPEND_LIST (tlist, disposables);
	    }
	}
      else
	{
	  /* Dequote the string. */
	  temp_string = dequote_string (tlist->word->word);
	  free (tlist->word->word);
	  tlist->word->word = temp_string;
	  PREPEND_LIST (tlist, output_list);
	}

      strvec_dispose (glob_array);
      glob_array = (char **)NULL;

      tlist = next;
    }

  if (disposables)
    dispose_words (disposables);

  if (output_list)
    output_list = REVERSE_LIST (output_list, WORD_LIST *);

  return (output_list);
}

#if defined (BRACE_EXPANSION)
static WORD_LIST *
brace_expand_word_list (WORD_LIST *tlist, int eflags)
{
  register char **expansions;
  char *temp_string;
  WORD_LIST *disposables, *output_list, *next;
  WORD_DESC *w;
  int eindex;

  for (disposables = output_list = (WORD_LIST *)NULL; tlist; tlist = next)
    {
      next = tlist->next;

      if (tlist->word->flags & W_NOBRACE)
        {
/*itrace("brace_expand_word_list: %s: W_NOBRACE", tlist->word->word);*/
	  PREPEND_LIST (tlist, output_list);
	  continue;
        }

      if ((tlist->word->flags & (W_COMPASSIGN|W_ASSIGNARG)) == (W_COMPASSIGN|W_ASSIGNARG))
        {
/*itrace("brace_expand_word_list: %s: W_COMPASSIGN|W_ASSIGNARG", tlist->word->word);*/
	  PREPEND_LIST (tlist, output_list);
	  continue;
        }

      /* Only do brace expansion if the word has a brace character.  If
	 not, just add the word list element to BRACES and continue.  In
	 the common case, at least when running shell scripts, this will
	 degenerate to a bunch of calls to `mbschr', and then what is
	 basically a reversal of TLIST into BRACES, which is corrected
	 by a call to REVERSE_LIST () on BRACES when the end of TLIST
	 is reached. */
      if (mbschr (tlist->word->word, LBRACE))
	{
	  expansions = brace_expand (tlist->word->word);

	  for (eindex = 0; temp_string = expansions[eindex]; eindex++)
	    {
	      w = alloc_word_desc ();
	      w->word = temp_string;

	      /* If brace expansion didn't change the word, preserve
		 the flags.  We may want to preserve the flags
		 unconditionally someday -- XXX */
	      if (STREQ (temp_string, tlist->word->word))
		w->flags = tlist->word->flags;
	      else
		w = make_word_flags (w, temp_string);

	      output_list = make_word_list (w, output_list);
	    }
	  free (expansions);

	  /* Add TLIST to the list of words to be freed after brace
	     expansion has been performed. */
	  PREPEND_LIST (tlist, disposables);
	}
      else
	PREPEND_LIST (tlist, output_list);
    }

  if (disposables)
    dispose_words (disposables);

  if (output_list)
    output_list = REVERSE_LIST (output_list, WORD_LIST *);

  return (output_list);
}
#endif

#if defined (ARRAY_VARS)
/* Take WORD, a compound array assignment, and internally run (for example),
   'declare -A w', where W is the variable name portion of WORD. OPTION is
   the list of options to supply to `declare'. CMD is the declaration command
   we are expanding right now; it's unused currently. */
static int
make_internal_declare (char *word, char *option, char *cmd)
{
  int t, r;
  WORD_LIST *wl;
  WORD_DESC *w;

  w = make_word (word);

  t = assignment (w->word, 0);
  if (w->word[t] == '=')
    {
      w->word[t] = '\0';
      if (w->word[t - 1] == '+')	/* cut off any append op */
	w->word[t - 1] = '\0';
    }

  wl = make_word_list (w, (WORD_LIST *)NULL);
  wl = make_word_list (make_word (option), wl);

  r = declare_builtin (wl);

  dispose_words (wl);
  return r;
}  

/* Expand VALUE in NAME[+]=( VALUE ) to a list of words. FLAGS is 1 if NAME
   is an associative array.

   If we are  processing an indexed array, expand_compound_array_assignment
   will expand all the individual words and quote_compound_array_list will
   single-quote them. If we are processing an associative array, we use
   parse_string_to_word_list to split VALUE into a list of words instead of
   faking up a shell variable and calling expand_compound_array_assignment.
   expand_and_quote_assoc_word expands and single-quotes each word in VALUE
   together so we don't have problems finding the end of the subscript when
   quoting it.

   Words in VALUE can be individual words, which are expanded and single-quoted,
   or words of the form [IND]=VALUE, which end up as explained below, as
   ['expanded-ind']='expanded-value'. */

static WORD_LIST *
expand_oneword (char *value, int flags)
{
  WORD_LIST *l, *nl;
  char *t;
  int kvpair;
  
  if (flags == 0)
    {
      /* Indexed array */
      l = expand_compound_array_assignment ((SHELL_VAR *)NULL, value, flags);
      /* Now we quote the results of the expansion above to prevent double
	 expansion. */
      quote_compound_array_list (l, flags);
      return l;
    }
  else
    {
      /* Associative array */
      l = parse_string_to_word_list (value, 1, "array assign");
#if ASSOC_KVPAIR_ASSIGNMENT
      kvpair = kvpair_assignment_p (l);
#endif

      /* For associative arrays, with their arbitrary subscripts, we have to
	 expand and quote in one step so we don't have to search for the
	 closing right bracket more than once. */
      for (nl = l; nl; nl = nl->next)
	{
#if ASSOC_KVPAIR_ASSIGNMENT
	  if (kvpair)
	    /* keys and values undergo the same set of expansions */
	    t = expand_and_quote_kvpair_word (nl->word->word);
	  else
#endif
	  if ((nl->word->flags & W_ASSIGNMENT) == 0)
	    t = sh_single_quote (nl->word->word ? nl->word->word : "");
	  else
	    t = expand_and_quote_assoc_word (nl->word->word, flags);
	  free (nl->word->word);
	  nl->word->word = t;
	}
      return l;
    }
}

/* Expand a single compound assignment argument to a declaration builtin.
   This word takes the form NAME[+]=( VALUE ). The NAME[+]= is passed through
   unchanged. The VALUE is expanded and each word in the result is single-
   quoted. Words of the form [key]=value end up as
   ['expanded-key']='expanded-value'. Associative arrays have special
   handling, see expand_oneword() above. The return value is
   NAME[+]=( expanded-and-quoted-VALUE ). */
static void
expand_compound_assignment_word (WORD_LIST *tlist, int flags)
{
  WORD_LIST *l;
  int wlen, oind, t;
  char *value, *temp;

/*itrace("expand_compound_assignment_word: original word = -%s-", tlist->word->word);*/
  t = assignment (tlist->word->word, 0);

  /* value doesn't have the open and close parens */
  oind = 1;
  value = extract_array_assignment_list (tlist->word->word + t + 1, &oind);
  /* This performs one round of expansion on the index/key and value and
     single-quotes each word in the result. */
  l = expand_oneword (value, flags);
  free (value);

  value = string_list (l);
  dispose_words (l);

  wlen = STRLEN (value);

  /* Now, let's rebuild the string */
  temp = xmalloc (t + 3 + wlen + 1);	/* name[+]=(value) */
  memcpy (temp, tlist->word->word, ++t);
  temp[t++] = '(';
  if (value)
    memcpy (temp + t, value, wlen);
  t += wlen;
  temp[t++] = ')';
  temp[t] = '\0';
/*itrace("expand_compound_assignment_word: reconstructed word = -%s-", temp);*/

  free (tlist->word->word);
  tlist->word->word = temp;

  free (value);
}

/* Expand and process an argument to a declaration command. We have already
   set flags in TLIST->word->flags depending on the declaration command
   (declare, local, etc.) and the options supplied to it (-a, -A, etc.).
   TLIST->word->word is of the form NAME[+]=( VALUE ).   

   This does several things, all using pieces of other functions to get the
   evaluation sequence right. It's called for compound array assignments with
   the W_ASSIGNMENT flag set (basically, valid identifier names on the lhs).
   It parses out which flags need to be set for declare to create the variable
   correctly, then calls declare internally (make_internal_declare) to make
   sure the variable exists with the correct attributes. Before the variable
   is created, it calls expand_compound_assignment_word to expand VALUE to a
   list of words, appropriately quoted for further evaluation. This preserves
   the semantics of word-expansion-before-calling-builtins. Finally, it calls
   do_word_assignment to perform the expansion and assignment with the same
   expansion semantics as a standalone assignment statement (no word splitting,
   etc.) even though the word is single-quoted so all that needs to happen is
   quote removal. */
static WORD_LIST *
expand_declaration_argument (WORD_LIST *tlist, WORD_LIST *wcmd)
{
  char opts[16], omap[128];
  int t, opti, oind, skip, inheriting;
  WORD_LIST *l;

  inheriting = localvar_inherit;
  opti = 0;
  if (tlist->word->flags & (W_ASSIGNASSOC|W_ASSNGLOBAL|W_CHKLOCAL|W_ASSIGNARRAY))
    opts[opti++] = '-';

  if ((tlist->word->flags & (W_ASSIGNASSOC|W_ASSNGLOBAL)) == (W_ASSIGNASSOC|W_ASSNGLOBAL))
    {
      opts[opti++] = 'g';
      opts[opti++] = 'A';
    }
  else if (tlist->word->flags & W_ASSIGNASSOC)
    {
      opts[opti++] = 'A';
    }
  else if ((tlist->word->flags & (W_ASSIGNARRAY|W_ASSNGLOBAL)) == (W_ASSIGNARRAY|W_ASSNGLOBAL))
    {
      opts[opti++] = 'g';
      opts[opti++] = 'a';
    }
  else if (tlist->word->flags & W_ASSIGNARRAY)
    {
      opts[opti++] = 'a';
    }
  else if (tlist->word->flags & W_ASSNGLOBAL)
    opts[opti++] = 'g';

  if (tlist->word->flags & W_CHKLOCAL)
    opts[opti++] = 'G';

  /* If we have special handling note the integer attribute and others
     that transform the value upon assignment.  What we do is take all
     of the option arguments and scan through them looking for options
     that cause such transformations, and add them to the `opts' array. */

  memset (omap, '\0', sizeof (omap));
  for (l = wcmd->next; l != tlist; l = l->next)
    {
      int optchar;

      if (l->word->word[0] != '-' && l->word->word[0] != '+')
	break;	/* non-option argument */
      if (l->word->word[0] == '-' && l->word->word[1] == '-' && l->word->word[2] == 0)
	break;	/* -- signals end of options */
      optchar = l->word->word[0];
      for (oind = 1; l->word->word[oind]; oind++)
	switch (l->word->word[oind])
	  {
	    case 'I':
	      inheriting = 1;
	    case 'i':
	    case 'l':
	    case 'u':
	    case 'c':
	      omap[l->word->word[oind]] = 1;
	      if (opti == 0)
		opts[opti++] = optchar;
	      break;
	    default:
	      break;
	  }
    }

  for (oind = 0; oind < sizeof (omap); oind++)
    if (omap[oind])
      opts[opti++] = oind;

  /* If there are no -a/-A options, but we have a compound assignment,
     we have a choice: we can set opts[0]='-', opts[1]='a', since the
     default is to create an indexed array, and call
     make_internal_declare with that, or we can just skip the -a and let
     declare_builtin deal with it.  Once we're here, we're better set
     up for the latter, since we don't want to deal with looking up
     any existing variable here -- better to let declare_builtin do it.
     We need the variable created, though, especially if it's local, so
     we get the scoping right before we call do_word_assignment.
     To ensure that make_local_declare gets called, we add `--' if there
     aren't any options. */
  if ((tlist->word->flags & (W_ASSIGNASSOC|W_ASSIGNARRAY)) == 0)
    {
      if (opti == 0)
	{
	  opts[opti++] = '-';
          opts[opti++] = '-';
	}
    }
  opts[opti] = '\0';

  /* This isn't perfect, but it's a start. Improvements later. We expand
     tlist->word->word and single-quote the results to avoid multiple
     expansions by, say, do_assignment_internal(). We have to weigh the
     cost of reconstructing the compound assignment string with its single
     quoting and letting the declare builtin handle it. The single quotes
     will prevent any unwanted additional expansion or word splitting. */
  expand_compound_assignment_word (tlist, (tlist->word->flags & W_ASSIGNASSOC) ? 1 : 0);

  skip = 0;
  if (opti > 0)
    {
      t = make_internal_declare (tlist->word->word, opts, wcmd ? wcmd->word->word : (char *)0);
      if (t != EXECUTION_SUCCESS)
	{
	  last_command_exit_value = t;
	  if (tlist->word->flags & W_FORCELOCAL)	/* non-fatal error */
	    skip = 1;
	  else
	    exp_jump_to_top_level (DISCARD);
	}
    }

  if (skip == 0)
    {
      t = do_word_assignment (tlist->word, 0);
      if (t == 0)
	{
	  last_command_exit_value = EXECUTION_FAILURE;
	  exp_jump_to_top_level (DISCARD);
	}
    }

  /* Now transform the word as ksh93 appears to do and go on */
  t = assignment (tlist->word->word, 0);
  tlist->word->word[t] = '\0';
  if (tlist->word->word[t - 1] == '+')
    tlist->word->word[t - 1] = '\0';	/* cut off append op */
  tlist->word->flags &= ~(W_ASSIGNMENT|W_NOSPLIT|W_COMPASSIGN|W_ASSIGNARG|W_ASSIGNASSOC|W_ASSIGNARRAY);

  return (tlist);
}
#endif /* ARRAY_VARS */

static WORD_LIST *
shell_expand_word_list (WORD_LIST *tlist, int eflags)
{
  WORD_LIST *expanded, *orig_list, *new_list, *next, *temp_list, *wcmd;
  int expanded_something, has_dollar_at;

  /* We do tilde expansion all the time.  This is what 1003.2 says. */
  wcmd = new_list = (WORD_LIST *)NULL;

  for (orig_list = tlist; tlist; tlist = next)
    {
      if (wcmd == 0 && (tlist->word->flags & W_ASSNBLTIN))
	wcmd = tlist;
	
      next = tlist->next;

#if defined (ARRAY_VARS)
      /* If this is a compound array assignment to a builtin that accepts
         such assignments (e.g., `declare'), take the assignment and perform
         it separately, handling the semantics of declarations inside shell
         functions.  This avoids the double-evaluation of such arguments,
         because `declare' does some evaluation of compound assignments on
         its own. */
      if ((tlist->word->flags & (W_COMPASSIGN|W_ASSIGNARG)) == (W_COMPASSIGN|W_ASSIGNARG))
	expand_declaration_argument (tlist, wcmd);
#endif

      expanded_something = 0;
      expanded = expand_word_internal
	(tlist->word, 0, 0, &has_dollar_at, &expanded_something);

      if (expanded == &expand_word_error || expanded == &expand_word_fatal)
	{
	  /* By convention, each time this error is returned,
	     tlist->word->word has already been freed. */
	  tlist->word->word = (char *)NULL;

	  /* Dispose our copy of the original list. */
	  dispose_words (orig_list);
	  /* Dispose the new list we're building. */
	  dispose_words (new_list);

	  last_command_exit_value = EXECUTION_FAILURE;
	  if (expanded == &expand_word_error)
	    exp_jump_to_top_level (DISCARD);
	  else
	    exp_jump_to_top_level (FORCE_EOF);
	}

      /* Don't split words marked W_NOSPLIT. */
      if (expanded_something && (tlist->word->flags & W_NOSPLIT) == 0)
	{
	  temp_list = word_list_split (expanded);
	  dispose_words (expanded);
	}
      else
	{
	  /* If no parameter expansion, command substitution, process
	     substitution, or arithmetic substitution took place, then
	     do not do word splitting.  We still have to remove quoted
	     null characters from the result. */
	  word_list_remove_quoted_nulls (expanded);
	  temp_list = expanded;
	}

      expanded = REVERSE_LIST (temp_list, WORD_LIST *);
      new_list = (WORD_LIST *)list_append (expanded, new_list);
    }

  if (orig_list)  
    dispose_words (orig_list);

  if (new_list)
    new_list = REVERSE_LIST (new_list, WORD_LIST *);

  return (new_list);
}

/* Perform assignment statements optionally preceding a command name COMMAND.
   If COMMAND == NULL, is_nullcmd usually == 1. Follow the POSIX rules for
   variable assignment errors. */
static int
do_assignment_statements (WORD_LIST *varlist, char *command, int is_nullcmd)
{
  WORD_LIST *temp_list;
  char *savecmd;
  sh_wassign_func_t *assign_func;
  int is_special_builtin, is_builtin_or_func, tint;

  /* If the remainder of the words expand to nothing, Posix.2 requires
     that the variable and environment assignments affect the shell's
     environment (do_word_assignment). */
  assign_func = is_nullcmd ? do_word_assignment : assign_in_env;
  tempenv_assign_error = 0;

  is_builtin_or_func = command && (find_shell_builtin (command) || find_function (command));
  /* Posix says that special builtins exit if a variable assignment error
     occurs in an assignment preceding it. (XXX - this is old -- current Posix
     says that any variable assignment error causes a non-interactive shell
     to exit. See the STRICT_POSIX checks below. */
  is_special_builtin = posixly_correct && command && find_special_builtin (command);

  savecmd = this_command_name;
  for (temp_list = varlist; temp_list; temp_list = temp_list->next)
    {
      this_command_name = (char *)NULL;
      assigning_in_environment = is_nullcmd == 0;
      tint = (*assign_func) (temp_list->word, is_builtin_or_func);
      assigning_in_environment = 0;
      this_command_name = savecmd;

      /* Variable assignment errors in non-interactive shells running
	 in posix mode cause the shell to exit. */
      if (tint == 0)
	{
	  if (is_nullcmd)	/* assignment statement */
	    {
	      last_command_exit_value = EXECUTION_FAILURE;
#if defined (STRICT_POSIX)
	      if (posixly_correct && interactive_shell == 0)
#else
	      if (posixly_correct && interactive_shell == 0 && executing_command_builtin == 0)
#endif
	        exp_jump_to_top_level (FORCE_EOF);
	      else
		exp_jump_to_top_level (DISCARD);
	    }
	  /* In posix mode, assignment errors in the temporary environment
	     cause a non-interactive shell executing a special builtin to
	     exit and a non-interactive shell to otherwise jump back to the
	     top level. This is what POSIX says to do for variable assignment
	     errors, and POSIX says errors in assigning to the temporary
	     environment are treated as variable assignment errors.
	     (XXX - this is not what current POSIX says - look at the
	     STRICT_POSIX defines. */
	  else if (posixly_correct)
	    {
	      last_command_exit_value = EXECUTION_FAILURE;
#if defined (STRICT_POSIX)
	      exp_jump_to_top_level ((interactive_shell == 0) ? FORCE_EOF : DISCARD);
#else
	      if (interactive_shell == 0 && is_special_builtin)
		exp_jump_to_top_level (FORCE_EOF);
	      else if (interactive_shell == 0)
		exp_jump_to_top_level (DISCARD);	/* XXX - maybe change later */
	      else
		exp_jump_to_top_level (DISCARD);
#endif
	    }
	  else
	    tempenv_assign_error++;
	}
    }
  return (tempenv_assign_error);
}

/* The workhorse for expand_words () and expand_words_no_vars ().
   First arg is LIST, a WORD_LIST of words.
   Second arg EFLAGS is a flags word controlling which expansions are
   performed.

   This does all of the substitutions: brace expansion, tilde expansion,
   parameter expansion, command substitution, arithmetic expansion,
   process substitution, word splitting, and pathname expansion, according
   to the bits set in EFLAGS.  Words with the W_QUOTED or W_NOSPLIT bits
   set, or for which no expansion is done, do not undergo word splitting.
   Words with the W_NOGLOB bit set do not undergo pathname expansion; words
   with W_NOBRACE set do not undergo brace expansion (see
   brace_expand_word_list above). */
static WORD_LIST *
expand_word_list_internal (WORD_LIST *list, int eflags)
{
  WORD_LIST *new_list, *temp_list;

  tempenv_assign_error = 0;
  if (list == 0)
    return ((WORD_LIST *)NULL);

  garglist = new_list = copy_word_list (list);
  if (eflags & WEXP_VARASSIGN)
    {
      garglist = new_list = separate_out_assignments (new_list);
      if (new_list == 0)
	{
	  if (subst_assign_varlist)
	    do_assignment_statements (subst_assign_varlist, (char *)NULL, 1);
	    
	  dispose_words (subst_assign_varlist);
	  subst_assign_varlist = (WORD_LIST *)NULL;

	  return ((WORD_LIST *)NULL);
	}
    }

  /* Begin expanding the words that remain.  The expansions take place on
     things that aren't really variable assignments. */

#if defined (BRACE_EXPANSION)
  /* Do brace expansion on this word if there are any brace characters
     in the string. */
  if ((eflags & WEXP_BRACEEXP) && brace_expansion && new_list)
    new_list = brace_expand_word_list (new_list, eflags);
#endif /* BRACE_EXPANSION */

  /* Perform the `normal' shell expansions: tilde expansion, parameter and
     variable substitution, command substitution, arithmetic expansion,
     and word splitting. */
  new_list = shell_expand_word_list (new_list, eflags);

  /* Okay, we're almost done.  Now let's just do some filename
     globbing. */
  if (new_list)
    {
      if ((eflags & WEXP_PATHEXP) && disallow_filename_globbing == 0)
	/* Glob expand the word list unless globbing has been disabled. */
	new_list = glob_expand_word_list (new_list, eflags);
      else
	/* Dequote the words, because we're not performing globbing. */
	new_list = dequote_list (new_list);
    }

  if ((eflags & WEXP_VARASSIGN) && subst_assign_varlist)
    {
      do_assignment_statements (subst_assign_varlist, (new_list && new_list->word) ? new_list->word->word : (char *)NULL, new_list == 0);

      dispose_words (subst_assign_varlist);
      subst_assign_varlist = (WORD_LIST *)NULL;
    }

  return (new_list);
}
