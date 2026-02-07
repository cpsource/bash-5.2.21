/* subst_extract.c -- String extraction/parsing, extracted from subst.c */

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

#include "bashansi.h"
#include "posixstat.h"
#include "bashintl.h"

#include "shell.h"
#include "parser.h"
#include "flags.h"
#include "jobs.h"
#include "execute_cmd.h"
#include "filecntl.h"
#include "trap.h"
#include "pathexp.h"
#include "mailcheck.h"

#include "shmbutil.h"
#if defined (HAVE_MBSTR_H) && defined (HAVE_MBSCHR)
#  include <mbstr.h>
#endif
#include "typemax.h"

#include "builtins/getopt.h"
#include "builtins/common.h"

#include "builtins/builtext.h"

#include <tilde/tilde.h>
#include <glob/strmatch.h>

#include "subst.h"
#include "subst_extract.h"

/* These defs make it easier to use the editor. */
#define LBRACE		'{'
#define RBRACE		'}'
#define LPAREN		'('
#define RPAREN		')'
#define LBRACK		'['
#define RBRACK		']'

/* Externs from subst.c not declared in any header */
extern char extract_string_error, extract_string_fatal;
extern int extended_quote;
extern int singlequote_translations;
extern void exp_jump_to_top_level PARAMS((int));

/* Forward declaration — needed cross-file from subst.c */
char *extract_dollar_brace_string PARAMS((char *, int *, int, int));

/* Extract a substring from STRING, starting at SINDEX and ending with
   one of the characters in CHARLIST.  Don't make the ending character
   part of the string.  Leave SINDEX pointing at the ending character.
   Understand about backslashes in the string.  If (flags & SX_VARNAME)
   is non-zero, and array variables have been compiled into the shell,
   everything between a `[' and a corresponding `]' is skipped over.
   If (flags & SX_NOALLOC) is non-zero, don't return the substring, just
   update SINDEX.  If (flags & SX_REQMATCH) is non-zero, the string must
   contain a closing character from CHARLIST. */
char *
string_extract (char *string, int *sindex, char *charlist, int flags)
{
  register int c, i;
  int found;
  size_t slen;
  char *temp;
  DECLARE_MBSTATE;

  slen = (MB_CUR_MAX > 1) ? strlen (string + *sindex) + *sindex : 0;
  i = *sindex;
  found = 0;
  while (c = string[i])
    {
      if (c == '\\')
	{
	  if (string[i + 1])
	    i++;
	  else
	    break;
	}
#if defined (ARRAY_VARS)
      else if ((flags & SX_VARNAME) && c == LBRACK)
	{
	  int ni;
	  /* If this is an array subscript, skip over it and continue. */
	  ni = skipsubscript (string, i, 0);
	  if (string[ni] == RBRACK)
	    i = ni;
	}
#endif
      else if (MEMBER (c, charlist))
	{
	  found = 1;
	  break;
	}

      ADVANCE_CHAR (string, slen, i);
    }

  /* If we had to have a matching delimiter and didn't find one, return an
     error and let the caller deal with it. */
  if ((flags & SX_REQMATCH) && found == 0)
    {
      *sindex = i;
      return (&extract_string_error);
    }
  
  temp = (flags & SX_NOALLOC) ? (char *)NULL : substring (string, *sindex, i);
  *sindex = i;
  
  return (temp);
}

/* Extract the contents of STRING as if it is enclosed in double quotes.
   SINDEX, when passed in, is the offset of the character immediately
   following the opening double quote; on exit, SINDEX is left pointing after
   the closing double quote.  If STRIPDQ is non-zero, unquoted double
   quotes are stripped and the string is terminated by a null byte.
   Backslashes between the embedded double quotes are processed.  If STRIPDQ
   is zero, an unquoted `"' terminates the string. */
char *
string_extract_double_quoted (char *string, int *sindex, int flags)
{
  size_t slen;
  char *send;
  int j, i, t;
  unsigned char c;
  char *temp, *ret;		/* The new string we return. */
  int pass_next, backquote, si;	/* State variables for the machine. */
  int dquote;
  int stripdq;
  DECLARE_MBSTATE;

  slen = strlen (string + *sindex) + *sindex;
  send = string + slen;

  stripdq = (flags & SX_STRIPDQ);

  pass_next = backquote = dquote = 0;
  temp = (char *)xmalloc (1 + slen - *sindex);

  j = 0;
  i = *sindex;
  while (c = string[i])
    {
      /* Process a character that was quoted by a backslash. */
      if (pass_next)
	{
	  /* XXX - take another look at this in light of Interp 221 */
	  /* Posix.2 sez:

	     ``The backslash shall retain its special meaning as an escape
	     character only when followed by one of the characters:
		$	`	"	\	<newline>''.

	     If STRIPDQ is zero, we handle the double quotes here and let
	     expand_word_internal handle the rest.  If STRIPDQ is non-zero,
	     we have already been through one round of backslash stripping,
	     and want to strip these backslashes only if DQUOTE is non-zero,
	     indicating that we are inside an embedded double-quoted string. */

	  /* If we are in an embedded quoted string, then don't strip
	     backslashes before characters for which the backslash
	     retains its special meaning, but remove backslashes in
	     front of other characters.  If we are not in an
	     embedded quoted string, don't strip backslashes at all.
	     This mess is necessary because the string was already
	     surrounded by double quotes (and sh has some really weird
	     quoting rules).
	     The returned string will be run through expansion as if
	     it were double-quoted. */
	  if ((stripdq == 0 && c != '"') ||
	      (stripdq && ((dquote && (sh_syntaxtab[c] & CBSDQUOTE)) || dquote == 0)))
	    temp[j++] = '\\';
	  pass_next = 0;

add_one_character:
	  COPY_CHAR_I (temp, j, string, send, i);
	  continue;
	}

      /* A backslash protects the next character.  The code just above
	 handles preserving the backslash in front of any character but
	 a double quote. */
      if (c == '\\')
	{
	  pass_next++;
	  i++;
	  continue;
	}

      /* Inside backquotes, ``the portion of the quoted string from the
	 initial backquote and the characters up to the next backquote
	 that is not preceded by a backslash, having escape characters
	 removed, defines that command''. */
      if (backquote)
	{
	  if (c == '`')
	    backquote = 0;
	  temp[j++] = c;	/* COPY_CHAR_I? */
	  i++;
	  continue;
	}

      if (c == '`')
	{
	  temp[j++] = c;
	  backquote++;
	  i++;
	  continue;
	}

      /* Pass everything between `$(' and the matching `)' or a quoted
	 ${ ... } pair through according to the Posix.2 specification. */
      if (c == '$' && ((string[i + 1] == LPAREN) || (string[i + 1] == LBRACE)))
	{
	  int free_ret = 1;

	  si = i + 2;
	  if (string[i + 1] == LPAREN)
	    ret = extract_command_subst (string, &si, (flags & SX_COMPLETE));
	  else
	    ret = extract_dollar_brace_string (string, &si, Q_DOUBLE_QUOTES, 0);

	  temp[j++] = '$';
	  temp[j++] = string[i + 1];

	  /* Just paranoia; ret will not be 0 unless no_longjmp_on_fatal_error
	     is set. */
	  if (ret == 0 && no_longjmp_on_fatal_error)
	    {
	      free_ret = 0;
	      ret = string + i + 2;
	    }

	  /* XXX - CHECK_STRING_OVERRUN here? */
	  for (t = 0; ret[t]; t++, j++)
	    temp[j] = ret[t];
	  temp[j] = string[si];

	  if (si < i + 2)	/* we went back? */
	    i += 2;
	  else if (string[si])
	    {
	      j++;
	      i = si + 1;
	    }
	  else
	    i = si;

	  if (free_ret)
	    free (ret);
	  continue;
	}

      /* Add any character but a double quote to the quoted string we're
	 accumulating. */
      if (c != '"')
	goto add_one_character;

      /* c == '"' */
      if (stripdq)
	{
	  dquote ^= 1;
	  i++;
	  continue;
	}

      break;
    }
  temp[j] = '\0';

  /* Point to after the closing quote. */
  if (c)
    i++;
  *sindex = i;

  return (temp);
}

/* This should really be another option to string_extract_double_quoted. */
int
skip_double_quoted (char *string, size_t slen, int sind, int flags)
{
  int c, i;
  char *ret;
  int pass_next, backquote, si;
  DECLARE_MBSTATE;

  pass_next = backquote = 0;
  i = sind;
  while (c = string[i])
    {
      if (pass_next)
	{
	  pass_next = 0;
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else if (c == '\\')
	{
	  pass_next++;
	  i++;
	  continue;
	}
      else if (backquote)
	{
	  if (c == '`')
	    backquote = 0;
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else if (c == '`')
	{
	  backquote++;
	  i++;
	  continue;
	}
      else if (c == '$' && ((string[i + 1] == LPAREN) || (string[i + 1] == LBRACE)))
	{
	  si = i + 2;
	  if (string[i + 1] == LPAREN)
	    ret = extract_command_subst (string, &si, SX_NOALLOC|(flags&SX_COMPLETE));
	  else
	    ret = extract_dollar_brace_string (string, &si, Q_DOUBLE_QUOTES, SX_NOALLOC);

	  /* These can consume the entire string if they are unterminated */
	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  i = si + 1;
	  continue;
	}
      else if (c != '"')
	{
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else
	break;
    }

  if (c)
    i++;

  return (i);
}

/* Extract the contents of STRING as if it is enclosed in single quotes.
   SINDEX, when passed in, is the offset of the character immediately
   following the opening single quote; on exit, SINDEX is left pointing after
   the closing single quote. ALLOWESC allows the single quote to be quoted by
   a backslash; it's not used yet. */
char *
string_extract_single_quoted (char *string, int *sindex, int allowesc)
{
  register int i;
  size_t slen;
  char *t;
  int pass_next;
  DECLARE_MBSTATE;

  /* Don't need slen for ADVANCE_CHAR unless multibyte chars possible. */
  slen = (MB_CUR_MAX > 1) ? strlen (string + *sindex) + *sindex : 0;
  i = *sindex;
  pass_next = 0;
  while (string[i])
    {
      if (pass_next)
	{
	  pass_next = 0;
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      if (allowesc && string[i] == '\\')
	pass_next++;
      else if (string[i] == '\'')
        break;
      ADVANCE_CHAR (string, slen, i);
    }

  t = substring (string, *sindex, i);

  if (string[i])
    i++;
  *sindex = i;

  return (t);
}

/* Skip over a single-quoted string.  We overload the SX_COMPLETE flag to mean
   that we are splitting out words for completion and have encountered a $'...'
   string, which allows backslash-escaped single quotes. */
int
skip_single_quoted (const char *string, size_t slen, int sind, int flags)
{
  register int c;
  DECLARE_MBSTATE;

  c = sind;
  while (string[c] && string[c] != '\'')
    {
      if ((flags & SX_COMPLETE) && string[c] == '\\' && string[c+1] == '\'' && string[c+2])
	ADVANCE_CHAR (string, slen, c);
      ADVANCE_CHAR (string, slen, c);
    }

  if (string[c])
    c++;
  return c;
}

/* Just like string_extract, but doesn't hack backslashes or any of
   that other stuff.  Obeys CTLESC quoting.  Used to do splitting on $IFS. */
char *
string_extract_verbatim (char *string, size_t slen, int *sindex, char *charlist, int flags)
{
  register int i;
#if defined (HANDLE_MULTIBYTE)
  wchar_t *wcharlist;
#endif
  int c;
  char *temp;
  DECLARE_MBSTATE;

  if ((flags & SX_NOCTLESC) && charlist[0] == '\'' && charlist[1] == '\0')
    {
      temp = string_extract_single_quoted (string, sindex, 0);
      --*sindex;	/* leave *sindex at separator character */
      return temp;
    }

  /* This can never be called with charlist == NULL. If *charlist == NULL,
     we can skip the loop and just return a copy of the string, updating
     *sindex */
  if (*charlist == 0)
    {
      temp = string + *sindex;
      c = (*sindex == 0) ? slen : STRLEN (temp);
      temp = savestring (temp);
      *sindex += c;
      return temp;
    }

  i = *sindex;
#if defined (HANDLE_MULTIBYTE)
  wcharlist = 0;
#endif
  while (c = string[i])
    {
#if defined (HANDLE_MULTIBYTE)
      size_t mblength;
#endif
      if ((flags & SX_NOCTLESC) == 0 && c == CTLESC)
	{
	  i += 2;
	  CHECK_STRING_OVERRUN (i, i, slen, c);
	  continue;
	}
      /* Even if flags contains SX_NOCTLESC, we let CTLESC quoting CTLNUL
	 through, to protect the CTLNULs from later calls to
	 remove_quoted_nulls. */
      else if ((flags & SX_NOESCCTLNUL) == 0 && c == CTLESC && string[i+1] == CTLNUL)
	{
	  i += 2;
	  CHECK_STRING_OVERRUN (i, i, slen, c);
	  continue;
	}

#if defined (HANDLE_MULTIBYTE)
      if (locale_utf8locale && slen > i && UTF8_SINGLEBYTE (string[i]))
	mblength = (string[i] != 0) ? 1 : 0;
      else
	mblength = MBLEN (string + i, slen - i);
      if (mblength > 1)
	{
	  wchar_t wc;
	  mblength = mbtowc (&wc, string + i, slen - i);
	  if (MB_INVALIDCH (mblength))
	    {
	      if (MEMBER (c, charlist))
		break;
	    }
	  else
	    {
	      if (wcharlist == 0)
		{
		  size_t len;
		  len = mbstowcs (wcharlist, charlist, 0);
		  if (len == -1)
		    len = 0;
		  wcharlist = (wchar_t *)xmalloc (sizeof (wchar_t) * (len + 1));
		  mbstowcs (wcharlist, charlist, len + 1);
		}

	      if (wcschr (wcharlist, wc))
		break;
	    }
	}
      else		
#endif
      if (MEMBER (c, charlist))
	break;

      ADVANCE_CHAR (string, slen, i);
    }

#if defined (HANDLE_MULTIBYTE)
  FREE (wcharlist);
#endif

  temp = substring (string, *sindex, i);
  *sindex = i;

  return (temp);
}

/* Extract the $( construct in STRING, and return a new string.
   Start extracting at (SINDEX) as if we had just seen "$(".
   Make (SINDEX) get the position of the matching ")". )
   XFLAGS is additional flags to pass to other extraction functions. */
char *
extract_command_subst (char *string, int *sindex, int xflags)
{
  char *ret;

  if (string[*sindex] == LPAREN || (xflags & SX_COMPLETE))
    return (extract_delimited_string (string, sindex, "$(", "(", ")", xflags|SX_COMMAND)); /*)*/
  else
    {
      xflags |= (no_longjmp_on_fatal_error ? SX_NOLONGJMP : 0);
      ret = xparse_dolparen (string, string+*sindex, sindex, xflags);
      return ret;
    }
}

/* Extract the $[ construct in STRING, and return a new string. (])
   Start extracting at (SINDEX) as if we had just seen "$[".
   Make (SINDEX) get the position of the matching "]". */
char *
extract_arithmetic_subst (char *string, int *sindex)
{
  return (extract_delimited_string (string, sindex, "$[", "[", "]", 0)); /*]*/
}

#if defined (PROCESS_SUBSTITUTION)
/* Extract the <( or >( construct in STRING, and return a new string.
   Start extracting at (SINDEX) as if we had just seen "<(".
   Make (SINDEX) get the position of the matching ")". */ /*))*/
char *
extract_process_subst (char *string, char *starter, int *sindex, int xflags)
{
#if 0
  /* XXX - check xflags&SX_COMPLETE here? */
  return (extract_delimited_string (string, sindex, starter, "(", ")", SX_COMMAND));
#else
  xflags |= (no_longjmp_on_fatal_error ? SX_NOLONGJMP : 0);
  return (xparse_dolparen (string, string+*sindex, sindex, xflags));
#endif
}
#endif /* PROCESS_SUBSTITUTION */

#if defined (ARRAY_VARS)
/* This can be fooled by unquoted right parens in the passed string. If
   each caller verifies that the last character in STRING is a right paren,
   we don't even need to call extract_delimited_string. */
char *
extract_array_assignment_list (char *string, int *sindex)
{
  int slen;
  char *ret;

  slen = strlen (string);
  if (string[slen - 1] == RPAREN)
   {
      ret = substring (string, *sindex, slen - 1);
      *sindex = slen - 1;
      return ret;
    }
  return 0;  
}
#endif

/* Extract and create a new string from the contents of STRING, a
   character string delimited with OPENER and CLOSER.  SINDEX is
   the address of an int describing the current offset in STRING;
   it should point to just after the first OPENER found.  On exit,
   SINDEX gets the position of the last character of the matching CLOSER.
   If OPENER is more than a single character, ALT_OPENER, if non-null,
   contains a character string that can also match CLOSER and thus
   needs to be skipped. */
static char *
extract_delimited_string (char *string, int *sindex, char *opener, char *alt_opener, char *closer, int flags)
{
  int i, c, si;
  size_t slen;
  char *t, *result;
  int pass_character, nesting_level, in_comment;
  int len_closer, len_opener, len_alt_opener;
  DECLARE_MBSTATE;

  slen = strlen (string + *sindex) + *sindex;
  len_opener = STRLEN (opener);
  len_alt_opener = STRLEN (alt_opener);
  len_closer = STRLEN (closer);

  pass_character = in_comment = 0;

  nesting_level = 1;
  i = *sindex;

  while (nesting_level)
    {
      c = string[i];

      /* If a recursive call or a call to ADVANCE_CHAR leaves the index beyond
	 the end of the string, catch it and cut the loop. */
      if (i > slen)
	{
	  i = slen;
	  c = string[i = slen];
	  break;
	}

      if (c == 0)
	break;

      if (in_comment)
	{
	  if (c == '\n')
	    in_comment = 0;
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}

      if (pass_character)	/* previous char was backslash */
	{
	  pass_character = 0;
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}

      /* Not exactly right yet; should handle shell metacharacters and
	 multibyte characters, too.  See COMMENT_BEGIN define in parse.y */
      if ((flags & SX_COMMAND) && c == '#' && (i == 0 || string[i - 1] == '\n' || shellblank (string[i - 1])))
	{
          in_comment = 1;
          ADVANCE_CHAR (string, slen, i);
          continue;
	}
        
      if (c == CTLESC || c == '\\')
	{
	  pass_character++;
	  i++;
	  continue;
	}

      /* Process a nested command substitution, but only if we're parsing an
	 arithmetic substitution. */
      if ((flags & SX_COMMAND) && string[i] == '$' && string[i+1] == LPAREN)
        {
          si = i + 2;
          t = extract_command_subst (string, &si, flags|SX_NOALLOC);
          CHECK_STRING_OVERRUN (i, si, slen, c);
          i = si + 1;
          continue;
        }

      /* Process a nested OPENER. */
      if (STREQN (string + i, opener, len_opener))
	{
	  si = i + len_opener;
	  t = extract_delimited_string (string, &si, opener, alt_opener, closer, flags|SX_NOALLOC);
	  CHECK_STRING_OVERRUN (i, si, slen, c);
	  i = si + 1;
	  continue;
	}

      /* Process a nested ALT_OPENER */
      if (len_alt_opener && STREQN (string + i, alt_opener, len_alt_opener))
	{
	  si = i + len_alt_opener;
	  t = extract_delimited_string (string, &si, alt_opener, alt_opener, closer, flags|SX_NOALLOC);
	  CHECK_STRING_OVERRUN (i, si, slen, c);
	  i = si + 1;
	  continue;
	}

      /* If the current substring terminates the delimited string, decrement
	 the nesting level. */
      if (STREQN (string + i, closer, len_closer))
	{
	  i += len_closer - 1;	/* move to last byte of the closer */
	  nesting_level--;
	  if (nesting_level == 0)
	    break;
	}

      /* Pass old-style command substitution through verbatim. */
      if (c == '`')
	{
	  si = i + 1;
	  t = string_extract (string, &si, "`", flags|SX_NOALLOC);
	  CHECK_STRING_OVERRUN (i, si, slen, c);
	  i = si + 1;
	  continue;
	}

      /* Pass single-quoted and double-quoted strings through verbatim. */
      if (c == '\'' || c == '"')
	{
	  si = i + 1;
	  i = (c == '\'') ? skip_single_quoted (string, slen, si, 0)
			  : skip_double_quoted (string, slen, si, 0);
	  continue;
	}

      /* move past this character, which was not special. */
      ADVANCE_CHAR (string, slen, i);
    }

  if (c == 0 && nesting_level)
    {
      if (no_longjmp_on_fatal_error == 0)
	{
	  last_command_exit_value = EXECUTION_FAILURE;
	  report_error (_("bad substitution: no closing `%s' in %s"), closer, string);
	  exp_jump_to_top_level (DISCARD);
	}
      else
	{
	  *sindex = i;
	  return (char *)NULL;
	}
    }

  si = i - *sindex - len_closer + 1;
  if (flags & SX_NOALLOC)
    result = (char *)NULL;
  else    
    {
      result = (char *)xmalloc (1 + si);
      strncpy (result, string + *sindex, si);
      result[si] = '\0';
    }
  *sindex = i;

  return (result);
}

/* A simplified version of extract_dollar_brace_string that exists to handle
   $'...' and $"..." quoting in here-documents, since the here-document read
   path doesn't. It's separate because we don't want to mess with the fast
   common path. We already know we're going to allocate and return a new
   string and quoted == Q_HERE_DOCUMENT. We might be able to cut it down
   some more, but extracting strings and adding them as we go adds complexity.
   This needs to match the logic in parse.y:parse_matched_pair so we get
   consistent behavior between here-documents and double-quoted strings. */
static char *
extract_heredoc_dolbrace_string (char *string, int *sindex, int quoted, int flags)
{
  register int i, c;
  size_t slen, tlen, result_index, result_size;
  int pass_character, nesting_level, si, dolbrace_state;
  char *result, *t, *send;
  DECLARE_MBSTATE;

  pass_character = 0;
  nesting_level = 1;
  slen = strlen (string + *sindex) + *sindex;
  send = string + slen;

  result_size = slen;
  result_index = 0;
  result = xmalloc (result_size + 1);

  /* This function isn't called if this condition is not true initially. */
  dolbrace_state = DOLBRACE_QUOTE;

  i = *sindex;
  while (c = string[i])
    {
      if (pass_character)
	{
	  pass_character = 0;
	  RESIZE_MALLOCED_BUFFER (result, result_index, locale_mb_cur_max + 1, result_size, 64);
	  COPY_CHAR_I (result, result_index, string, send, i);
	  continue;
	}

      /* CTLESCs and backslashes quote the next character. */
      if (c == CTLESC || c == '\\')
	{
	  pass_character++;
	  RESIZE_MALLOCED_BUFFER (result, result_index, 2, result_size, 64);
	  result[result_index++] = c;
	  i++;
	  continue;
	}

      /* The entire reason we have this separate function right here. */
      if (c == '$' && string[i+1] == '\'')
	{
	  char *ttrans;
	  int ttranslen;

	  if ((posixly_correct || extended_quote == 0) && dolbrace_state != DOLBRACE_QUOTE && dolbrace_state != DOLBRACE_QUOTE2)
	    {
	      RESIZE_MALLOCED_BUFFER (result, result_index, 3, result_size, 64);
	      result[result_index++] = '$';
	      result[result_index++] = '\'';
	      i += 2;
	      continue;
	    }

	  si = i + 2;
	  t = string_extract_single_quoted (string, &si, 1);	/* XXX */
	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  tlen = si - i - 2;	/* -2 since si is one after the close quote */
	  ttrans = ansiexpand (t, 0, tlen, &ttranslen);
	  free (t);

	  /* needed to correctly quote any embedded single quotes. */
	  if (dolbrace_state == DOLBRACE_QUOTE || dolbrace_state == DOLBRACE_QUOTE2)
	    {
	      t = sh_single_quote (ttrans);
	      tlen = strlen (t);
	      free (ttrans);
	    }
	  else if (extended_quote) /* dolbrace_state == DOLBRACE_PARAM */
	    {
	      /* This matches what parse.y:parse_matched_pair() does */
	      t = ttrans;
	      tlen = strlen (t);
	    }

	  RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 1, result_size, 64);
	  strncpy (result + result_index, t, tlen);
	  result_index += tlen;
	  free (t);
	  i = si;
	  continue;
	}

#if defined (TRANSLATABLE_STRINGS)
      if (c == '$' && string[i+1] == '"')
	{
	  char *ttrans;
	  int ttranslen;

	  si = i + 2;
	  t = string_extract_double_quoted (string, &si, flags);	/* XXX */
	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  tlen = si - i - 2;	/* -2 since si is one after the close quote */
	  ttrans = locale_expand (t, 0, tlen, line_number, &ttranslen);
	  free (t);

	  t = singlequote_translations ? sh_single_quote (ttrans) : sh_mkdoublequoted (ttrans, ttranslen, 0);
	  tlen = strlen (t);
	  free (ttrans);

	  RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 1, result_size, 64);
	  strncpy (result + result_index, t, tlen);
	  result_index += tlen;
	  free (t);
	  i = si;
	  continue;
	}
#endif /* TRANSLATABLE_STRINGS */

      if (c == '$' && string[i+1] == LBRACE)
	{
	  nesting_level++;
	  RESIZE_MALLOCED_BUFFER (result, result_index, 3, result_size, 64);
	  result[result_index++] = c;
	  result[result_index++] = string[i+1];
	  i += 2;
	  if (dolbrace_state == DOLBRACE_QUOTE || dolbrace_state == DOLBRACE_QUOTE2 || dolbrace_state == DOLBRACE_WORD)
	    dolbrace_state = DOLBRACE_PARAM;
	  continue;
	}

      if (c == RBRACE)
	{
	  nesting_level--;
	  if (nesting_level == 0)
	    break;
	  RESIZE_MALLOCED_BUFFER (result, result_index, 2, result_size, 64);
	  result[result_index++] = c;
	  i++;
	  continue;
	}

      /* Pass the contents of old-style command substitutions through
	 verbatim. */
      if (c == '`')
	{
	  si = i + 1;
	  t = string_extract (string, &si, "`", flags);	/* already know (flags & SX_NOALLOC) == 0) */
	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  tlen = si - i - 1;
	  RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 3, result_size, 64);
	  result[result_index++] = c;
	  strncpy (result + result_index, t, tlen);
	  result_index += tlen;
	  result[result_index++] = string[si];
	  free (t);
	  i = si + 1;
	  continue;
	}

      /* Pass the contents of new-style command substitutions and
	 arithmetic substitutions through verbatim. */
      if (string[i] == '$' && string[i+1] == LPAREN)
	{
	  si = i + 2;
	  t = extract_command_subst (string, &si, flags);
	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  tlen = si - i - 2;
	  RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 4, result_size, 64);
	  result[result_index++] = c;
	  result[result_index++] = LPAREN;
	  strncpy (result + result_index, t, tlen);
	  result_index += tlen;
	  result[result_index++] = string[si];
	  free (t);
	  i = si + 1;
	  continue;
	}

#if defined (PROCESS_SUBSTITUTION)
      /* Technically this should only work at the start of a word */
      if ((string[i] == '<' || string[i] == '>') && string[i+1] == LPAREN)
	{
	  si = i + 2;
	  t = extract_process_subst (string, (string[i] == '<' ? "<(" : ">)"), &si, flags);
	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  tlen = si - i - 2;
	  RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 4, result_size, 64);
	  result[result_index++] = c;
	  result[result_index++] = LPAREN;
	  strncpy (result + result_index, t, tlen);
	  result_index += tlen;
	  result[result_index++] = string[si];
	  free (t);
	  i = si + 1;
	  continue;
	}
#endif

      if (c == '\'' && posixly_correct && shell_compatibility_level > 42 && dolbrace_state != DOLBRACE_QUOTE)
	{
	  COPY_CHAR_I (result, result_index, string, send, i);
	  continue;
	}

      /* Pass the contents of single and double-quoted strings through verbatim. */
      if (c == '"' || c == '\'')
	{
	  si = i + 1;
	  if (c == '"')
	    t = string_extract_double_quoted (string, &si, flags);
	  else
	    t = string_extract_single_quoted (string, &si, 0);
	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  tlen = si - i - 2;	/* -2 since si is one after the close quote */
	  RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 3, result_size, 64);
	  result[result_index++] = c;
	  strncpy (result + result_index, t, tlen);
	  result_index += tlen;
	  result[result_index++] = string[si - 1];
	  free (t);
	  i = si;
	  continue;
	}

      /* copy this character, which was not special. */
      COPY_CHAR_I (result, result_index, string, send, i);

      /* This logic must agree with parse.y:parse_matched_pair, since they
	 share the same defines. */
      if (dolbrace_state == DOLBRACE_PARAM && c == '%' && (i - *sindex) > 1)
	dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == '#' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == '/' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE2;	/* XXX */
      else if (dolbrace_state == DOLBRACE_PARAM && c == '^' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == ',' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      /* This is intended to handle all of the [:]op expansions and the substring/
	 length/pattern removal/pattern substitution expansions. */
      else if (dolbrace_state == DOLBRACE_PARAM && strchr ("#%^,~:-=?+/", c) != 0)
	dolbrace_state = DOLBRACE_OP;
      else if (dolbrace_state == DOLBRACE_OP && strchr ("#%^,~:-=?+/", c) == 0)
	dolbrace_state = DOLBRACE_WORD;
    }

  if (c == 0 && nesting_level)
    {
      free (result);
      if (no_longjmp_on_fatal_error == 0)
	{			/* { */
	  last_command_exit_value = EXECUTION_FAILURE;
	  report_error (_("bad substitution: no closing `%s' in %s"), "}", string);
	  exp_jump_to_top_level (DISCARD);
	}
      else
	{
	  *sindex = i;
	  return ((char *)NULL);
	}
    }

  *sindex = i;
  result[result_index] = '\0';

  return (result);
}

#define PARAMEXPNEST_MAX	32	// for now
static int dbstate[PARAMEXPNEST_MAX];

/* Extract a parameter expansion expression within ${ and } from STRING.
   Obey the Posix.2 rules for finding the ending `}': count braces while
   skipping over enclosed quoted strings and command substitutions.
   SINDEX is the address of an int describing the current offset in STRING;
   it should point to just after the first `{' found.  On exit, SINDEX
   gets the position of the matching `}'.  QUOTED is non-zero if this
   occurs inside double quotes. */
/* XXX -- this is very similar to extract_delimited_string -- XXX */
char *
extract_dollar_brace_string (char *string, int *sindex, int quoted, int flags)
{
  register int i, c;
  size_t slen;
  int pass_character, nesting_level, si, dolbrace_state;
  char *result, *t;
  DECLARE_MBSTATE;

  /* The handling of dolbrace_state needs to agree with the code in parse.y:
     parse_matched_pair().  The different initial value is to handle the
     case where this function is called to parse the word in
     ${param op word} (SX_WORD). */
  dolbrace_state = (flags & SX_WORD) ? DOLBRACE_WORD : DOLBRACE_PARAM;
  if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && (flags & SX_POSIXEXP))
    dolbrace_state = DOLBRACE_QUOTE;

  if (quoted == Q_HERE_DOCUMENT && dolbrace_state == DOLBRACE_QUOTE && (flags & SX_NOALLOC) == 0)
    return (extract_heredoc_dolbrace_string (string, sindex, quoted, flags));

  dbstate[0] = dolbrace_state;

  pass_character = 0;
  nesting_level = 1;
  slen = strlen (string + *sindex) + *sindex;

  i = *sindex;
  while (c = string[i])
    {
      if (pass_character)
	{
	  pass_character = 0;
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}

      /* CTLESCs and backslashes quote the next character. */
      if (c == CTLESC || c == '\\')
	{
	  pass_character++;
	  i++;
	  continue;
	}

      if (string[i] == '$' && string[i+1] == LBRACE)
	{
	  if (nesting_level < PARAMEXPNEST_MAX)
	    dbstate[nesting_level] = dolbrace_state;
	  nesting_level++;
	  i += 2;
	  if (dolbrace_state == DOLBRACE_QUOTE || dolbrace_state == DOLBRACE_WORD)
	    dolbrace_state = DOLBRACE_PARAM;
	  continue;
	}

      if (c == RBRACE)
	{
	  nesting_level--;
	  if (nesting_level == 0)
	    break;
	  dolbrace_state = (nesting_level < PARAMEXPNEST_MAX) ? dbstate[nesting_level] : dbstate[0];	/* Guess using initial state */
	  i++;
	  continue;
	}

      /* Pass the contents of old-style command substitutions through
	 verbatim. */
      if (c == '`')
	{
	  si = i + 1;
	  t = string_extract (string, &si, "`", flags|SX_NOALLOC);

	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  i = si + 1;
	  continue;
	}

      /* Pass the contents of new-style command substitutions and
	 arithmetic substitutions through verbatim. */
      if (string[i] == '$' && string[i+1] == LPAREN)
	{
	  si = i + 2;
	  t = extract_command_subst (string, &si, flags|SX_NOALLOC);

	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  i = si + 1;
	  continue;
	}

#if defined (PROCESS_SUBSTITUTION)
      /* Technically this should only work at the start of a word */
      if ((string[i] == '<' || string[i] == '>') && string[i+1] == LPAREN)
	{
	  si = i + 2;
	  t = extract_process_subst (string, (string[i] == '<' ? "<(" : ">)"), &si, flags|SX_NOALLOC);

	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  i = si + 1;
	  continue;
	}
#endif

      /* Pass the contents of double-quoted strings through verbatim. */
      if (c == '"')
	{
	  si = i + 1;
	  i = skip_double_quoted (string, slen, si, 0);
	  /* skip_XXX_quoted leaves index one past close quote */
	  continue;
	}

      if (c == '\'')
	{
/*itrace("extract_dollar_brace_string: c == single quote flags = %d quoted = %d dolbrace_state = %d", flags, quoted, dolbrace_state);*/
	  if (posixly_correct && shell_compatibility_level > 42 && dolbrace_state != DOLBRACE_QUOTE && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
	    ADVANCE_CHAR (string, slen, i);
	  else
	    {
	      si = i + 1;
	      i = skip_single_quoted (string, slen, si, 0);
	    }

          continue;
	}

#if defined (ARRAY_VARS)
      if (c == LBRACK && dolbrace_state == DOLBRACE_PARAM)
	{
	  si = skipsubscript (string, i, 0);
	  CHECK_STRING_OVERRUN (i, si, slen, c);
	  if (string[si] == RBRACK)
	    c = string[i = si];
	}
#endif

      /* move past this character, which was not special. */
      ADVANCE_CHAR (string, slen, i);

      /* This logic must agree with parse.y:parse_matched_pair, since they
	 share the same defines. */
      if (dolbrace_state == DOLBRACE_PARAM && c == '%' && (i - *sindex) > 1)
	dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == '#' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == '/' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE2;	/* XXX */
      else if (dolbrace_state == DOLBRACE_PARAM && c == '^' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == ',' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      /* This is intended to handle all of the [:]op expansions and the substring/
	 length/pattern removal/pattern substitution expansions. */
      else if (dolbrace_state == DOLBRACE_PARAM && strchr ("#%^,~:-=?+/", c) != 0)
	dolbrace_state = DOLBRACE_OP;
      else if (dolbrace_state == DOLBRACE_OP && strchr ("#%^,~:-=?+/", c) == 0)
	dolbrace_state = DOLBRACE_WORD;
    }

  if (c == 0 && nesting_level)
    {
      if (no_longjmp_on_fatal_error == 0)
	{			/* { */
	  last_command_exit_value = EXECUTION_FAILURE;
	  report_error (_("bad substitution: no closing `%s' in %s"), "}", string);
	  exp_jump_to_top_level (DISCARD);
	}
      else
	{
	  *sindex = i;
	  return ((char *)NULL);
	}
    }

  result = (flags & SX_NOALLOC) ? (char *)NULL : substring (string, *sindex, i);
  *sindex = i;

  return (result);
}

/* Remove backslashes which are quoting backquotes from STRING.  Modifies
   STRING, and returns a pointer to it. */
char *
de_backslash (char *string)
{
  register size_t slen;
  register int i, j, prev_i;
  DECLARE_MBSTATE;

  slen = strlen (string);
  i = j = 0;

  /* Loop copying string[i] to string[j], i >= j. */
  while (i < slen)
    {
      if (string[i] == '\\' && (string[i + 1] == '`' || string[i + 1] == '\\' ||
			      string[i + 1] == '$'))
	i++;
      prev_i = i;
      ADVANCE_CHAR (string, slen, i);
      if (j < prev_i)
	do string[j++] = string[prev_i++]; while (prev_i < i);
      else
	j = i;
    }
  string[j] = '\0';

  return (string);
}

#if 0
/*UNUSED*/
/* Replace instances of \! in a string with !. */
void
unquote_bang (char *string)
{
  register int i, j;
  register char *temp;

  temp = (char *)xmalloc (1 + strlen (string));

  for (i = 0, j = 0; (temp[j] = string[i]); i++, j++)
    {
      if (string[i] == '\\' && string[i + 1] == '!')
	{
	  temp[j] = '!';
	  i++;
	}
    }
  strcpy (string, temp);
  free (temp);
}
#endif

#define CQ_RETURN(x) do { no_longjmp_on_fatal_error = oldjmp; return (x); } while (0)

/* When FLAGS & 2 == 0, this function assumes STRING[I] == OPEN; when
   FLAGS & 2 != 0, it assumes STRING[I] points to one character past OPEN;
   returns with STRING[RET] == close; used to parse array subscripts.
   FLAGS & 1 means not to attempt to skip over matched pairs of quotes or
   backquotes, or skip word expansions; it is intended to be used after
   expansion has been performed and during final assignment parsing (see
   arrayfunc.c:assign_compound_array_list()) or during execution by a builtin
   which has already undergone word expansion. */
static int
skip_matched_pair (const char *string, int start, int open, int close, int flags)
{
  int i, pass_next, backq, si, c, count, oldjmp;
  size_t slen;
  char *temp, *ss;
  DECLARE_MBSTATE;

  slen = strlen (string + start) + start;
  oldjmp = no_longjmp_on_fatal_error;
  no_longjmp_on_fatal_error = 1;

  /* Move to the first character after a leading OPEN. If FLAGS&2, we assume
    that START already points to that character. If not, we need to skip over
    it here. */
  i = (flags & 2) ? start : start + 1;
  count = 1;
  pass_next = backq = 0;
  ss = (char *)string;
  while (c = string[i])
    {
      if (pass_next)
	{
	  pass_next = 0;
	  if (c == 0)
	    CQ_RETURN(i);
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else if ((flags & 1) == 0 && c == '\\')
	{
	  pass_next = 1;
	  i++;
	  continue;
	}
      else if (backq)
	{
	  if (c == '`')
	    backq = 0;
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else if ((flags & 1) == 0 && c == '`')
	{
	  backq = 1;
	  i++;
	  continue;
	}
      else if ((flags & 1) == 0 && c == open)
	{
	  count++;
	  i++;
	  continue;
	}
      else if (c == close)
	{
	  count--;
	  if (count == 0)
	    break;
	  i++;
	  continue;
	}
      else if ((flags & 1) == 0 && (c == '\'' || c == '"'))
	{
	  i = (c == '\'') ? skip_single_quoted (ss, slen, ++i, 0)
			  : skip_double_quoted (ss, slen, ++i, 0);
	  /* no increment, the skip functions increment past the closing quote. */
	}
      else if ((flags & 1) == 0 && c == '$' && (string[i+1] == LPAREN || string[i+1] == LBRACE))
	{
	  si = i + 2;
	  if (string[si] == '\0')
	    CQ_RETURN(si);

	  /* XXX - extract_command_subst here? */
	  if (string[i+1] == LPAREN)
	    temp = extract_delimited_string (ss, &si, "$(", "(", ")", SX_NOALLOC|SX_COMMAND); /* ) */
	  else
	    temp = extract_dollar_brace_string (ss, &si, 0, SX_NOALLOC);

	  CHECK_STRING_OVERRUN (i, si, slen, c);

	  i = si;
	  if (string[i] == '\0')	/* don't increment i past EOS in loop */
	    break;
	  i++;
	  continue;
	}
      else
	ADVANCE_CHAR (string, slen, i);
    }

  CQ_RETURN(i);
}

#if defined (ARRAY_VARS)
/* FLAGS has 1 as a reserved value, since skip_matched_pair uses it for
   skipping over quoted strings and taking the first instance of the
   closing character. FLAGS & 2 means that STRING[START] points one
   character past the open bracket; FLAGS & 2 == 0 means that STRING[START]
   points to the open bracket. skip_matched_pair knows how to deal with this. */
int
skipsubscript (const char *string, int start, int flags)
{
  return (skip_matched_pair (string, start, '[', ']', flags));
}
#endif

/* Skip characters in STRING until we find a character in DELIMS, and return
   the index of that character.  START is the index into string at which we
   begin.  This is similar in spirit to strpbrk, but it returns an index into
   STRING and takes a starting index.  This little piece of code knows quite
   a lot of shell syntax.  It's very similar to skip_double_quoted and other
   functions of that ilk. */
int
skip_to_delim (char *string, int start, char *delims, int flags)
{
  int i, pass_next, backq, dquote, si, c, oldjmp;
  int invert, skipquote, skipcmd, noprocsub, completeflag;
  int arithexp, skipcol;
  size_t slen;
  char *temp, open[3];
  DECLARE_MBSTATE;

  slen = strlen (string + start) + start;
  oldjmp = no_longjmp_on_fatal_error;
  if (flags & SD_NOJMP)
    no_longjmp_on_fatal_error = 1;
  invert = (flags & SD_INVERT);
  skipcmd = (flags & SD_NOSKIPCMD) == 0;
  noprocsub = (flags & SD_NOPROCSUB);
  completeflag = (flags & SD_COMPLETE) ? SX_COMPLETE : 0;

  arithexp = (flags & SD_ARITHEXP);
  skipcol = 0;

  i = start;
  pass_next = backq = dquote = 0;
  while (c = string[i])
    {
      /* If this is non-zero, we should not let quote characters be delimiters
	 and the current character is a single or double quote.  We should not
	 test whether or not it's a delimiter until after we skip single- or
	 double-quoted strings. */
      skipquote = ((flags & SD_NOQUOTEDELIM) && (c == '\'' || c =='"'));
      if (pass_next)
	{
	  pass_next = 0;
	  if (c == 0)
	    CQ_RETURN(i);
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else if (c == '\\')
	{
	  pass_next = 1;
	  i++;
	  continue;
	}
      else if (backq)
	{
	  if (c == '`')
	    backq = 0;
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else if (c == '`')
	{
	  backq = 1;
	  i++;
	  continue;
	}
      else if (arithexp && skipcol && c == ':')
	{
	  skipcol--;
	  i++;
	  continue;
	}
      else if (arithexp && c == '?')
	{
	  skipcol++;
	  i++;
	  continue;
	}
      else if (skipquote == 0 && invert == 0 && member (c, delims))
	break;
      /* the usual case is to use skip_xxx_quoted, but we don't skip over double
	 quoted strings when looking for the history expansion character as a
	 delimiter. */
      /* special case for programmable completion which takes place before
         parser converts backslash-escaped single quotes between $'...' to
         `regular' single-quoted strings. */
      else if (completeflag && i > 0 && string[i-1] == '$' && c == '\'')
	i = skip_single_quoted (string, slen, ++i, SX_COMPLETE);
      else if (c == '\'')
	i = skip_single_quoted (string, slen, ++i, 0);
      else if (c == '"')
	i = skip_double_quoted (string, slen, ++i, completeflag);
      else if (c == LPAREN && arithexp)
        {
          si = i + 1;
          if (string[si] == '\0')
	    CQ_RETURN(si);

	  temp = extract_delimited_string (string, &si, "(", "(", ")", SX_NOALLOC); /* ) */
	  i = si;
	  if (string[i] == '\0')	/* don't increment i past EOS in loop */
	    break;
	  i++;
	  continue;         
        }
      else if (c == '$' && ((skipcmd && string[i+1] == LPAREN) || string[i+1] == LBRACE))
	{
	  si = i + 2;
	  if (string[si] == '\0')
	    CQ_RETURN(si);

	  if (string[i+1] == LPAREN)
	    temp = extract_delimited_string (string, &si, "$(", "(", ")", SX_NOALLOC|SX_COMMAND|completeflag); /* ) */
	  else
	    temp = extract_dollar_brace_string (string, &si, 0, SX_NOALLOC);
	  CHECK_STRING_OVERRUN (i, si, slen, c);
	  i = si;
	  if (string[i] == '\0')	/* don't increment i past EOS in loop */
	    break;
	  i++;
	  continue;
	}
#if defined (PROCESS_SUBSTITUTION)
      else if (skipcmd && noprocsub == 0 && (c == '<' || c == '>') && string[i+1] == LPAREN)
	{
	  si = i + 2;
	  if (string[si] == '\0')
	    CQ_RETURN(si);

	  temp = extract_delimited_string (string, &si, (c == '<') ? "<(" : ">(", "(", ")", SX_COMMAND|SX_NOALLOC); /* )) */
	  CHECK_STRING_OVERRUN (i, si, slen, c);
	  i = si;
	  if (string[i] == '\0')
	    break;
	  i++;
	  continue;
	}
#endif /* PROCESS_SUBSTITUTION */
#if defined (EXTENDED_GLOB)
      else if ((flags & SD_EXTGLOB) && extended_glob && string[i+1] == LPAREN && member (c, "?*+!@"))
	{
	  si = i + 2;
	  if (string[si] == '\0')
	    CQ_RETURN(si);

	  open[0] = c;
	  open[1] = LPAREN;
	  open[2] = '\0';
	  temp = extract_delimited_string (string, &si, open, "(", ")", SX_NOALLOC); /* ) */

	  CHECK_STRING_OVERRUN (i, si, slen, c);
	  i = si;
	  if (string[i] == '\0')	/* don't increment i past EOS in loop */
	    break;
	  i++;
	  continue;
	}
#endif
      else if ((flags & SD_GLOB) && c == LBRACK)
	{
	  si = i + 1;
	  if (string[si] == '\0')
	    CQ_RETURN(si);

	  temp = extract_delimited_string (string, &si, "[", "[", "]", SX_NOALLOC); /* ] */

	  i = si;
	  if (string[i] == '\0')	/* don't increment i past EOS in loop */
	    break;
	  i++;
	  continue;
	}
      else if ((skipquote || invert) && (member (c, delims) == 0))
	break;
      else
	ADVANCE_CHAR (string, slen, i);
    }

  CQ_RETURN(i);
}

#if defined (BANG_HISTORY)
/* Skip to the history expansion character (delims[0]), paying attention to
   quoted strings and command and process substitution.  This is a stripped-
   down version of skip_to_delims.  The essential difference is that this
   resets the quoting state when starting a command substitution */
int
skip_to_histexp (char *string, int start, char *delims, int flags)
{
  int i, pass_next, backq, dquote, c, oldjmp;
  int histexp_comsub, histexp_backq, old_dquote;
  size_t slen;
  DECLARE_MBSTATE;

  slen = strlen (string + start) + start;
  oldjmp = no_longjmp_on_fatal_error;
  if (flags & SD_NOJMP)
    no_longjmp_on_fatal_error = 1;

  histexp_comsub = histexp_backq = old_dquote = 0;

  i = start;
  pass_next = backq = dquote = 0;
  while (c = string[i])
    {
      if (pass_next)
	{
	  pass_next = 0;
	  if (c == 0)
	    CQ_RETURN(i);
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else if (c == '\\')
	{
	  pass_next = 1;
	  i++;
	  continue;
	}
      else if (backq && c == '`')
	{
	  backq = 0;
	  histexp_backq--;
	  dquote = old_dquote;
	  i++;
	  continue;
	}
      else if (c == '`')
	{
	  backq = 1;
	  histexp_backq++;
	  old_dquote = dquote;		/* simple - one level for now */
	  dquote = 0;
	  i++;
	  continue;
	}
      /* When in double quotes, act as if the double quote is a member of
	 history_no_expand_chars, like the history library does */
      else if (dquote && c == delims[0] && string[i+1] == '"')
	{
	  i++;
	  continue;
	}
      else if (c == delims[0])
	break;
      /* the usual case is to use skip_xxx_quoted, but we don't skip over double
	 quoted strings when looking for the history expansion character as a
	 delimiter. */
      else if (dquote && c == '\'')
        {
          i++;
          continue;
        }
      else if (c == '\'')
	i = skip_single_quoted (string, slen, ++i, 0);
      /* The posixly_correct test makes posix-mode shells allow double quotes
	 to quote the history expansion character */
      else if (posixly_correct == 0 && c == '"')
	{
	  dquote = 1 - dquote;
	  i++;
	  continue;
	}     
      else if (c == '"')
	i = skip_double_quoted (string, slen, ++i, 0);
#if defined (PROCESS_SUBSTITUTION)
      else if ((c == '$' || c == '<' || c == '>') && string[i+1] == LPAREN && string[i+2] != LPAREN)
#else
      else if (c == '$' && string[i+1] == LPAREN && string[i+2] != LPAREN)
#endif
        {
	  if (string[i+2] == '\0')
	    CQ_RETURN(i+2);
	  i += 2;
	  histexp_comsub++;
	  old_dquote = dquote;
	  dquote = 0;
        }
      else if (histexp_comsub && c == RPAREN)
	{
	  histexp_comsub--;
	  dquote = old_dquote;
	  i++;
	  continue;
	}
      else if (backq)		/* placeholder */
	{
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else
	ADVANCE_CHAR (string, slen, i);
    }

  CQ_RETURN(i);
}
#endif /* BANG_HISTORY */

#if defined (READLINE)
/* Return 1 if the portion of STRING ending at EINDEX is quoted (there is
   an unclosed quoted string), or if the character at EINDEX is quoted
   by a backslash. NO_LONGJMP_ON_FATAL_ERROR is used to flag that the various
   single and double-quoted string parsing functions should not return an
   error if there are unclosed quotes or braces.  The characters that this
   recognizes need to be the same as the contents of
   rl_completer_quote_characters. */

int
char_is_quoted (char *string, int eindex)
{
  int i, pass_next, c, oldjmp;
  size_t slen;
  DECLARE_MBSTATE;

  slen = strlen (string);
  oldjmp = no_longjmp_on_fatal_error;
  no_longjmp_on_fatal_error = 1;
  i = pass_next = 0;

  /* If we have an open quoted string from a previous line, see if it's
     closed before string[eindex], so we don't interpret that close quote
     as starting a new quoted string. */
  if (current_command_line_count > 0 && dstack.delimiter_depth > 0)
    {
      c = dstack.delimiters[dstack.delimiter_depth - 1];
      if (c == '\'')
	i = skip_single_quoted (string, slen, 0, 0);
      else if (c == '"')
	i = skip_double_quoted (string, slen, 0, SX_COMPLETE);
      if (i > eindex)
	CQ_RETURN (1);
    }

  while (i <= eindex)
    {
      c = string[i];

      if (pass_next)
	{
	  pass_next = 0;
	  if (i >= eindex)	/* XXX was if (i >= eindex - 1) */
	    CQ_RETURN(1);
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else if (c == '\\')
	{
	  pass_next = 1;
	  i++;
	  continue;
	}
      else if (c == '$' && string[i+1] == '\'' && string[i+2])
	{
	  i += 2;
	  i = skip_single_quoted (string, slen, i, SX_COMPLETE);
	  if (i > eindex)
	    CQ_RETURN (i);
	}
      else if (c == '\'' || c == '"')
	{
	  i = (c == '\'') ? skip_single_quoted (string, slen, ++i, 0)
			  : skip_double_quoted (string, slen, ++i, SX_COMPLETE);
	  if (i > eindex)
	    CQ_RETURN(1);
	  /* no increment, the skip_xxx functions go one past end */
	}
      else
	ADVANCE_CHAR (string, slen, i);
    }

  CQ_RETURN(0);
}

int
unclosed_pair (char *string, int eindex, char *openstr)
{
  int i, pass_next, openc, olen;
  size_t slen;
  DECLARE_MBSTATE;

  slen = strlen (string);
  olen = strlen (openstr);
  i = pass_next = openc = 0;
  while (i <= eindex)
    {
      if (pass_next)
	{
	  pass_next = 0;
	  if (i >= eindex)	/* XXX was if (i >= eindex - 1) */
	    return 0;
	  ADVANCE_CHAR (string, slen, i);
	  continue;
	}
      else if (string[i] == '\\')
	{
	  pass_next = 1;
	  i++;
	  continue;
	}
      else if (STREQN (string + i, openstr, olen))
	{
	  openc = 1 - openc;
	  i += olen;
	}
      /* XXX - may want to handle $'...' specially here */
      else if (string[i] == '\'' || string[i] == '"')
	{
	  i = (string[i] == '\'') ? skip_single_quoted (string, slen, i, 0)
				  : skip_double_quoted (string, slen, i, SX_COMPLETE);
	  if (i > eindex)
	    return 0;
	}
      else
	ADVANCE_CHAR (string, slen, i);
    }
  return (openc);
}

/* Split STRING (length SLEN) at DELIMS, and return a WORD_LIST with the
   individual words.  If DELIMS is NULL, the current value of $IFS is used
   to split the string, and the function follows the shell field splitting
   rules.  SENTINEL is an index to look for.  NWP, if non-NULL,
   gets the number of words in the returned list.  CWP, if non-NULL, gets
   the index of the word containing SENTINEL.  Non-whitespace chars in
   DELIMS delimit separate fields.  This is used by programmable completion. */
WORD_LIST *
split_at_delims (char *string, int slen, const char *delims, int sentinel, int flags, int *nwp, int *cwp)
{
  int ts, te, i, nw, cw, ifs_split, dflags;
  char *token, *d, *d2;
  WORD_LIST *ret, *tl;

  if (string == 0 || *string == '\0')
    {
      if (nwp)
	*nwp = 0;
      if (cwp)
	*cwp = 0;	
      return ((WORD_LIST *)NULL);
    }

  d = (delims == 0) ? ifs_value : (char *)delims;
  ifs_split = delims == 0;

  /* Make d2 the non-whitespace characters in delims */
  d2 = 0;
  if (delims)
    {
      size_t slength;
#if defined (HANDLE_MULTIBYTE)
      size_t mblength = 1;
#endif
      DECLARE_MBSTATE;

      slength = strlen (delims);
      d2 = (char *)xmalloc (slength + 1);
      i = ts = 0;
      while (delims[i])
	{
#if defined (HANDLE_MULTIBYTE)
	  mbstate_t state_bak;
	  state_bak = state;
	  mblength = MBRLEN (delims + i, slength, &state);
	  if (MB_INVALIDCH (mblength))
	    state = state_bak;
	  else if (mblength > 1)
	    {
	      memcpy (d2 + ts, delims + i, mblength);
	      ts += mblength;
	      i += mblength;
	      slength -= mblength;
	      continue;
	    }
#endif
	  if (whitespace (delims[i]) == 0)
	    d2[ts++] = delims[i];

	  i++;
	  slength--;
	}
      d2[ts] = '\0';
    }

  ret = (WORD_LIST *)NULL;

  /* Remove sequences of whitespace characters at the start of the string, as
     long as those characters are delimiters. */
  for (i = 0; member (string[i], d) && spctabnl (string[i]); i++)
    ;
  if (string[i] == '\0')
    {
      FREE (d2);
      return (ret);
    }

  ts = i;
  nw = 0;
  cw = -1;
  dflags = flags|SD_NOJMP;
  while (1)
    {
      te = skip_to_delim (string, ts, d, dflags);

      /* If we have a non-whitespace delimiter character, use it to make a
	 separate field.  This is just about what $IFS splitting does and
	 is closer to the behavior of the shell parser. */
      if (ts == te && d2 && member (string[ts], d2))
	{
	  te = ts + 1;
	  /* If we're using IFS splitting, the non-whitespace delimiter char
	     and any additional IFS whitespace delimits a field. */
	  if (ifs_split)
	    while (member (string[te], d) && spctabnl (string[te]) && ((flags&SD_NOQUOTEDELIM) == 0 || (string[te] != '\'' && string[te] != '"')))
	      te++;
	  else
	    while (member (string[te], d2) && ((flags&SD_NOQUOTEDELIM) == 0 || (string[te] != '\'' && string[te] != '"')))
	      te++;
	}

      token = substring (string, ts, te);

      ret = add_string_to_list (token, ret);	/* XXX */
      free (token);
      nw++;

      if (sentinel >= ts && sentinel <= te)
	cw = nw;

      /* If the cursor is at whitespace just before word start, set the
	 sentinel word to the current word. */
      if (cwp && cw == -1 && sentinel == ts-1)
	cw = nw;

      /* If the cursor is at whitespace between two words, make a new, empty
	 word, add it before (well, after, since the list is in reverse order)
	 the word we just added, and set the current word to that one. */
      if (cwp && cw == -1 && sentinel < ts)
	{
	  tl = make_word_list (make_word (""), ret->next);
	  ret->next = tl;
	  cw = nw;
	  nw++;
	}

      if (string[te] == 0)
	break;

      i = te;
      /* XXX - honor SD_NOQUOTEDELIM here */
      while (member (string[i], d) && (ifs_split || spctabnl(string[i])) && ((flags&SD_NOQUOTEDELIM) == 0 || (string[te] != '\'' && string[te] != '"')))
	i++;

      if (string[i])
	ts = i;
      else
	break;
    }

  /* Special case for SENTINEL at the end of STRING.  If we haven't found
     the word containing SENTINEL yet, and the index we're looking for is at
     the end of STRING (or past the end of the previously-found token,
     possible if the end of the line is composed solely of IFS whitespace)
     add an additional null argument and set the current word pointer to that. */
  if (cwp && cw == -1 && (sentinel >= slen || sentinel >= te))
    {
      if (whitespace (string[sentinel - 1]))
	{
	  token = "";
	  ret = add_string_to_list (token, ret);
	  nw++;
	}
      cw = nw;
    }

  if (nwp)
    *nwp = nw;
  if (cwp)
    *cwp = cw;

  FREE (d2);

  return (REVERSE_LIST (ret, WORD_LIST *));
}
#endif /* READLINE */

#if 0
/* UNUSED */
/* Extract the name of the variable to bind to from the assignment string. */
char *
assignment_name (char *string)
{
  int offset;
  char *temp;

  offset = assignment (string, 0);
  if (offset == 0)
    return (char *)NULL;
  temp = substring (string, 0, offset);
  return (temp);
}
#endif
