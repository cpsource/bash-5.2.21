/* subst_pattern.c -- Pattern matching and substitution, extracted from subst.c */

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
#  include <mbstr.h>		/* mbschr */
#endif
#include "typemax.h"

#include "builtins/getopt.h"
#include "builtins/common.h"

#include "builtins/builtext.h"

#include <tilde/tilde.h>
#include <glob/strmatch.h>

#include "subst.h"
#include "subst_quote.h"
#include "subst_pattern.h"
#include "subst_extract.h"

/* Constants from subst.c -- variable types returned by get_var_and_type */
#define VT_VARIABLE	0
#define VT_POSPARMS	1
#define VT_ARRAYVAR	2
#define VT_ARRAYMEMBER	3
#define VT_STARSUB	128	/* $* or ${array[*]} -- used to split */

#define LPAREN		'('
#define WLPAREN		L'('

/* EXPFUNC type from subst.c */
typedef WORD_LIST *EXPFUNC PARAMS((char *, int));

/* Functions defined in subst.c that we call */
extern char *expand_string_for_patsub PARAMS((char *, int));
extern char *expand_string_if_necessary PARAMS((char *, int, EXPFUNC *));
extern char *expand_string_to_string_internal PARAMS((char *, int, EXPFUNC *));
extern WORD_LIST *expand_string_for_pat PARAMS((char *, int, int *, int *));
extern int get_var_and_type PARAMS((char *, char *, array_eltstate_t *, int, int, SHELL_VAR **, char **));

/* **************************************************************** */
/*								    */
/*	   Functions for Matching and Removing Patterns		    */
/*								    */
/* **************************************************************** */

#if defined (HANDLE_MULTIBYTE)
# ifdef INCLUDE_UNUSED
static unsigned char *
mb_getcharlens (char *string, int len)
{
  int i, offset, last;
  unsigned char *ret;
  char *p;
  DECLARE_MBSTATE;

  i = offset = 0;
  last = 0;
  ret = (unsigned char *)xmalloc (len);
  memset (ret, 0, len);
  while (string[last])
    {
      ADVANCE_CHAR (string, len, offset);
      ret[last] = offset - last;
      last = offset;
    }
  return ret;
}
#  endif
#endif

/* Remove the portion of PARAM matched by PATTERN according to OP, where OP
   can have one of 4 values:
	RP_LONG_LEFT	remove longest matching portion at start of PARAM
	RP_SHORT_LEFT	remove shortest matching portion at start of PARAM
	RP_LONG_RIGHT	remove longest matching portion at end of PARAM
	RP_SHORT_RIGHT	remove shortest matching portion at end of PARAM
*/

#define RP_LONG_LEFT	1
#define RP_SHORT_LEFT	2
#define RP_LONG_RIGHT	3
#define RP_SHORT_RIGHT	4

/* Returns its first argument if nothing matched; new memory otherwise */
static char *
remove_upattern (char *param, char *pattern, int op)
{
  register size_t len;
  register char *end;
  register char *p, *ret, c;

  len = STRLEN (param);
  end = param + len;

  switch (op)
    {
      case RP_LONG_LEFT:	/* remove longest match at start */
	for (p = end; p >= param; p--)
	  {
	    c = *p; *p = '\0';
	    if (strmatch (pattern, param, FNMATCH_EXTFLAG) != FNM_NOMATCH)
	      {
		*p = c;
		return (savestring (p));
	      }
	    *p = c;

	  }
	break;

      case RP_SHORT_LEFT:	/* remove shortest match at start */
	for (p = param; p <= end; p++)
	  {
	    c = *p; *p = '\0';
	    if (strmatch (pattern, param, FNMATCH_EXTFLAG) != FNM_NOMATCH)
	      {
		*p = c;
		return (savestring (p));
	      }
	    *p = c;
	  }
	break;

      case RP_LONG_RIGHT:	/* remove longest match at end */
	for (p = param; p <= end; p++)
	  {
	    if (strmatch (pattern, p, FNMATCH_EXTFLAG) != FNM_NOMATCH)
	      {
		c = *p; *p = '\0';
		ret = savestring (param);
		*p = c;
		return (ret);
	      }
	  }
	break;

      case RP_SHORT_RIGHT:	/* remove shortest match at end */
	for (p = end; p >= param; p--)
	  {
	    if (strmatch (pattern, p, FNMATCH_EXTFLAG) != FNM_NOMATCH)
	      {
		c = *p; *p = '\0';
		ret = savestring (param);
		*p = c;
		return (ret);
	      }
	  }
	break;
    }

  return (param);	/* no match, return original string */
}

#if defined (HANDLE_MULTIBYTE)
/* Returns its first argument if nothing matched; new memory otherwise */
static wchar_t *
remove_wpattern (wchar_t *wparam, size_t wstrlen, wchar_t *wpattern, int op)
{
  wchar_t wc, *ret;
  int n;

  switch (op)
    {
      case RP_LONG_LEFT:	/* remove longest match at start */
        for (n = wstrlen; n >= 0; n--)
	  {
	    wc = wparam[n]; wparam[n] = L'\0';
	    if (wcsmatch (wpattern, wparam, FNMATCH_EXTFLAG) != FNM_NOMATCH)
	      {
		wparam[n] = wc;
		return (wcsdup (wparam + n));
	      }
	    wparam[n] = wc;
	  }
	break;

      case RP_SHORT_LEFT:	/* remove shortest match at start */
	for (n = 0; n <= wstrlen; n++)
	  {
	    wc = wparam[n]; wparam[n] = L'\0';
	    if (wcsmatch (wpattern, wparam, FNMATCH_EXTFLAG) != FNM_NOMATCH)
	      {
		wparam[n] = wc;
		return (wcsdup (wparam + n));
	      }
	    wparam[n] = wc;
	  }
	break;

      case RP_LONG_RIGHT:	/* remove longest match at end */
        for (n = 0; n <= wstrlen; n++)
	  {
	    if (wcsmatch (wpattern, wparam + n, FNMATCH_EXTFLAG) != FNM_NOMATCH)
	      {
		wc = wparam[n]; wparam[n] = L'\0';
		ret = wcsdup (wparam);
		wparam[n] = wc;
		return (ret);
	      }
	  }
	break;

      case RP_SHORT_RIGHT:	/* remove shortest match at end */
	for (n = wstrlen; n >= 0; n--)
	  {
	    if (wcsmatch (wpattern, wparam + n, FNMATCH_EXTFLAG) != FNM_NOMATCH)
	      {
		wc = wparam[n]; wparam[n] = L'\0';
		ret = wcsdup (wparam);
		wparam[n] = wc;
		return (ret);
	      }
	  }
	break;
    }

  return (wparam);	/* no match, return original string */
}
#endif /* HANDLE_MULTIBYTE */

static char *
remove_pattern (char *param, char *pattern, int op)
{
  char *xret;

  if (param == NULL)
    return (param);
  if (*param == '\0' || pattern == NULL || *pattern == '\0')	/* minor optimization */
    return (savestring (param));

#if defined (HANDLE_MULTIBYTE)
  if (MB_CUR_MAX > 1)
    {
      wchar_t *ret, *oret;
      size_t n;
      wchar_t *wparam, *wpattern;
      mbstate_t ps;

      /* XXX - could optimize here by checking param and pattern for multibyte
	 chars with mbsmbchar and calling remove_upattern. */

      n = xdupmbstowcs (&wpattern, NULL, pattern);
      if (n == (size_t)-1)
	{
	  xret = remove_upattern (param, pattern, op);
	  return ((xret == param) ? savestring (param) : xret);
	}
      n = xdupmbstowcs (&wparam, NULL, param);

      if (n == (size_t)-1)
	{
	  free (wpattern);
	  xret = remove_upattern (param, pattern, op);
	  return ((xret == param) ? savestring (param) : xret);
	}
      oret = ret = remove_wpattern (wparam, n, wpattern, op);
      /* Don't bother to convert wparam back to multibyte string if nothing
	 matched; just return copy of original string */
      if (ret == wparam)
        {
          free (wparam);
          free (wpattern);
          return (savestring (param));
        }

      free (wparam);
      free (wpattern);

      n = strlen (param);
      xret = (char *)xmalloc (n + 1);
      memset (&ps, '\0', sizeof (mbstate_t));
      n = wcsrtombs (xret, (const wchar_t **)&ret, n, &ps);
      xret[n] = '\0';		/* just to make sure */
      free (oret);
      return xret;      
    }
  else
#endif
    {
      xret = remove_upattern (param, pattern, op);
      return ((xret == param) ? savestring (param) : xret);
    }
}

/* Match PAT anywhere in STRING and return the match boundaries.
   This returns 1 in case of a successful match, 0 otherwise.  SP
   and EP are pointers into the string where the match begins and
   ends, respectively.  MTYPE controls what kind of match is attempted.
   MATCH_BEG and MATCH_END anchor the match at the beginning and end
   of the string, respectively.  The longest match is returned. */
static int
match_upattern (char *string, char *pat, int mtype, char **sp, char **ep)
{
  int c, mlen;
  size_t len;
  register char *p, *p1, *npat;
  char *end;

  /* If the pattern doesn't match anywhere in the string, go ahead and
     short-circuit right away.  A minor optimization, saves a bunch of
     unnecessary calls to strmatch (up to N calls for a string of N
     characters) if the match is unsuccessful.  To preserve the semantics
     of the substring matches below, we make sure that the pattern has
     `*' as first and last character, making a new pattern if necessary. */
  /* XXX - check this later if I ever implement `**' with special meaning,
     since this will potentially result in `**' at the beginning or end */
  len = STRLEN (pat);
  if (pat[0] != '*' || (pat[0] == '*' && pat[1] == LPAREN && extended_glob) || pat[len - 1] != '*')
    {
      int unescaped_backslash;
      char *pp;

      p = npat = (char *)xmalloc (len + 3);
      p1 = pat;
      if ((mtype != MATCH_BEG) && (*p1 != '*' || (*p1 == '*' && p1[1] == LPAREN && extended_glob)))
	*p++ = '*';
      while (*p1)
	*p++ = *p1++;
#if 1
      /* Need to also handle a pattern that ends with an unescaped backslash.
	 For right now, we ignore it because the pattern matching code will
	 fail the match anyway */
      /* If the pattern ends with a `*' we leave it alone if it's preceded by
	 an even number of backslashes, but if it's escaped by a backslash
	 we need to add another `*'. */
      if ((mtype != MATCH_END) && (p1[-1] == '*' && (unescaped_backslash = p1[-2] == '\\')))
	{
	  pp = p1 - 3;
	  while (pp >= pat && *pp-- == '\\')
	    unescaped_backslash = 1 - unescaped_backslash;
	  if (unescaped_backslash)
	    *p++ = '*';
	}
      else if (mtype != MATCH_END && p1[-1] != '*')
	*p++ = '*';
#else 
      if (p1[-1] != '*' || p1[-2] == '\\')
	*p++ = '*';
#endif
      *p = '\0';
    }
  else
    npat = pat;
  c = strmatch (npat, string, FNMATCH_EXTFLAG | FNMATCH_IGNCASE);
  if (npat != pat)
    free (npat);
  if (c == FNM_NOMATCH)
    return (0);

  len = STRLEN (string);
  end = string + len;

  mlen = umatchlen (pat, len);
  if (mlen > (int)len)
    return (0);

  switch (mtype)
    {
    case MATCH_ANY:
      for (p = string; p <= end; p++)
	{
	  if (match_pattern_char (pat, p, FNMATCH_IGNCASE))
	    {
	      p1 = (mlen == -1) ? end : p + mlen;
	      /* p1 - p = length of portion of string to be considered
	         p = current position in string
	         mlen = number of characters consumed by match (-1 for entire string)
	         end = end of string
	         we want to break immediately if the potential match len
	         is greater than the number of characters remaining in the
	         string
	      */
	      if (p1 > end)
		break;
	      for ( ; p1 >= p; p1--)
		{
		  c = *p1; *p1 = '\0';
		  if (strmatch (pat, p, FNMATCH_EXTFLAG | FNMATCH_IGNCASE) == 0)
		    {
		      *p1 = c;
		      *sp = p;
		      *ep = p1;
		      return 1;
		    }
		  *p1 = c;
#if 1
		  /* If MLEN != -1, we have a fixed length pattern. */
		  if (mlen != -1)
		    break;
#endif
		}
	    }
	}

      return (0);

    case MATCH_BEG:
      if (match_pattern_char (pat, string, FNMATCH_IGNCASE) == 0)
	return (0);

      for (p = (mlen == -1) ? end : string + mlen; p >= string; p--)
	{
	  c = *p; *p = '\0';
	  if (strmatch (pat, string, FNMATCH_EXTFLAG | FNMATCH_IGNCASE) == 0)
	    {
	      *p = c;
	      *sp = string;
	      *ep = p;
	      return 1;
	    }
	  *p = c;
	  /* If MLEN != -1, we have a fixed length pattern. */
	  if (mlen != -1)
	    break;
	}

      return (0);

    case MATCH_END:
      for (p = end - ((mlen == -1) ? len : mlen); p <= end; p++)
	{
	  if (strmatch (pat, p, FNMATCH_EXTFLAG | FNMATCH_IGNCASE) == 0)
	    {
	      *sp = p;
	      *ep = end;
	      return 1;
	    }
	  /* If MLEN != -1, we have a fixed length pattern. */
	  if (mlen != -1)
	    break;
	}

      return (0);
    }

  return (0);
}

#if defined (HANDLE_MULTIBYTE)

#define WFOLD(c) (match_ignore_case && iswupper (c) ? towlower (c) : (c))

/* Match WPAT anywhere in WSTRING and return the match boundaries.
   This returns 1 in case of a successful match, 0 otherwise.  Wide
   character version. */
static int
match_wpattern (wchar_t *wstring, char **indices, size_t wstrlen, wchar_t *wpat, int mtype, char **sp, char **ep)
{
  wchar_t wc, *wp, *nwpat, *wp1;
  size_t len;
  int mlen;
  int n, n1, n2, simple;

  simple = (wpat[0] != L'\\' && wpat[0] != L'*' && wpat[0] != L'?' && wpat[0] != L'[');
#if defined (EXTENDED_GLOB)
  if (extended_glob)
    simple &= (wpat[1] != L'(' || (wpat[0] != L'*' && wpat[0] != L'?' && wpat[0] != L'+' && wpat[0] != L'!' && wpat[0] != L'@')); /*)*/
#endif

  /* If the pattern doesn't match anywhere in the string, go ahead and
     short-circuit right away.  A minor optimization, saves a bunch of
     unnecessary calls to strmatch (up to N calls for a string of N
     characters) if the match is unsuccessful.  To preserve the semantics
     of the substring matches below, we make sure that the pattern has
     `*' as first and last character, making a new pattern if necessary. */
  len = wcslen (wpat);
  if (wpat[0] != L'*' || (wpat[0] == L'*' && wpat[1] == WLPAREN && extended_glob) || wpat[len - 1] != L'*')
    {
      int unescaped_backslash;
      wchar_t *wpp;

      wp = nwpat = (wchar_t *)xmalloc ((len + 3) * sizeof (wchar_t));
      wp1 = wpat;
      if (*wp1 != L'*' || (*wp1 == '*' && wp1[1] == WLPAREN && extended_glob))
	*wp++ = L'*';
      while (*wp1 != L'\0')
	*wp++ = *wp1++;
#if 1
      /* See comments above in match_upattern. */
      if (wp1[-1] == L'*' && (unescaped_backslash = wp1[-2] == L'\\'))
        {
          wpp = wp1 - 3;
          while (wpp >= wpat && *wpp-- == L'\\')
            unescaped_backslash = 1 - unescaped_backslash;
          if (unescaped_backslash)
            *wp++ = L'*';
        }
      else if (wp1[-1] != L'*')
        *wp++ = L'*';
#else      
      if (wp1[-1] != L'*' || wp1[-2] == L'\\')
        *wp++ = L'*';
#endif
      *wp = '\0';
    }
  else
    nwpat = wpat;
  len = wcsmatch (nwpat, wstring, FNMATCH_EXTFLAG | FNMATCH_IGNCASE);
  if (nwpat != wpat)
    free (nwpat);
  if (len == FNM_NOMATCH)
    return (0);

  mlen = wmatchlen (wpat, wstrlen);
  if (mlen > (int)wstrlen)
    return (0);

/* itrace("wmatchlen (%ls) -> %d", wpat, mlen); */
  switch (mtype)
    {
    case MATCH_ANY:
      for (n = 0; n <= wstrlen; n++)
	{
	  n2 = simple ? (WFOLD(*wpat) == WFOLD(wstring[n])) : match_pattern_wchar (wpat, wstring + n, FNMATCH_IGNCASE);
	  if (n2)
	    {
	      n1 = (mlen == -1) ? wstrlen : n + mlen;
	      if (n1 > wstrlen)
	        break;

	      for ( ; n1 >= n; n1--)
		{
		  wc = wstring[n1]; wstring[n1] = L'\0';
		  if (wcsmatch (wpat, wstring + n, FNMATCH_EXTFLAG | FNMATCH_IGNCASE) == 0)
		    {
		      wstring[n1] = wc;
		      *sp = indices[n];
		      *ep = indices[n1];
		      return 1;
		    }
		  wstring[n1] = wc;
		  /* If MLEN != -1, we have a fixed length pattern. */
		  if (mlen != -1)
		    break;
		}
	    }
	}

      return (0);

    case MATCH_BEG:
      if (match_pattern_wchar (wpat, wstring, FNMATCH_IGNCASE) == 0)
	return (0);

      for (n = (mlen == -1) ? wstrlen : mlen; n >= 0; n--)
	{
	  wc = wstring[n]; wstring[n] = L'\0';
	  if (wcsmatch (wpat, wstring, FNMATCH_EXTFLAG | FNMATCH_IGNCASE) == 0)
	    {
	      wstring[n] = wc;
	      *sp = indices[0];
	      *ep = indices[n];
	      return 1;
	    }
	  wstring[n] = wc;
	  /* If MLEN != -1, we have a fixed length pattern. */
	  if (mlen != -1)
	    break;
	}

      return (0);

    case MATCH_END:
      for (n = wstrlen - ((mlen == -1) ? wstrlen : mlen); n <= wstrlen; n++)
	{
	  if (wcsmatch (wpat, wstring + n, FNMATCH_EXTFLAG | FNMATCH_IGNCASE) == 0)
	    {
	      *sp = indices[n];
	      *ep = indices[wstrlen];
	      return 1;
	    }
	  /* If MLEN != -1, we have a fixed length pattern. */
	  if (mlen != -1)
	    break;
	}

      return (0);
    }

  return (0);
}
#undef WFOLD
#endif /* HANDLE_MULTIBYTE */

static int
match_pattern (char *string, char *pat, int mtype, char **sp, char **ep)
{
#if defined (HANDLE_MULTIBYTE)
  int ret;
  size_t n;
  wchar_t *wstring, *wpat;
  char **indices;
#endif

  if (string == 0 || pat == 0 || *pat == 0)
    return (0);

#if defined (HANDLE_MULTIBYTE)
  if (MB_CUR_MAX > 1)
    {
      if (mbsmbchar (string) == 0 && mbsmbchar (pat) == 0)
        return (match_upattern (string, pat, mtype, sp, ep));

      n = xdupmbstowcs (&wpat, NULL, pat);
      if (n == (size_t)-1)
	return (match_upattern (string, pat, mtype, sp, ep));
      n = xdupmbstowcs (&wstring, &indices, string);
      if (n == (size_t)-1)
	{
	  free (wpat);
	  return (match_upattern (string, pat, mtype, sp, ep));
	}
      ret = match_wpattern (wstring, indices, n, wpat, mtype, sp, ep);

      free (wpat);
      free (wstring);
      free (indices);

      return (ret);
    }
  else
#endif
    return (match_upattern (string, pat, mtype, sp, ep));
}

static int
getpatspec (int c, const char *value)
{
  if (c == '#')
    return ((*value == '#') ? RP_LONG_LEFT : RP_SHORT_LEFT);
  else	/* c == '%' */
    return ((*value == '%') ? RP_LONG_RIGHT : RP_SHORT_RIGHT);
}

/* Posix.2 says that the WORD should be run through tilde expansion,
   parameter expansion, command substitution and arithmetic expansion.
   This leaves the result quoted, so quote_string_for_globbing () has
   to be called to fix it up for strmatch ().  If QUOTED is non-zero,
   it means that the entire expression was enclosed in double quotes.
   This means that quoting characters in the pattern do not make any
   special pattern characters quoted.  For example, the `*' in the
   following retains its special meaning: "${foo#'*'}". */
char *
getpattern (char *value, int quoted, int expandpat)
{
  char *pat, *tword;
  WORD_LIST *l;
#if 0
  int i;
#endif
  /* There is a problem here:  how to handle single or double quotes in the
     pattern string when the whole expression is between double quotes?
     POSIX.2 says that enclosing double quotes do not cause the pattern to
     be quoted, but does that leave us a problem with @ and array[@] and their
     expansions inside a pattern? */
#if 0
  if (expandpat && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && *tword)
    {
      i = 0;
      pat = string_extract_double_quoted (tword, &i, SX_STRIPDQ);
      free (tword);
      tword = pat;
    }
#endif

  /* expand_string_for_pat () leaves WORD quoted and does not perform
     word splitting. */
  l = *value ? expand_string_for_pat (value,
				      (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) ? Q_PATQUOTE : quoted,
				      (int *)NULL, (int *)NULL)
	     : (WORD_LIST *)0;
  if (l)
    word_list_remove_quoted_nulls (l);
  pat = string_list (l);
  dispose_words (l);
  if (pat)
    {
      tword = quote_string_for_globbing (pat, QGLOB_CVTNULL);
      free (pat);
      pat = tword;
    }
  return (pat);
}

#if 0
/* Handle removing a pattern from a string as a result of ${name%[%]value}
   or ${name#[#]value}. */
static char *
variable_remove_pattern (char *value, char *pattern, int patspec, int quoted)
{
  char *tword;

  tword = remove_pattern (value, pattern, patspec);

  return (tword);
}
#endif

static char *
list_remove_pattern (WORD_LIST *list, char *pattern, int patspec, int itype, int quoted)
{
  WORD_LIST *new, *l;
  WORD_DESC *w;
  char *tword;

  for (new = (WORD_LIST *)NULL, l = list; l; l = l->next)
    {
      tword = remove_pattern (l->word->word, pattern, patspec);
      w = alloc_word_desc ();
      w->word = tword ? tword : savestring ("");
      new = make_word_list (w, new);
    }

  l = REVERSE_LIST (new, WORD_LIST *);
  tword = string_list_pos_params (itype, l, quoted, 0);
  dispose_words (l);

  return (tword);
}

static char *
parameter_list_remove_pattern (int itype, char *pattern, int patspec, int quoted)
{
  char *ret;
  WORD_LIST *list;

  list = list_rest_of_args ();
  if (list == 0)
    return ((char *)NULL);
  ret = list_remove_pattern (list, pattern, patspec, itype, quoted);
  dispose_words (list);
  return (ret);
}

#if defined (ARRAY_VARS)
static char *
array_remove_pattern (SHELL_VAR *var, char *pattern, int patspec, int starsub, int quoted)
{
  ARRAY *a;
  HASH_TABLE *h;
  int itype;
  char *ret;
  WORD_LIST *list;
  SHELL_VAR *v;

  v = var;		/* XXX - for now */

  itype = starsub ? '*' : '@';

  a = (v && array_p (v)) ? array_cell (v) : 0;
  h = (v && assoc_p (v)) ? assoc_cell (v) : 0;
  
  list = a ? array_to_word_list (a) : (h ? assoc_to_word_list (h) : 0);
  if (list == 0)
   return ((char *)NULL);
  ret = list_remove_pattern (list, pattern, patspec, itype, quoted);
  dispose_words (list);

  return ret;
}
#endif /* ARRAY_VARS */

char *
parameter_brace_remove_pattern (char *varname, char *value, array_eltstate_t *estatep, char *patstr, int rtype, int quoted, int flags)
{
  int vtype, patspec, starsub;
  char *temp1, *val, *pattern, *oname;
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

  patspec = getpatspec (rtype, patstr);
  if (patspec == RP_LONG_LEFT || patspec == RP_LONG_RIGHT)
    patstr++;

  /* Need to pass getpattern newly-allocated memory in case of expansion --
     the expansion code will free the passed string on an error. */
  temp1 = savestring (patstr);
  pattern = getpattern (temp1, quoted, 1);
  free (temp1);

  temp1 = (char *)NULL;		/* shut up gcc */
  switch (vtype)
    {
    case VT_VARIABLE:
    case VT_ARRAYMEMBER:
      temp1 = remove_pattern (val, pattern, patspec);
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
      temp1 = array_remove_pattern (v, pattern, patspec, starsub, quoted);
      if (temp1 && ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) == 0))
	{
	  val = quote_escapes (temp1);
	  free (temp1);
	  temp1 = val;
	}
      break;
#endif
    case VT_POSPARMS:
      temp1 = parameter_list_remove_pattern (varname[0], pattern, patspec, quoted);
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

  FREE (pattern);
  return temp1;
}    


/****************************************************************/
/*								*/
/* Functions to perform pattern substitution on variable values */
/*								*/
/****************************************************************/

static int
shouldexp_replacement (char *s)
{
  size_t slen;
  int sindex, c;
  DECLARE_MBSTATE;

  sindex = 0;
  slen = STRLEN (s);
  while (c = s[sindex])
    {
      if (c == '\\')
	{
	  sindex++;
	  if (s[sindex] == 0)
	    return 0;
	  /* We want to remove this backslash because we treat it as special
	     in this context. THIS ASSUMES THE STRING IS PROCESSED BY
	     strcreplace() OR EQUIVALENT that handles removing backslashes
	     preceding the special character. */
	  if (s[sindex] == '&')
	    return 1;
	  if (s[sindex] == '\\')
	    return 1;
	}
      else if (c == '&')
	return 1;
      ADVANCE_CHAR (s, slen, sindex);
    }
  return 0;
}

char *
pat_subst (char *string, char *pat, char *rep, int mflags)
{
  char *ret, *s, *e, *str, *rstr, *mstr, *send;
  int rptr, mtype, rxpand, mlen;
  size_t rsize, l, replen, rslen;
  DECLARE_MBSTATE;

  if (string == 0)
    return (savestring (""));

  mtype = mflags & MATCH_TYPEMASK;
  rxpand = mflags & MATCH_EXPREP;

  /* Special cases:
   * 	1.  A null pattern with mtype == MATCH_BEG means to prefix STRING
   *	    with REP and return the result.
   *	2.  A null pattern with mtype == MATCH_END means to append REP to
   *	    STRING and return the result.
   *	3.  A null STRING with a matching pattern means to append REP to
   *	    STRING and return the result.
   *
   * These process `&' in the replacement string, like `sed' does when
   * presented with a BRE of `^' or `$'.
   */
  if ((pat == 0 || *pat == 0) && (mtype == MATCH_BEG || mtype == MATCH_END))
    {
      rstr = (mflags & MATCH_EXPREP) ? strcreplace (rep, '&', "", 2) : rep;
      rslen = STRLEN (rstr);
      l = STRLEN (string);
      ret = (char *)xmalloc (rslen + l + 2);
      if (rslen == 0)
	strcpy (ret, string);
      else if (mtype == MATCH_BEG)
	{
	  strcpy (ret, rstr);
	  strcpy (ret + rslen, string);
	}
      else
	{
	  strcpy (ret, string);
	  strcpy (ret + l, rstr);
	}
      if (rstr != rep)
	free (rstr);
      return (ret);
    }
  else if (*string == 0 && (match_pattern (string, pat, mtype, &s, &e) != 0))
    return (mflags & MATCH_EXPREP) ? strcreplace (rep, '&', "", 2)
				   : (rep ? savestring (rep) : savestring (""));

  ret = (char *)xmalloc (rsize = 64);
  ret[0] = '\0';
  send = string + strlen (string);

  for (replen = STRLEN (rep), rptr = 0, str = string; *str;)
    {
      if (match_pattern (str, pat, mtype, &s, &e) == 0)
	break;
      l = s - str;

      if (rep && rxpand)
        {
	  int x;
	  mlen = e - s;
	  mstr = xmalloc (mlen + 1);
	  for (x = 0; x < mlen; x++)
	    mstr[x] = s[x];
	  mstr[mlen] = '\0';
	  rstr = strcreplace (rep, '&', mstr, 2);
	  free (mstr);
	  rslen = strlen (rstr);
        }
      else
	{
	  rstr = rep;
	  rslen = replen;
	}
        
      RESIZE_MALLOCED_BUFFER (ret, rptr, (l + rslen), rsize, 64);

      /* OK, now copy the leading unmatched portion of the string (from
	 str to s) to ret starting at rptr (the current offset).  Then copy
	 the replacement string at ret + rptr + (s - str).  Increment
	 rptr (if necessary) and str and go on. */
      if (l)
	{
	  strncpy (ret + rptr, str, l);
	  rptr += l;
	}
      if (replen)
	{
	  strncpy (ret + rptr, rstr, rslen);
	  rptr += rslen;
	}
      str = e;		/* e == end of match */

      if (rstr != rep)
	free (rstr);

      if (((mflags & MATCH_GLOBREP) == 0) || mtype != MATCH_ANY)
	break;

      if (s == e)
	{
	  /* On a zero-length match, make sure we copy one character, since
	     we increment one character to avoid infinite recursion. */
	  char *p, *origp, *origs;
	  size_t clen;

	  RESIZE_MALLOCED_BUFFER (ret, rptr, locale_mb_cur_max, rsize, 64);
#if defined (HANDLE_MULTIBYTE)
	  p = origp = ret + rptr;
	  origs = str;
	  COPY_CHAR_P (p, str, send);
	  rptr += p - origp;
	  e += str - origs;
#else
	  ret[rptr++] = *str++;
	  e++;		/* avoid infinite recursion on zero-length match */
#endif
	}
    }

  /* Now copy the unmatched portion of the input string */
  if (str && *str)
    {
      l = send - str + 1;
      RESIZE_MALLOCED_BUFFER (ret, rptr, l, rsize, 64);
      strcpy (ret + rptr, str);
    }
  else
    ret[rptr] = '\0';

  return ret;
}

/* Do pattern match and replacement on the positional parameters. */
static char *
pos_params_pat_subst (char *string, char *pat, char *rep, int mflags)
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
      ret = pat_subst (params->word->word, pat, rep, mflags);
      w = alloc_word_desc ();
      w->word = ret ? ret : savestring ("");
      dispose_word (params->word);
      params->word = w;
    }

  pchar = (mflags & MATCH_STARSUB) == MATCH_STARSUB ? '*' : '@';
  qflags = (mflags & MATCH_QUOTED) == MATCH_QUOTED ? Q_DOUBLE_QUOTES : 0;
  pflags = (mflags & MATCH_ASSIGNRHS) == MATCH_ASSIGNRHS ? PF_ASSIGNRHS : 0;

  /* If we are expanding in a context where word splitting will not be
     performed, treat as quoted. This changes how $* will be expanded. */
  if (pchar == '*' && (mflags & MATCH_ASSIGNRHS) && expand_no_split_dollar_star && ifs_is_null)
    qflags |= Q_DOUBLE_QUOTES;		/* Posix interp 888 */

  ret = string_list_pos_params (pchar, save, qflags, pflags);
  dispose_words (save);

  return (ret);
}

/* Perform pattern substitution on VALUE, which is the expansion of
   VARNAME.  PATSUB is an expression supplying the pattern to match
   and the string to substitute.  QUOTED is a flags word containing
   the type of quoting currently in effect. */
char *
parameter_brace_patsub (char *varname, char *value, array_eltstate_t *estatep, char *patsub, int quoted, int pflags, int flags)
{
  int vtype, mflags, starsub, delim;
  char *val, *temp, *pat, *rep, *p, *lpatsub, *tt, *oname;
  SHELL_VAR *v;

  if (value == 0)
    return ((char *)NULL);

  oname = this_command_name;
  this_command_name = varname;		/* error messages */

  vtype = get_var_and_type (varname, value, estatep, quoted, flags, &v, &val);
  if (vtype == -1)
    {
      this_command_name = oname;
      return ((char *)NULL);
    }

  starsub = vtype & VT_STARSUB;
  vtype &= ~VT_STARSUB;

  mflags = 0;
  /* PATSUB is never NULL when this is called. */
  if (*patsub == '/')
    {
      mflags |= MATCH_GLOBREP;
      patsub++;
    }

  /* Malloc this because expand_string_if_necessary or one of the expansion
     functions in its call chain may free it on a substitution error. */
  lpatsub = savestring (patsub);

  if (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES))
    mflags |= MATCH_QUOTED;

  if (starsub)
    mflags |= MATCH_STARSUB;

  if (pflags & PF_ASSIGNRHS)
    mflags |= MATCH_ASSIGNRHS;

  /* If the pattern starts with a `/', make sure we skip over it when looking
     for the replacement delimiter. */
  delim = skip_to_delim (lpatsub, ((*patsub == '/') ? 1 : 0), "/", 0);
  if (lpatsub[delim] == '/')
    {
      lpatsub[delim] = 0;
      rep = lpatsub + delim + 1;
    }
  else
    rep = (char *)NULL;

  if (rep && *rep == '\0')
    rep = (char *)NULL;

  /* Perform the same expansions on the pattern as performed by the
     pattern removal expansions. */
  pat = getpattern (lpatsub, quoted, 1);

  if (rep)
    {
      /* We want to perform quote removal on the expanded replacement even if
	 the entire expansion is double-quoted because the parser and string
	 extraction functions treated quotes in the replacement string as
	 special.  THIS IS NOT BACKWARDS COMPATIBLE WITH BASH-4.2. */
      if (shell_compatibility_level > 42 && patsub_replacement == 0)
	rep = expand_string_if_necessary (rep, quoted & ~(Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT), expand_string_unsplit);
      else if (shell_compatibility_level > 42 && patsub_replacement)
	rep = expand_string_for_patsub (rep, quoted & ~(Q_DOUBLE_QUOTES|Q_HERE_DOCUMENT));
      /* This is the bash-4.2 code. */      
      else if ((mflags & MATCH_QUOTED) == 0)
	rep = expand_string_if_necessary (rep, quoted, expand_string_unsplit);
      else
	rep = expand_string_to_string_internal (rep, quoted, expand_string_unsplit);

      /* Check whether or not to replace `&' in the replacement string after
	 expanding it, since we want to treat backslashes quoting the `&'
	 consistently. */
      if (patsub_replacement && rep && *rep && shouldexp_replacement (rep))
	mflags |= MATCH_EXPREP;

    }

  /* ksh93 doesn't allow the match specifier to be a part of the expanded
     pattern.  This is an extension.  Make sure we don't anchor the pattern
     at the beginning or end of the string if we're doing global replacement,
     though. */
  p = pat;
  if (mflags & MATCH_GLOBREP)
    mflags |= MATCH_ANY;
  else if (pat && pat[0] == '#')
    {
      mflags |= MATCH_BEG;
      p++;
    }
  else if (pat && pat[0] == '%')
    {
      mflags |= MATCH_END;
      p++;
    }
  else
    mflags |= MATCH_ANY;

  /* OK, we now want to substitute REP for PAT in VAL.  If
     flags & MATCH_GLOBREP is non-zero, the substitution is done
     everywhere, otherwise only the first occurrence of PAT is
     replaced.  The pattern matching code doesn't understand
     CTLESC quoting CTLESC and CTLNUL so we use the dequoted variable
     values passed in (VT_VARIABLE) so the pattern substitution
     code works right.  We need to requote special chars after
     we're done for VT_VARIABLE and VT_ARRAYMEMBER, and for the
     other cases if QUOTED == 0, since the posparams and arrays
     indexed by * or @ do special things when QUOTED != 0. */

  switch (vtype)
    {
    case VT_VARIABLE:
    case VT_ARRAYMEMBER:
      temp = pat_subst (val, p, rep, mflags);
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
      /* This does the right thing for the case where we are not performing
	 word splitting. MATCH_STARSUB restricts it to ${* /foo/bar}, and
	 pos_params_pat_subst/string_list_pos_params will do the right thing
	 in turn for the case where ifs_is_null. Posix interp 888 */
      if ((pflags & PF_NOSPLIT2) && (mflags & MATCH_STARSUB))
        mflags |= MATCH_ASSIGNRHS;
      temp = pos_params_pat_subst (val, p, rep, mflags);
      if (temp && quoted == 0 && ifs_is_null)
	{
	  /* Posix interp 888 */
	}
      else if (temp && quoted == 0 && (pflags & PF_ASSIGNRHS))
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

      /* these eventually call string_list_pos_params */
      if (assoc_p (v))
	temp = assoc_patsub (assoc_cell (v), p, rep, mflags);
      else
	temp = array_patsub (array_cell (v), p, rep, mflags);

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
  FREE (rep);
  free (lpatsub);

  this_command_name = oname;

  return temp;
}

