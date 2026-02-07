/* subst_quote.c -- Quoting/dequoting functions, extracted from subst.c */

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
#if defined (HAVE_UNISTD_H)
#  include <unistd.h>
#endif

#include "bashansi.h"
#include "bashintl.h"

#include "shell.h"
#include "syntax.h"
#include "parser.h"
#include "flags.h"
#include "execute_cmd.h"

#include "shmbutil.h"
#if defined (HAVE_MBSTR_H) && defined (HAVE_MBSCHR)
#  include <mbstr.h>		/* mbschr */
#endif

#include "subst.h"
#include "subst_quote.h"

/***************************************************
 *						   *
 *	Functions to handle quoting chars	   *
 *						   *
 ***************************************************/

/* Conventions:

     A string with s[0] == CTLNUL && s[1] == 0 is a quoted null string.
     The parser passes CTLNUL as CTLESC CTLNUL. */

/* Quote escape characters in string s, but no other characters.  This is
   used to protect CTLESC and CTLNUL in variable values from the rest of
   the word expansion process after the variable is expanded (word splitting
   and filename generation).  If IFS is null, we quote spaces as well, just
   in case we split on spaces later (in the case of unquoted $@, we will
   eventually attempt to split the entire word on spaces).  Corresponding
   code exists in dequote_escapes.  Even if we don't end up splitting on
   spaces, quoting spaces is not a problem.  This should never be called on
   a string that is quoted with single or double quotes or part of a here
   document (effectively double-quoted).
   FLAGS says whether or not we are going to split the result. If we are not,
   and there is a CTLESC or CTLNUL in IFS, we need to quote CTLESC and CTLNUL,
   respectively, to prevent them from being removed as part of dequoting. */
static char *
quote_escapes_internal (const char *string, int flags)
{
  const char *s, *send;
  char *t, *result;
  size_t slen;
  int quote_spaces, skip_ctlesc, skip_ctlnul, nosplit;
  DECLARE_MBSTATE;

  slen = strlen (string);
  send = string + slen;

  quote_spaces = (ifs_value && *ifs_value == 0);
  nosplit = (flags & PF_NOSPLIT2);

  for (skip_ctlesc = skip_ctlnul = 0, s = ifs_value; s && *s; s++)
    {
      skip_ctlesc |= (nosplit == 0 && *s == CTLESC);
      skip_ctlnul |= (nosplit == 0 && *s == CTLNUL);
    }

  t = result = (char *)xmalloc ((slen * 2) + 1);
  s = string;

  while (*s)
    {
      if ((skip_ctlesc == 0 && *s == CTLESC) || (skip_ctlnul == 0 && *s == CTLNUL) || (quote_spaces && *s == ' '))
	*t++ = CTLESC;
      COPY_CHAR_P (t, s, send);
    }
  *t = '\0';

  return (result);
}

char *
quote_escapes (const char *string)
{
  return (quote_escapes_internal (string, 0));
}

char *
quote_rhs (const char *string)
{
  return (quote_escapes_internal (string, PF_NOSPLIT2));
}

WORD_LIST *
list_quote_escapes (WORD_LIST *list)
{
  register WORD_LIST *w;
  char *t;

  for (w = list; w; w = w->next)
    {
      t = w->word->word;
      w->word->word = quote_escapes (t);
      free (t);
    }
  return list;
}

/* Inverse of quote_escapes; remove CTLESC protecting CTLESC or CTLNUL.

   The parser passes us CTLESC as CTLESC CTLESC and CTLNUL as CTLESC CTLNUL.
   This is necessary to make unquoted CTLESC and CTLNUL characters in the
   data stream pass through properly.

   We need to remove doubled CTLESC characters inside quoted strings before
   quoting the entire string, so we do not double the number of CTLESC
   characters.

   Also used by parts of the pattern substitution code. */
char *
dequote_escapes (const char *string)
{
  const char *s, *send;
  char *t, *result;
  size_t slen;
  int quote_spaces;
  DECLARE_MBSTATE;

  if (string == 0)
    return (char *)0;

  slen = strlen (string);
  send = string + slen;

  t = result = (char *)xmalloc (slen + 1);

  if (strchr (string, CTLESC) == 0)
    return (strcpy (result, string));

  quote_spaces = (ifs_value && *ifs_value == 0);

  s = string;
  while (*s)
    {
      if (*s == CTLESC && (s[1] == CTLESC || s[1] == CTLNUL || (quote_spaces && s[1] == ' ')))
	{
	  s++;
	  if (*s == '\0')
	    break;
	}
      COPY_CHAR_P (t, s, send);
    }
  *t = '\0';

  return result;
}

#if defined (INCLUDE_UNUSED)
static WORD_LIST *
list_dequote_escapes (WORD_LIST *list)
{
  register WORD_LIST *w;
  char *t;

  for (w = list; w; w = w->next)
    {
      t = w->word->word;
      w->word->word = dequote_escapes (t);
      free (t);
    }
  return list;
}
#endif

/* Return a new string with the quoted representation of character C.
   This turns "" into QUOTED_NULL, so the W_HASQUOTEDNULL flag needs to be
   set in any resultant WORD_DESC where this value is the word. */
char *
make_quoted_char (int c)
{
  char *temp;

  temp = (char *)xmalloc (3);
  if (c == 0)
    {
      temp[0] = CTLNUL;
      temp[1] = '\0';
    }
  else
    {
      temp[0] = CTLESC;
      temp[1] = c;
      temp[2] = '\0';
    }
  return (temp);
}

/* Quote STRING, returning a new string.  This turns "" into QUOTED_NULL, so
   the W_HASQUOTEDNULL flag needs to be set in any resultant WORD_DESC where
   this value is the word. */
char *
quote_string (char *string)
{
  register char *t;
  size_t slen;
  char *result, *send;

  if (*string == 0)
    {
      result = (char *)xmalloc (2);
      result[0] = CTLNUL;
      result[1] = '\0';
    }
  else
    {
      DECLARE_MBSTATE;

      slen = strlen (string);
      send = string + slen;

      result = (char *)xmalloc ((slen * 2) + 1);

      for (t = result; string < send; )
	{
	  *t++ = CTLESC;
	  COPY_CHAR_P (t, string, send);
	}
      *t = '\0';
    }
  return (result);
}

/* De-quote quoted characters in STRING. */
char *
dequote_string (char *string)
{
  register char *s, *t;
  size_t slen;
  char *result, *send;
  DECLARE_MBSTATE;

  if (string[0] == CTLESC && string[1] == 0)
    internal_debug ("dequote_string: string with bare CTLESC");

  slen = STRLEN (string);

  t = result = (char *)xmalloc (slen + 1);

  if (QUOTED_NULL (string))
    {
      result[0] = '\0';
      return (result);
    }

  /* A string consisting of only a single CTLESC should pass through unchanged */
  if (string[0] == CTLESC && string[1] == 0)
    {
      result[0] = CTLESC;
      result[1] = '\0';
      return (result);
    }

  /* If no character in the string can be quoted, don't bother examining
     each character.  Just return a copy of the string passed to us. */
  if (strchr (string, CTLESC) == NULL)
    return (strcpy (result, string));

  send = string + slen;
  s = string;
  while (*s)
    {
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

/* Quote the entire WORD_LIST list. */
WORD_LIST *
quote_list (WORD_LIST *list)
{
  register WORD_LIST *w;
  char *t;

  for (w = list; w; w = w->next)
    {
      t = w->word->word;
      w->word->word = quote_string (t);
      if (*t == 0)
	w->word->flags |= W_HASQUOTEDNULL;	/* XXX - turn on W_HASQUOTEDNULL here? */
      w->word->flags |= W_QUOTED;
      free (t);
    }
  return list;
}

WORD_DESC *
dequote_word (WORD_DESC *word)
{
  register char *s;

  s = dequote_string (word->word);
  if (QUOTED_NULL (word->word))
    word->flags &= ~W_HASQUOTEDNULL;
  free (word->word);
  word->word = s;

  return word;
}

/* De-quote quoted characters in each word in LIST. */
WORD_LIST *
dequote_list (WORD_LIST *list)
{
  register char *s;
  register WORD_LIST *tlist;

  for (tlist = list; tlist; tlist = tlist->next)
    {
      s = dequote_string (tlist->word->word);
      if (QUOTED_NULL (tlist->word->word))
	tlist->word->flags &= ~W_HASQUOTEDNULL;
      free (tlist->word->word);
      tlist->word->word = s;
    }
  return list;
}

/* Remove CTLESC protecting a CTLESC or CTLNUL in place.  Return the passed
   string. */
char *
remove_quoted_escapes (char *string)
{
  char *t;

  if (string)
    {
      t = dequote_escapes (string);
      strcpy (string, t);
      free (t);
    }

  return (string);
}

/* Remove quoted $IFS characters from STRING.  Quoted IFS characters are
   added to protect them from word splitting, but we need to remove them
   if no word splitting takes place.  This returns newly-allocated memory,
   so callers can use it to replace savestring(). */
char *
remove_quoted_ifs (char *string)
{
  register size_t slen;
  register int i, j;
  char *ret, *send;
  DECLARE_MBSTATE;

  slen = strlen (string);
  send = string + slen;

  i = j = 0;
  ret = (char *)xmalloc (slen + 1);

  while (i < slen)
    {
      if (string[i] == CTLESC)
	{
	  i++;
	  if (string[i] == 0 || isifs (string[i]) == 0)
	    ret[j++] = CTLESC;
	  if (i == slen)
	    break;
	}

      COPY_CHAR_I (ret, j, string, send, i);
    }
  ret[j] = '\0';

  return (ret);
}

char *
remove_quoted_nulls (char *string)
{
  register size_t slen;
  register int i, j, prev_i;
  DECLARE_MBSTATE;

  if (strchr (string, CTLNUL) == 0)		/* XXX */
    return string;				/* XXX */

  slen = strlen (string);
  i = j = 0;

  while (i < slen)
    {
      if (string[i] == CTLESC)
	{
	  /* Old code had j++, but we cannot assume that i == j at this
	     point -- what if a CTLNUL has already been removed from the
	     string?  We don't want to drop the CTLESC or recopy characters
	     that we've already copied down. */
	  i++;
	  string[j++] = CTLESC;
	  if (i == slen)
	    break;
	}
      else if (string[i] == CTLNUL)
	{
	  i++;
	  continue;
	}

      prev_i = i;
      ADVANCE_CHAR (string, slen, i);		/* COPY_CHAR_I? */
      if (j < prev_i)
	{
	  do string[j++] = string[prev_i++]; while (prev_i < i);
	}
      else
	j = i;
    }
  string[j] = '\0';

  return (string);
}

/* Perform quoted null character removal on each element of LIST.
   This modifies LIST. */
void
word_list_remove_quoted_nulls (WORD_LIST *list)
{
  register WORD_LIST *t;

  for (t = list; t; t = t->next)
    {
      remove_quoted_nulls (t->word->word);
      t->word->flags &= ~W_HASQUOTEDNULL;
    }
}
