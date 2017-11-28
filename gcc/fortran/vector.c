#include "config.h"
#include "system.h"
#include "gfortran.h"
#include "match.h"
#include "constructor.h"

/****************** Vector constructor functions ******************/

/* Forward declaration because these functions are mutually recursive.  */
static match match_vector_cons_element (gfc_constructor_base *);

match
gfc_match_vector_constructor (gfc_expr **result)
{
  gfc_constructor_base head, new_cons;
  gfc_expr *expr;
  gfc_typespec ts;
  locus where;
  match m;
  const char *end_delim;
  bool seen_ts;

  if (gfc_match (" {/") == MATCH_NO)
  {
    return MATCH_NO;
  }
  else
    end_delim = " /}";

  where = gfc_current_locus;
  head = new_cons = NULL;
  seen_ts = false;

  if (! seen_ts)
    gfc_current_locus = where;

  if (gfc_match (end_delim) == MATCH_YES)
  {
    if (seen_ts)
      goto done;
    else
    {
      gfc_error ("Empty vector constructor at %C is not allowed");
      goto cleanup;
    }
  }

  for (;;)
  {
    m = match_vector_cons_element (&head);
    if (m == MATCH_ERROR)
      goto cleanup;
    if (m == MATCH_NO)
      goto syntax;

    fprintf (stderr, "one elem\n");

    if (gfc_match_char (',') == MATCH_NO)
      break;
  }

  if (gfc_match (end_delim) == MATCH_NO)
    goto syntax;

done:
  /* Size must be calculated at resolution time.  */
  if (seen_ts)
  {
    expr = gfc_get_vector_expr (ts.type, ts.kind, &where);
    expr->ts = ts;
  }
  else
    expr = gfc_get_vector_expr (BT_UNKNOWN, 0, &where);

  expr->value.constructor = head;
  if (expr->ts.u.cl)
    expr->ts.u.cl->length_from_typespec = seen_ts;

  *result = expr;
  fprintf (stderr, "match vec\n");
  return MATCH_YES;

syntax:
  gfc_error ("Syntax error in vector constructor at %C");

cleanup:
  gfc_constructor_free (head);
  return MATCH_ERROR;
}


/* Match a list of vector elements.  */

static match
match_vector_list (gfc_constructor_base *result)
{
  gfc_constructor_base head;
  gfc_constructor *p;
  gfc_iterator iter;
  locus old_loc;
  gfc_expr *e;
  match m;
  int n;

  old_loc = gfc_current_locus;

  if (gfc_match_char ('(') == MATCH_NO)
    return MATCH_NO;

  memset (&iter, '\0', sizeof (gfc_iterator));
  head = NULL;

  m = match_vector_cons_element (&head);
  if (m != MATCH_YES)
    goto cleanup;

  if (gfc_match_char (',') != MATCH_YES)
    {
      m = MATCH_NO;
      goto cleanup;
    }

  for (n = 1;; n++)
  {
    m = gfc_match_iterator (&iter, 0);
    if (m == MATCH_YES)
      break;
    if (m == MATCH_ERROR)
      goto cleanup;

    m = match_vector_cons_element (&head);

    if (m == MATCH_ERROR)
      goto cleanup;
    if (m == MATCH_NO)
    {
      if (n > 2)
        goto syntax;
      m = MATCH_NO;
      goto cleanup;		/* Could be a complex constant */
    }

    if (gfc_match_char (',') != MATCH_YES)
    {
      if (n > 2)
        goto syntax;
      m = MATCH_NO;
      goto cleanup;
    }
  }

  if (gfc_match_char (')') != MATCH_YES)
    goto syntax;

  e = gfc_get_vector_expr (BT_UNKNOWN, 0, &old_loc);
  e->value.constructor = head;

  p = gfc_constructor_append_expr (result, e, &gfc_current_locus);
  p->iterator = gfc_get_iterator ();
  *p->iterator = iter;

  return MATCH_YES;

syntax:
  gfc_error ("Syntax error in vector constructor at %C");
  m = MATCH_ERROR;

cleanup:
  gfc_constructor_free (head);
  gfc_free_iterator (&iter, 0);
  gfc_current_locus = old_loc;
  return m;
}


/* Match a single element of a vector constructor, which can be a
   single expression or a list of elements.  */

static match
match_vector_cons_element (gfc_constructor_base *result)
{
  gfc_expr *expr;
  match m;

  m = match_vector_list (result);
  if (m != MATCH_NO)
    return m;

  m = gfc_match_expr (&expr);
  if (m != MATCH_YES)
    return m;

  gfc_constructor_append_expr (result, expr, &gfc_current_locus);
  return MATCH_YES;
}

