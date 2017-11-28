#include "libgfortran.h"
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#if defined (HAVE_GFC_VECTOR_32)

void
cshift0_v32 (gfc_array_v32 *ret, const gfc_array_v32 *array, ptrdiff_t shift,
		     int which)
{
  /* r.* indicates the return array.  */
  index_type rstride[GFC_MAX_DIMENSIONS];
  index_type rstride0;
  index_type roffset;
  GFC_VECTOR_32 *rptr;

  /* s.* indicates the source array.  */
  index_type sstride[GFC_MAX_DIMENSIONS];
  index_type sstride0;
  index_type soffset;
  const GFC_VECTOR_32 *sptr;

  index_type count[GFC_MAX_DIMENSIONS];
  index_type extent[GFC_MAX_DIMENSIONS];
  index_type dim;
  index_type len;
  index_type n;

  which = which - 1;
  sstride[0] = 0;
  rstride[0] = 0;

  extent[0] = 1;
  count[0] = 0;
  n = 0;
  /* Initialized for avoiding compiler warnings.  */
  roffset = 1;
  soffset = 1;
  len = 0;

  for (dim = 0; dim < GFC_DESCRIPTOR_RANK (array); dim++)
    {
      if (dim == which)
        {
          roffset = GFC_DESCRIPTOR_STRIDE(ret,dim);
          if (roffset == 0)
            roffset = 1;
          soffset = GFC_DESCRIPTOR_STRIDE(array,dim);
          if (soffset == 0)
            soffset = 1;
          len = GFC_DESCRIPTOR_EXTENT(array,dim);
        }
      else
        {
          count[n] = 0;
          extent[n] = GFC_DESCRIPTOR_EXTENT(array,dim);
          rstride[n] = GFC_DESCRIPTOR_STRIDE(ret,dim);
          sstride[n] = GFC_DESCRIPTOR_STRIDE(array,dim);
          n++;
        }
    }
  if (sstride[0] == 0)
    sstride[0] = 1;
  if (rstride[0] == 0)
    rstride[0] = 1;

  dim = GFC_DESCRIPTOR_RANK (array);
  rstride0 = rstride[0];
  sstride0 = sstride[0];
  rptr = ret->data;
  sptr = array->data;

  shift = len == 0 ? 0 : shift % (ptrdiff_t)len;
  if (shift < 0)
    shift += len;

  while (rptr)
    {
      /* Do the shift for this dimension.  */

      /* If elements are contiguous, perform the operation
	 in two block moves.  */
      if (soffset == 1 && roffset == 1)
	{
	  size_t len1 = shift * sizeof (GFC_VECTOR_32);
	  size_t len2 = (len - shift) * sizeof (GFC_VECTOR_32);
	  memcpy (rptr, sptr + shift, len2);
	  memcpy (rptr + (len - shift), sptr, len1);
	}
      else
	{
	  /* Otherwise, we will have to perform the copy one element at
	     a time.  */
	  GFC_VECTOR_32 *dest = rptr;
	  const GFC_VECTOR_32 *src = &sptr[shift * soffset];

	  for (n = 0; n < len - shift; n++)
	    {
	      //*dest = *src;
		  memcpy(dest, src, sizeof(GFC_VECTOR_32));
	      dest += roffset;
	      src += soffset;
	    }
	  for (src = sptr, n = 0; n < shift; n++)
	    {
	      //*dest = *src;
		  memcpy(dest, src, sizeof(GFC_VECTOR_32));
	      dest += roffset;
	      src += soffset;
	    }
	}

      /* Advance to the next section.  */
      rptr += rstride0;
      sptr += sstride0;
      count[0]++;
      n = 0;
      while (count[n] == extent[n])
        {
          /* When we get to the end of a dimension, reset it and increment
             the next dimension.  */
          count[n] = 0;
          /* We could precalculate these products, but this is a less
             frequently used path so probably not worth it.  */
          rptr -= rstride[n] * extent[n];
          sptr -= sstride[n] * extent[n];
          n++;
          if (n >= dim - 1)
            {
              /* Break out of the loop.  */
              rptr = NULL;
              break;
            }
          else
            {
              count[n]++;
              rptr += rstride[n];
              sptr += sstride[n];
            }
        }
    }

  return;
}

#endif
