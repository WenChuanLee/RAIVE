/* { dg-do compile } */
/* { dg-skip-if "" { i?86-*-* x86_64-*-* } { "-march=*" } { "-march=core2" } } */
/* { dg-options "-O2 -ftree-vectorize -mfpmath=sse -march=core2 -fdump-tree-vect-stats" } */

extern void abort (void);

#ifndef STATIC
#define STATIC
#endif

#define N 16
 
double cb[N] = {0,3,6,9,12,15,18,21,24,27,30,33,36,39,42,45};
double ca[N];

STATIC void
__attribute__ ((noinline))
sse2_test (void)
{  
  int i;

  for (i = 0; i < N; i++)
    {
      ca[i] = cb[i];
    }

  /* check results:  */
  for (i = 0; i < N; i++)
    {
      if (ca[i] != cb[i])
        abort ();
    }
}

/* { dg-final { scan-tree-dump-times "vectorized 1 loops" 1 "vect" } } */
/* { dg-final { cleanup-tree-dump "vect" } } */
