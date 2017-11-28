#ifndef LINEAGE_H
#define LINEAGE_H

#include "gimple.h"

extern void lineage_init (void);

extern void lineage_fp_init (void);

extern void lineage_finish_file (void);

extern void lineage_patch_predicate256 (gimple_stmt_iterator *, gimple);

#endif  /* LINEAGE_H */
