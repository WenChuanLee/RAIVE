#ifndef IX86_BUILTINS_H
#define IX86_BUILTINS_H

#define DEF_IX86_BUILTIN(name) IX86_BUILTIN_## name,
/* Codes for all the SSE/MMX builtins.  */
enum ix86_builtins
{

#include "ix86-ssemmx.def"

  IX86_BUILTIN_MAX
};
#undef DEF_IX86_BUILTIN

#endif
