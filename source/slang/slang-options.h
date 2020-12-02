// slang-options.h
#ifndef SLANG_OPTIONS_H
#define SLANG_OPTIONS_H

#include "../core/slang-basic.h"

namespace Slang
{


UnownedStringSlice getCodeGenTargetName(SlangCompileTarget target);

SlangResult parseOptions(
    SlangCompileRequest*    compileRequestIn,
    int                     argc,
    char const* const*      argv);

}
#endif
