#ifndef SLANG_H
#define SLANG_H

#if defined(SLANG_DYNAMIC_EXPORT)
    #if !defined(SLANG_DYNAMIC)
        #define SLANG_DYNAMIC
    #endif
#endif

#if defined(SLANG_DYNAMIC)
    #if defined(_MSC_VER)
        #ifdef SLANG_DYNAMIC_EXPORT
            #define SLANG_API __declspec(dllexport)
        #else
            #define SLANG_API __declspec(dllimport)
        #endif
    #else
        // TODO: need to consider compiler capabilities
//        #ifdef SLANG_DYNAMIC_EXPORT
            #define SLANG_API __attribute__((__visibility__("default")))
//        #endif
    #endif
#endif

#ifndef SLANG_API
#define SLANG_API
#endif

#ifndef  SLANG_NO_INTTYPES
#include <inttypes.h>
#endif // ! SLANG_NO_INTTYPES

#ifndef  SLANG_NO_STDDEF
#include <stddef.h>
#endif // ! SLANG_NO_STDDEF

#ifdef __cplusplus  
extern "C"
{
#endif
    /*!
    @mainpage Introduction

    API Reference: slang.h

    @file slang.h
    */

    typedef uint32_t    SlangUInt32;
    typedef intptr_t    SlangInt;
    typedef uintptr_t   SlangUInt;

    /*!
    @brief Severity of a diagnostic generated by the compiler.
    Values come from the enum below, with higher values representing more severe
    conditions, and all values >= SLANG_SEVERITY_ERROR indicating compilation
    failure.
    */
    typedef int SlangSeverity;
    enum
    {
        SLANG_SEVERITY_NOTE = 0,    /**< An informative message. */
        SLANG_SEVERITY_WARNING,     /**< A warning, which indicates a possible proble. */
        SLANG_SEVERITY_ERROR,       /**< An error, indicating that compilation failed. */
        SLANG_SEVERITY_FATAL,       /**< An unrecoverable error, which forced compilation to abort. */
        SLANG_SEVERITY_INTERNAL,    /**< An internal error, indicating a logic error in the compiler. */
    };

    typedef int SlangBindableResourceType;
    enum
    {
        SLANG_NON_BINDABLE = 0,
        SLANG_TEXTURE,
        SLANG_SAMPLER,
        SLANG_UNIFORM_BUFFER,
        SLANG_STORAGE_BUFFER,
    };

    typedef int SlangCompileTarget;
    enum
    {
        SLANG_TARGET_UNKNOWN,
        SLANG_TARGET_NONE,
        SLANG_GLSL,
        SLANG_GLSL_VULKAN,
        SLANG_GLSL_VULKAN_ONE_DESC,
        SLANG_HLSL,
        SLANG_SPIRV,
        SLANG_SPIRV_ASM,
        SLANG_DXBC,
        SLANG_DXBC_ASM,
        SLANG_DXIL,
        SLANG_DXIL_ASM,
    };

    /* A "container format" describes the way that the outputs
    for multiple files, entry points, targets, etc. should be
    combined into a single artifact for output. */
    typedef int SlangContainerFormat;
    enum
    {
        /* Don't generate a container. */
        SLANG_CONTAINER_FORMAT_NONE,

        /* Generate a container in the `.slang-module` format,
        which includes reflection information, compiled kernels, etc. */
        SLANG_CONTAINER_FORMAT_SLANG_MODULE,
    };

    typedef int SlangPassThrough;
    enum
    {
        SLANG_PASS_THROUGH_NONE,
        SLANG_PASS_THROUGH_FXC,
        SLANG_PASS_THROUGH_DXC,
        SLANG_PASS_THROUGH_GLSLANG,
    };

    /*!
    Flags to control compilation behavior.
    */
    typedef unsigned int SlangCompileFlags;
    enum
    {
         /** Disable semantic checking as much as possible. */
        SLANG_COMPILE_FLAG_NO_CHECKING          = 1 << 0,

        /* Split apart types that contain a mix of resource and non-resource data */
        SLANG_COMPILE_FLAG_SPLIT_MIXED_TYPES    = 1 << 1,

        /* Use new IR-based code generation path (unstable pre-release feature)*/
        SLANG_COMPILE_FLAG_USE_IR               = 1 << 2,

        /* Do as little mangling of names as possible, to try to preserve original names */
        SLANG_COMPILE_FLAG_NO_MANGLING          = 1 << 3,
    };

    /*!
    @brief Flags to control code generation behavior of a compilation target */
    typedef unsigned int SlangTargetFlags;
    enum
    {
        /* When compiling for a D3D Shader Model 5.1 or higher target, allocate
           distinct register spaces for parameter blocks. */
        SLANG_TARGET_FLAG_PARAMETER_BLOCKS_USE_REGISTER_SPACES = 1 << 4,
    };

    /*!
    @brief Options to control emission of `#line` directives
    */
    typedef unsigned int SlangLineDirectiveMode;
    enum
    {
        SLANG_LINE_DIRECTIVE_MODE_DEFAULT = 0,  /**< Default behavior: pick behavior base on target. */
        SLANG_LINE_DIRECTIVE_MODE_NONE,         /**< Don't emit line directives at all. */
        SLANG_LINE_DIRECTIVE_MODE_STANDARD,     /**< Emit standard C-style `#line` directives. */
        SLANG_LINE_DIRECTIVE_MODE_GLSL,         /**< Emit GLSL-style directives with file *number* instead of name */
    };

    typedef int SlangSourceLanguage;
    enum
    {
        SLANG_SOURCE_LANGUAGE_UNKNOWN,
        SLANG_SOURCE_LANGUAGE_SLANG,
        SLANG_SOURCE_LANGUAGE_HLSL,
        SLANG_SOURCE_LANGUAGE_GLSL,
    };

    typedef unsigned int SlangProfileID;
    enum
    {
        SLANG_PROFILE_UNKNOWN,
    };

//#define SLANG_LAYOUT_UNIFORM 0
//#define SLANG_LAYOUT_PACKED 1
//#define SLANG_LAYOUT_STORAGE 2

#define SLANG_ERROR_INSUFFICIENT_BUFFER -1
#define SLANG_ERROR_INVALID_PARAMETER -2

    /*!
    @brief An instance of the Slang library.
    */
    typedef struct SlangSession SlangSession;

    /*!
    @bref A request for one or more compilation actions to be performed.
    */
    typedef struct SlangCompileRequest SlangCompileRequest;

    /*!
    @brief Initialize an instance of the Slang library.
    @param cacheDir The directory used to store cached compilation results. Pass NULL to disable caching.
    */
    SLANG_API SlangSession* spCreateSession(const char * cacheDir);

    /*!
    @brief Clean up after an instance of the Slang library.
    */
    SLANG_API void spDestroySession(
        SlangSession*   session);


    /*!
    @brief Add new builtin declarations to be used in subsequent compiles.
    */
    SLANG_API void spAddBuiltins(
        SlangSession*   session,
        char const*     sourcePath,
        char const*     sourceString);

    /*!
    @brief Create a compile request.
    */
    SLANG_API SlangCompileRequest* spCreateCompileRequest(
        SlangSession* session);

    /*!
    @brief Destroy a compile request.
    */
    SLANG_API void spDestroyCompileRequest(
        SlangCompileRequest*    request);


    /*!
    @brief Set flags to be used for compilation.
    */
    SLANG_API void spSetCompileFlags(
        SlangCompileRequest*    request,
        SlangCompileFlags       flags);

    /*!
    @brief Set whether to dump intermediate results (for debugging) or not.
    */
    SLANG_API void spSetDumpIntermediates(
        SlangCompileRequest*    request,
        int                     enable);

    /*!
    @brief Set whether (and how) `#line` directives hsould be output.
    */
    SLANG_API void spSetLineDirectiveMode(
        SlangCompileRequest*    request,
        SlangLineDirectiveMode  mode);

    /*!
    @brief Sets the target for code generation.
    @param ctx The compilation context.
    @param target The code generation target. Possible values are:
    - SLANG_GLSL. Generates GLSL code.
    - SLANG_HLSL. Generates HLSL code.
    - SLANG_SPIRV. Generates SPIR-V code.
    */
    SLANG_API void spSetCodeGenTarget(
        SlangCompileRequest*    request,
        int target);

    /*!
    @brief Add a code-generation target to be used.
    */
    SLANG_API int spAddCodeGenTarget(
        SlangCompileRequest*    request,
        SlangCompileTarget      target);

    SLANG_API void spSetTargetProfile(
        SlangCompileRequest*    request,
        int                     targetIndex,
        SlangProfileID          profile);

    SLANG_API void spSetTargetFlags(
        SlangCompileRequest*    request,
        int                     targetIndex,
        SlangTargetFlags        flags);

    /*!
    @brief Set the container format to be used for binary output.
    */
    SLANG_API void spSetOutputContainerFormat(
        SlangCompileRequest*    request,
        SlangContainerFormat    format);

    SLANG_API void spSetPassThrough(
        SlangCompileRequest*    request,
        SlangPassThrough        passThrough);

    typedef void(*SlangDiagnosticCallback)(
        char const* message,
        void*       userData);

    SLANG_API void spSetDiagnosticCallback(
        SlangCompileRequest*    request,
        SlangDiagnosticCallback callback,
        void const*             userData);

    /*!
    @brief Add a path to use when searching for referenced files.
    This will be used for both `#include` directives and also for explicit `__import` declarations.
    @param ctx The compilation context.
    @param searchDir The additional search directory.
    */
    SLANG_API void spAddSearchPath(
        SlangCompileRequest*    request,
        const char*             searchDir);

    /*!
    @brief Add a macro definition to be used during preprocessing.
    @param key The name of the macro to define.
    @param value The value of the macro to define.
    */
    SLANG_API void spAddPreprocessorDefine(
        SlangCompileRequest*    request,
        const char*             key,
        const char*             value);

    /*!
    @brief Set options using arguments as if specified via command line.
    */
    SLANG_API int spProcessCommandLineArguments(
        SlangCompileRequest*    request,
        char const* const*      args,
        int                     argCount);

    /** Add a distinct translation unit to the compilation request

    `name` is optional.
    Returns the zero-based index of the translation unit created.
    */
    SLANG_API int spAddTranslationUnit(
        SlangCompileRequest*    request,
        SlangSourceLanguage     language,
        char const*             name);

    /** Add a preprocessor definition that is scoped to a single translation unit.

    @param translationUnitIndex The index of the translation unit to get the definition.
    @param key The name of the macro to define.
    @param value The value of the macro to define.
    */
    SLANG_API void spTranslationUnit_addPreprocessorDefine(
        SlangCompileRequest*    request,
        int                     translationUnitIndex,
        const char*             key,
        const char*             value);


    /** Add a source file to the given translation unit
    */
    SLANG_API void spAddTranslationUnitSourceFile(
        SlangCompileRequest*    request,
        int                     translationUnitIndex,
        char const*             path);

    /** Add a source string to the given translation unit

    The `path` will be used in any diagnostic output.
    */
    SLANG_API void spAddTranslationUnitSourceString(
        SlangCompileRequest*    request,
        int                     translationUnitIndex,
        char const*             path,
        char const*             source);

    /** Look up a compilation profile by name.

    For example, one could look up the string `"ps_5_0"` to find the corresponding target ID.
    */
    SLANG_API SlangProfileID spFindProfile(
        SlangSession*   session,
        char const*     name);

    /** Add an entry point in a particular translation unit
    */
    SLANG_API int spAddEntryPoint(
        SlangCompileRequest*    request,
        int                     translationUnitIndex,
        char const*             name,
        SlangProfileID          profile);

    /** Add an entry point in a particular translation unit,
        with additional arguments that specify the concrete
        type names for global generic type parameters.
    */
    SLANG_API int spAddEntryPointEx(
        SlangCompileRequest*    request,
        int                     translationUnitIndex,
        char const*             name,
        SlangProfileID          profile,
        int                     genericTypeNameCount,
        char const**            genericTypeNames);

    /** Execute the compilation request.

    Returns zero on success, non-zero on failure.
    */
    SLANG_API int spCompile(
        SlangCompileRequest*    request);


    /** Get any diagnostic messages reported by the compiler.
    */
    SLANG_API char const* spGetDiagnosticOutput(
        SlangCompileRequest*    request);

    /** Get the number of files that this compilation depended on.
    
    This includes both the explicit source files, as well as any
    additional files that were transitively referenced (e.g., via
    a `#include` directive).
    */
    SLANG_API int
    spGetDependencyFileCount(
        SlangCompileRequest*    request);

    /** Get the path to a file this compilation dependend on.
    */
    SLANG_API char const*
    spGetDependencyFilePath(
        SlangCompileRequest*    request,
        int                     index);

    /** Get the number of tranlsation units associated with the compilation request
    */
    SLANG_API int
    spGetTranslationUnitCount(
        SlangCompileRequest*    request);

    /** Get the output code associated with a specific translation unit.

    The lifetime of the output pointer is the same as `request`.
    */
    SLANG_API char const* spGetTranslationUnitSource(
        SlangCompileRequest*    request,
        int                     translationUnitIndex);

    /** Get the output source code associated with a specific entry point.

    The lifetime of the output pointer is the same as `request`.
    */
    SLANG_API char const* spGetEntryPointSource(
        SlangCompileRequest*    request,
        int                     entryPointIndex);

    /** Get the output bytecode associated with a specific entry point.

    The lifetime of the output pointer is the same as `request`.
    */
    SLANG_API void const* spGetEntryPointCode(
        SlangCompileRequest*    request,
        int                     entryPointIndex,
        size_t*                 outSize);

    /** Get the output bytecode associated with an entire compile request.

    The lifetime of the output pointer is the same as `request`.
    */
    SLANG_API void const* spGetCompileRequestCode(
        SlangCompileRequest*    request,
        size_t*                 outSize);



    typedef struct SlangVM          SlangVM;
    typedef struct SlangVMModule    SlangVMModule;
    typedef struct SlangVMFunc      SlangVMFunc;
    typedef struct SlangVMThread    SlangVMThread;

    SLANG_API SlangVM* SlangVM_create();

    SLANG_API SlangVMModule* SlangVMModule_load(
        SlangVM*    vm,
        void const* bytecode,
        size_t      bytecodeSize);

    SLANG_API void* SlangVMModule_findGlobalSymbolPtr(
        SlangVMModule*  module,
        char const*     name);

    SLANG_API SlangVMThread* SlangVMThread_create(
        SlangVM*    vm);

    SLANG_API void SlangVMThread_beginCall(
        SlangVMThread*  thread,
        SlangVMFunc*    func);

    SLANG_API void SlangVMThread_setArg(
        SlangVMThread*  thread,
        SlangUInt       argIndex,
        void const*     data,
        size_t          size);

    SLANG_API void SlangVMThread_resume(
        SlangVMThread*  thread);

    /* Note(tfoley): working on new reflection interface...
    */

    typedef struct SlangReflection                  SlangReflection;
    typedef struct SlangReflectionEntryPoint        SlangReflectionEntryPoint;
    typedef struct SlangReflectionType              SlangReflectionType;
    typedef struct SlangReflectionTypeLayout        SlangReflectionTypeLayout;
    typedef struct SlangReflectionVariable          SlangReflectionVariable;
    typedef struct SlangReflectionVariableLayout    SlangReflectionVariableLayout;

    // get reflection data from a compilation request
    SLANG_API SlangReflection* spGetReflection(
        SlangCompileRequest*    request);

    // type reflection

    typedef unsigned int SlangTypeKind;
    enum
    {
        SLANG_TYPE_KIND_NONE,
        SLANG_TYPE_KIND_STRUCT,
        SLANG_TYPE_KIND_ARRAY,
        SLANG_TYPE_KIND_MATRIX,
        SLANG_TYPE_KIND_VECTOR,
        SLANG_TYPE_KIND_SCALAR,
        SLANG_TYPE_KIND_CONSTANT_BUFFER,
        SLANG_TYPE_KIND_RESOURCE,
        SLANG_TYPE_KIND_SAMPLER_STATE,
        SLANG_TYPE_KIND_TEXTURE_BUFFER,
        SLANG_TYPE_KIND_SHADER_STORAGE_BUFFER,

        SLANG_TYPE_KIND_COUNT,
    };

    typedef unsigned int SlangScalarType;
    enum
    {
        SLANG_SCALAR_TYPE_NONE,
        SLANG_SCALAR_TYPE_VOID,
        SLANG_SCALAR_TYPE_BOOL,
        SLANG_SCALAR_TYPE_INT32,
        SLANG_SCALAR_TYPE_UINT32,
        SLANG_SCALAR_TYPE_INT64,
        SLANG_SCALAR_TYPE_UINT64,
        SLANG_SCALAR_TYPE_FLOAT16,
        SLANG_SCALAR_TYPE_FLOAT32,
        SLANG_SCALAR_TYPE_FLOAT64,
    };

    typedef unsigned int SlangResourceShape;
    enum
    {
        SLANG_RESOURCE_BASE_SHAPE_MASK      = 0x0F,

        SLANG_RESOURCE_NONE                 = 0x00,

        SLANG_TEXTURE_1D                    = 0x01,
        SLANG_TEXTURE_2D                    = 0x02,
        SLANG_TEXTURE_3D                    = 0x03,
        SLANG_TEXTURE_CUBE                  = 0x04,
        SLANG_TEXTURE_BUFFER                = 0x05,

        SLANG_STRUCTURED_BUFFER             = 0x06,
        SLANG_BYTE_ADDRESS_BUFFER           = 0x07,
        SLANG_RESOURCE_UNKNOWN              = 0x08,

        SLANG_RESOURCE_EXT_SHAPE_MASK       = 0xF0,
        SLANG_TEXTURE_ARRAY_FLAG            = 0x40,
        SLANG_TEXTURE_MULTISAMPLE_FLAG      = 0x80,

        SLANG_TEXTURE_1D_ARRAY              = SLANG_TEXTURE_1D   | SLANG_TEXTURE_ARRAY_FLAG,
        SLANG_TEXTURE_2D_ARRAY              = SLANG_TEXTURE_2D   | SLANG_TEXTURE_ARRAY_FLAG,
        SLANG_TEXTURE_CUBE_ARRAY            = SLANG_TEXTURE_CUBE | SLANG_TEXTURE_ARRAY_FLAG,

        SLANG_TEXTURE_2D_MULTISAMPLE        = SLANG_TEXTURE_2D | SLANG_TEXTURE_MULTISAMPLE_FLAG,
        SLANG_TEXTURE_2D_MULTISAMPLE_ARRAY  = SLANG_TEXTURE_2D | SLANG_TEXTURE_MULTISAMPLE_FLAG | SLANG_TEXTURE_ARRAY_FLAG,
    };

    typedef unsigned int SlangResourceAccess;
    enum
    {
        SLANG_RESOURCE_ACCESS_NONE,
        SLANG_RESOURCE_ACCESS_READ,
        SLANG_RESOURCE_ACCESS_READ_WRITE,
        SLANG_RESOURCE_ACCESS_RASTER_ORDERED,
        SLANG_RESOURCE_ACCESS_APPEND,
        SLANG_RESOURCE_ACCESS_CONSUME,
    };

    typedef unsigned int SlangParameterCategory;
    enum
    {
        SLANG_PARAMETER_CATEGORY_NONE,
        SLANG_PARAMETER_CATEGORY_MIXED,
        SLANG_PARAMETER_CATEGORY_CONSTANT_BUFFER,
        SLANG_PARAMETER_CATEGORY_SHADER_RESOURCE,
        SLANG_PARAMETER_CATEGORY_UNORDERED_ACCESS,
        SLANG_PARAMETER_CATEGORY_VERTEX_INPUT,
        SLANG_PARAMETER_CATEGORY_FRAGMENT_OUTPUT,
        SLANG_PARAMETER_CATEGORY_SAMPLER_STATE,
        SLANG_PARAMETER_CATEGORY_UNIFORM,
        SLANG_PARAMETER_CATEGORY_DESCRIPTOR_TABLE_SLOT,
        SLANG_PARAMETER_CATEGORY_SPECIALIZATION_CONSTANT,
        SLANG_PARAMETER_CATEGORY_PUSH_CONSTANT_BUFFER,

        // HLSL register `space`, Vulkan GLSL `set`
        SLANG_PARAMETER_CATEGORY_REGISTER_SPACE,

        // A generic-typed entry-point parameter
        SLANG_PARAMETER_CATEGORY_GENERIC,

        //
        SLANG_PARAMETER_CATEGORY_COUNT,
    };

    typedef SlangUInt32 SlangStage;
    enum
    {
        SLANG_STAGE_NONE,
        SLANG_STAGE_VERTEX,
        SLANG_STAGE_HULL,
        SLANG_STAGE_DOMAIN,
        SLANG_STAGE_GEOMETRY,
        SLANG_STAGE_FRAGMENT,
        SLANG_STAGE_COMPUTE,

        SLANG_STAGE_PIXEL = SLANG_STAGE_FRAGMENT,
    };

    // Type Reflection

    SLANG_API SlangTypeKind spReflectionType_GetKind(SlangReflectionType* type);
    SLANG_API unsigned int spReflectionType_GetFieldCount(SlangReflectionType* type);
    SLANG_API SlangReflectionVariable* spReflectionType_GetFieldByIndex(SlangReflectionType* type, unsigned index);

    SLANG_API size_t spReflectionType_GetElementCount(SlangReflectionType* type);
    SLANG_API SlangReflectionType* spReflectionType_GetElementType(SlangReflectionType* type);

    SLANG_API unsigned int spReflectionType_GetRowCount(SlangReflectionType* type);
    SLANG_API unsigned int spReflectionType_GetColumnCount(SlangReflectionType* type);
    SLANG_API SlangScalarType spReflectionType_GetScalarType(SlangReflectionType* type);

    SLANG_API SlangResourceShape spReflectionType_GetResourceShape(SlangReflectionType* type);
    SLANG_API SlangResourceAccess spReflectionType_GetResourceAccess(SlangReflectionType* type);
    SLANG_API SlangReflectionType* spReflectionType_GetResourceResultType(SlangReflectionType* type);

    SLANG_API char const* spReflectionType_GetName(SlangReflectionType* type);

    // Type Layout Reflection

    SLANG_API SlangReflectionType* spReflectionTypeLayout_GetType(SlangReflectionTypeLayout* type);
    SLANG_API size_t spReflectionTypeLayout_GetSize(SlangReflectionTypeLayout* type, SlangParameterCategory category);

    SLANG_API SlangReflectionVariableLayout* spReflectionTypeLayout_GetFieldByIndex(SlangReflectionTypeLayout* type, unsigned index);

    SLANG_API size_t spReflectionTypeLayout_GetElementStride(SlangReflectionTypeLayout* type, SlangParameterCategory category);
    SLANG_API SlangReflectionTypeLayout* spReflectionTypeLayout_GetElementTypeLayout(SlangReflectionTypeLayout* type);

    SLANG_API SlangParameterCategory spReflectionTypeLayout_GetParameterCategory(SlangReflectionTypeLayout* type);

    SLANG_API unsigned spReflectionTypeLayout_GetCategoryCount(SlangReflectionTypeLayout* type);
    SLANG_API SlangParameterCategory spReflectionTypeLayout_GetCategoryByIndex(SlangReflectionTypeLayout* type, unsigned index);

    // Variable Reflection

    SLANG_API char const* spReflectionVariable_GetName(SlangReflectionVariable* var);
    SLANG_API SlangReflectionType* spReflectionVariable_GetType(SlangReflectionVariable* var);

    // Variable Layout Reflection

    SLANG_API SlangReflectionVariable* spReflectionVariableLayout_GetVariable(SlangReflectionVariableLayout* var);

    SLANG_API SlangReflectionTypeLayout* spReflectionVariableLayout_GetTypeLayout(SlangReflectionVariableLayout* var);

    SLANG_API size_t spReflectionVariableLayout_GetOffset(SlangReflectionVariableLayout* var, SlangParameterCategory category);
    SLANG_API size_t spReflectionVariableLayout_GetSpace(SlangReflectionVariableLayout* var, SlangParameterCategory category);

    SLANG_API char const* spReflectionVariableLayout_GetSemanticName(SlangReflectionVariableLayout* var);
    SLANG_API size_t spReflectionVariableLayout_GetSemanticIndex(SlangReflectionVariableLayout* var);

    // Shader Parameter Reflection

    typedef SlangReflectionVariableLayout SlangReflectionParameter;

    SLANG_API unsigned spReflectionParameter_GetBindingIndex(SlangReflectionParameter* parameter);
    SLANG_API unsigned spReflectionParameter_GetBindingSpace(SlangReflectionParameter* parameter);

    // Entry Point Reflection

    SLANG_API char const* spReflectionEntryPoint_getName(
        SlangReflectionEntryPoint* entryPoint);

    SLANG_API unsigned spReflectionEntryPoint_getParameterCount(
        SlangReflectionEntryPoint* entryPoint);

    SLANG_API SlangReflectionVariableLayout* spReflectionEntryPoint_getParameterByIndex(
        SlangReflectionEntryPoint*  entryPoint,
        unsigned                    index);

    SLANG_API SlangStage spReflectionEntryPoint_getStage(SlangReflectionEntryPoint* entryPoint);

    SLANG_API void spReflectionEntryPoint_getComputeThreadGroupSize(
        SlangReflectionEntryPoint*  entryPoint,
        SlangUInt                   axisCount,
        SlangUInt*                  outSizeAlongAxis);

    SLANG_API int spReflectionEntryPoint_usesAnySampleRateInput(
        SlangReflectionEntryPoint* entryPoint);

    // Shader Reflection

    SLANG_API unsigned spReflection_GetParameterCount(SlangReflection* reflection);
    SLANG_API SlangReflectionParameter* spReflection_GetParameterByIndex(SlangReflection* reflection, unsigned index);


    SLANG_API SlangUInt spReflection_getEntryPointCount(SlangReflection* reflection);

    SLANG_API SlangReflectionEntryPoint* spReflection_getEntryPointByIndex(SlangReflection* reflection, SlangUInt index);
    SLANG_API SlangUInt spReflection_getGlobalConstantBufferBinding(SlangReflection* reflection);
    SLANG_API size_t spReflection_getGlobalConstantBufferSize(SlangReflection* reflection);

#ifdef __cplusplus  
}

/* Helper interfaces for C++ users */
namespace slang
{
#define SLANG_SAFE_BOOL(expr) \
    operator bool() const { return expr; }

    struct BufferReflection;
    struct TypeLayoutReflection;
    struct TypeReflection;
    struct VariableLayoutReflection;
    struct VariableReflection;

    struct TypeReflection
    {
        enum class Kind
        {
            None    = SLANG_TYPE_KIND_NONE,
            Struct  = SLANG_TYPE_KIND_STRUCT,
            Array   = SLANG_TYPE_KIND_ARRAY,
            Matrix  = SLANG_TYPE_KIND_MATRIX,
            Vector  = SLANG_TYPE_KIND_VECTOR,
            Scalar  = SLANG_TYPE_KIND_SCALAR,
            ConstantBuffer = SLANG_TYPE_KIND_CONSTANT_BUFFER,
            Resource = SLANG_TYPE_KIND_RESOURCE,
            SamplerState = SLANG_TYPE_KIND_SAMPLER_STATE,
            TextureBuffer = SLANG_TYPE_KIND_TEXTURE_BUFFER,
            ShaderStorageBuffer = SLANG_TYPE_KIND_SHADER_STORAGE_BUFFER,
        };

        enum ScalarType : SlangScalarType
        {
            None    = SLANG_SCALAR_TYPE_NONE,
            Void    = SLANG_SCALAR_TYPE_VOID,
            Bool    = SLANG_SCALAR_TYPE_BOOL,
            Int32   = SLANG_SCALAR_TYPE_INT32,
            UInt32  = SLANG_SCALAR_TYPE_UINT32,
            Int64   = SLANG_SCALAR_TYPE_INT64,
            UInt64  = SLANG_SCALAR_TYPE_UINT64,
            Float16 = SLANG_SCALAR_TYPE_FLOAT16,
            Float32 = SLANG_SCALAR_TYPE_FLOAT32,
            Float64 = SLANG_SCALAR_TYPE_FLOAT64,
        };

        Kind getKind()
        {
            return (Kind) spReflectionType_GetKind((SlangReflectionType*) this);
        }

        // only useful if `getKind() == Kind::Struct`
        unsigned int getFieldCount()
        {
            return spReflectionType_GetFieldCount((SlangReflectionType*) this);
        }

        VariableReflection* getFieldByIndex(unsigned int index)
        {
            return (VariableReflection*) spReflectionType_GetFieldByIndex((SlangReflectionType*) this, index);
        }

        bool isArray() { return getKind() == TypeReflection::Kind::Array; }

        TypeReflection* unwrapArray()
        {
            TypeReflection* type = this;
            while( type->isArray() )
            {
                type = type->getElementType();
            }
            return type;
        }

        // only useful if `getKind() == Kind::Array`
        size_t getElementCount()
        {
            return spReflectionType_GetElementCount((SlangReflectionType*) this);
        }

        size_t getTotalArrayElementCount()
        {
            if(!isArray()) return 0;
            size_t result = 1;
            TypeReflection* type = this;
            for(;;)
            {
                if(!type->isArray())
                    return result;

                result *= type->getElementCount();
                type = type->getElementType();
            }
        }

        TypeReflection* getElementType()
        {
            return (TypeReflection*) spReflectionType_GetElementType((SlangReflectionType*) this);
        }

        unsigned getRowCount()
        {
            return spReflectionType_GetRowCount((SlangReflectionType*) this);
        }

        unsigned getColumnCount()
        {
            return spReflectionType_GetColumnCount((SlangReflectionType*) this);
        }

        ScalarType getScalarType()
        {
            return (ScalarType) spReflectionType_GetScalarType((SlangReflectionType*) this);
        }

        TypeReflection* getResourceResultType()
        {
            return (TypeReflection*) spReflectionType_GetResourceResultType((SlangReflectionType*) this);
        }

        SlangResourceShape getResourceShape()
        {
            return spReflectionType_GetResourceShape((SlangReflectionType*) this);
        }

        SlangResourceAccess getResourceAccess()
        {
            return spReflectionType_GetResourceAccess((SlangReflectionType*) this);
        }

        char const* getName()
        {
            return spReflectionType_GetName((SlangReflectionType*) this);
        }
    };

    enum ParameterCategory : SlangParameterCategory
    {
        // TODO: these aren't scoped...
        None = SLANG_PARAMETER_CATEGORY_NONE,
        Mixed = SLANG_PARAMETER_CATEGORY_MIXED,
        ConstantBuffer = SLANG_PARAMETER_CATEGORY_CONSTANT_BUFFER,
        ShaderResource = SLANG_PARAMETER_CATEGORY_SHADER_RESOURCE,
        UnorderedAccess = SLANG_PARAMETER_CATEGORY_UNORDERED_ACCESS,
        VertexInput = SLANG_PARAMETER_CATEGORY_VERTEX_INPUT,
        FragmentOutput = SLANG_PARAMETER_CATEGORY_FRAGMENT_OUTPUT,
        SamplerState = SLANG_PARAMETER_CATEGORY_SAMPLER_STATE,
        Uniform = SLANG_PARAMETER_CATEGORY_UNIFORM,
        DescriptorTableSlot = SLANG_PARAMETER_CATEGORY_DESCRIPTOR_TABLE_SLOT,
        SpecializationConstant = SLANG_PARAMETER_CATEGORY_SPECIALIZATION_CONSTANT,
        PushConstantBuffer = SLANG_PARAMETER_CATEGORY_PUSH_CONSTANT_BUFFER,
        RegisterSpace = SLANG_PARAMETER_CATEGORY_REGISTER_SPACE,
        GenericResource = SLANG_PARAMETER_CATEGORY_GENERIC,
    };

    struct TypeLayoutReflection
    {
        TypeReflection* getType()
        {
            return (TypeReflection*) spReflectionTypeLayout_GetType((SlangReflectionTypeLayout*) this);
        }

        TypeReflection::Kind getKind() { return getType()->getKind(); }

        size_t getSize(SlangParameterCategory category = SLANG_PARAMETER_CATEGORY_UNIFORM)
        {
            return spReflectionTypeLayout_GetSize((SlangReflectionTypeLayout*) this, category);
        }

        unsigned int getFieldCount()
        {
            return getType()->getFieldCount();
        }

        VariableLayoutReflection* getFieldByIndex(unsigned int index)
        {
            return (VariableLayoutReflection*) spReflectionTypeLayout_GetFieldByIndex((SlangReflectionTypeLayout*) this, index);
        }

        bool isArray() { return getType()->isArray(); }

        TypeLayoutReflection* unwrapArray()
        {
            TypeLayoutReflection* typeLayout = this;
            while( typeLayout->isArray() )
            {
                typeLayout = typeLayout->getElementTypeLayout();
            }
            return typeLayout;
        }

        // only useful if `getKind() == Kind::Array`
        size_t getElementCount()
        {
            return getType()->getElementCount();
        }

        size_t getTotalArrayElementCount()
        {
            return getType()->getTotalArrayElementCount();
        }

        size_t getElementStride(SlangParameterCategory category)
        {
            return spReflectionTypeLayout_GetElementStride((SlangReflectionTypeLayout*) this, category);
        }

        TypeLayoutReflection* getElementTypeLayout()
        {
            return (TypeLayoutReflection*) spReflectionTypeLayout_GetElementTypeLayout((SlangReflectionTypeLayout*) this);
        }

        // How is this type supposed to be bound?
        ParameterCategory getParameterCategory()
        {
            return (ParameterCategory) spReflectionTypeLayout_GetParameterCategory((SlangReflectionTypeLayout*) this);
        }

        unsigned int getCategoryCount()
        {
            return spReflectionTypeLayout_GetCategoryCount((SlangReflectionTypeLayout*) this);
        }

        ParameterCategory getCategoryByIndex(unsigned int index)
        {
            return (ParameterCategory) spReflectionTypeLayout_GetCategoryByIndex((SlangReflectionTypeLayout*) this, index);
        }

        unsigned getRowCount()
        {
            return getType()->getRowCount();
        }

        unsigned getColumnCount()
        {
            return getType()->getColumnCount();
        }

        TypeReflection::ScalarType getScalarType()
        {
            return getType()->getScalarType();
        }

        TypeReflection* getResourceResultType()
        {
            return getType()->getResourceResultType();
        }

        SlangResourceShape getResourceShape()
        {
            return getType()->getResourceShape();
        }

        SlangResourceAccess getResourceAccess()
        {
            return getType()->getResourceAccess();
        }

        char const* getName()
        {
            return getType()->getName();
        }
    };

    struct VariableReflection
    {
        char const* getName()
        {
            return spReflectionVariable_GetName((SlangReflectionVariable*) this);
        }

        TypeReflection* getType()
        {
            return (TypeReflection*) spReflectionVariable_GetType((SlangReflectionVariable*) this);
        }
    };

    struct VariableLayoutReflection
    {
        VariableReflection* getVariable()
        {
            return (VariableReflection*) spReflectionVariableLayout_GetVariable((SlangReflectionVariableLayout*) this);
        }

        char const* getName()
        {
            return getVariable()->getName();
        }

        TypeLayoutReflection* getTypeLayout()
        {
            return (TypeLayoutReflection*) spReflectionVariableLayout_GetTypeLayout((SlangReflectionVariableLayout*) this);
        }

        ParameterCategory getCategory()
        {
            return getTypeLayout()->getParameterCategory();
        }

        unsigned int getCategoryCount()
        {
            return getTypeLayout()->getCategoryCount();
        }

        ParameterCategory getCategoryByIndex(unsigned int index)
        {
            return getTypeLayout()->getCategoryByIndex(index);
        }


        size_t getOffset(SlangParameterCategory category = SLANG_PARAMETER_CATEGORY_UNIFORM)
        {
            return spReflectionVariableLayout_GetOffset((SlangReflectionVariableLayout*) this, category);
        }

        TypeReflection* getType()
        {
            return getVariable()->getType();
        }

        unsigned getBindingIndex()
        {
            return spReflectionParameter_GetBindingIndex((SlangReflectionVariableLayout*) this);
        }

        unsigned getBindingSpace()
        {
            return spReflectionParameter_GetBindingSpace((SlangReflectionVariableLayout*) this);
        }

        size_t getBindingSpace(SlangParameterCategory category)
        {
            return spReflectionVariableLayout_GetSpace((SlangReflectionVariableLayout*) this, category);
        }

        char const* getSemanticName()
        {
            return spReflectionVariableLayout_GetSemanticName((SlangReflectionVariableLayout*) this);
        }

        size_t getSemanticIndex()
        {
            return spReflectionVariableLayout_GetSemanticIndex((SlangReflectionVariableLayout*) this);
        }
    };

    struct EntryPointReflection
    {
        char const* getName()
        {
            return spReflectionEntryPoint_getName((SlangReflectionEntryPoint*) this);
        }

        unsigned getParameterCount()
        {
            return spReflectionEntryPoint_getParameterCount((SlangReflectionEntryPoint*) this);
        }

        VariableLayoutReflection* getParameterByIndex(unsigned index)
        {
            return (VariableLayoutReflection*) spReflectionEntryPoint_getParameterByIndex((SlangReflectionEntryPoint*) this, index);
        }

        SlangStage getStage()
        {
            return spReflectionEntryPoint_getStage((SlangReflectionEntryPoint*) this);
        }

        void getComputeThreadGroupSize(
            SlangUInt   axisCount,
            SlangUInt*  outSizeAlongAxis)
        {
            return spReflectionEntryPoint_getComputeThreadGroupSize((SlangReflectionEntryPoint*) this, axisCount, outSizeAlongAxis);
        }

        bool usesAnySampleRateInput()
        {
            return 0 != spReflectionEntryPoint_usesAnySampleRateInput((SlangReflectionEntryPoint*) this);
        }
    };

    struct ShaderReflection
    {
        unsigned getParameterCount()
        {
            return spReflection_GetParameterCount((SlangReflection*) this);
        }

        VariableLayoutReflection* getParameterByIndex(unsigned index)
        {
            return (VariableLayoutReflection*) spReflection_GetParameterByIndex((SlangReflection*) this, index);
        }

        static ShaderReflection* get(SlangCompileRequest* request)
        {
            return (ShaderReflection*) spGetReflection(request);
        }

        SlangUInt getEntryPointCount()
        {
            return spReflection_getEntryPointCount((SlangReflection*) this);
        }

        EntryPointReflection* getEntryPointByIndex(SlangUInt index)
        {
            return (EntryPointReflection*) spReflection_getEntryPointByIndex((SlangReflection*) this, index);
        }

        SlangUInt getGlobalConstantBufferBinding()
        {
            return spReflection_getGlobalConstantBufferBinding((SlangReflection*)this);
        }

        size_t getGlobalConstantBufferSize()
        {
            return spReflection_getGlobalConstantBufferSize((SlangReflection*)this);
        }
    };
}

#endif

#ifdef SLANG_INCLUDE_IMPLEMENTATION

#include "source/core/platform.cpp"
#include "source/core/slang-io.cpp"
#include "source/core/slang-string.cpp"
#include "source/core/stream.cpp"
#include "source/core/text-io.cpp"
#include "source/slang/bytecode.cpp"
#include "source/slang/diagnostics.cpp"
#include "source/slang/dxc-support.cpp"
#include "source/slang/emit.cpp"
#include "source/slang/ir.cpp"
#include "source/slang/ir-legalize-types.cpp"
#include "source/slang/lexer.cpp"
#include "source/slang/mangle.cpp"
#include "source/slang/name.cpp"
#include "source/slang/options.cpp"
#include "source/slang/parameter-binding.cpp"
#include "source/slang/parser.cpp"
#include "source/slang/preprocessor.cpp"
#include "source/slang/profile.cpp"
#include "source/slang/lookup.cpp"
#include "source/slang/lower.cpp"
#include "source/slang/lower-to-ir.cpp"
#include "source/slang/check.cpp"
#include "source/slang/compiler.cpp"
#include "source/slang/slang-stdlib.cpp"
#include "source/slang/source-loc.cpp"
#include "source/slang/syntax.cpp"
#include "source/slang/token.cpp"
#include "source/slang/type-layout.cpp"
#include "source/slang/reflection.cpp"
#include "source/slang/slang.cpp"
#include "source/slang/vm.cpp"

#endif

#endif
