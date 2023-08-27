#include "slang-spirv-core-grammar.h"

#include "../core/slang-rtti-util.h"
#include "../core/slang-string-util.h"
#include "slang-json-native.h"
#include "slang-core-diagnostics.h"

namespace Slang
{
using SpvWord = uint32_t;

//
// Structs which mirror the structure of spirv.core.grammar.json
//
// Commented members are those which currently don't use
struct InstructionPrintingClass
{
    UnownedStringSlice tag;
    UnownedStringSlice heading;
};
SLANG_MAKE_STRUCT_RTTI_INFO(
    InstructionPrintingClass,
    SLANG_RTTI_FIELD(tag),
    SLANG_OPTIONAL_RTTI_FIELD(heading)
);

struct Operand
{
    UnownedStringSlice kind;
    UnownedStringSlice quantifier;
    // UnownedStringSlice name;
};
SLANG_MAKE_STRUCT_RTTI_INFO(
    Operand,
    SLANG_RTTI_FIELD(kind),
    SLANG_OPTIONAL_RTTI_FIELD(quantifier)
    //SLANG_RTTI_FIELD(name),
);

struct Instruction
{
    UnownedStringSlice opname;
    UnownedStringSlice class_;
    SpvWord opcode;
    List<UnownedStringSlice> capabilities;
    List<Operand> operands;
};
SLANG_MAKE_STRUCT_RTTI_INFO(
    Instruction,
    SLANG_RTTI_FIELD(opname),
    SLANG_RTTI_FIELD_IMPL(class_, "class", 0),
    SLANG_RTTI_FIELD(opcode),
    SLANG_OPTIONAL_RTTI_FIELD(capabilities),
    SLANG_OPTIONAL_RTTI_FIELD(operands)
);

struct Enumerant
{
    UnownedStringSlice enumerant;
    JSONValue value;
    List<UnownedStringSlice> capabilities;
    // List<Operand> parameters;
    // UnownedStringSlice version;
    // UnownedStringSlice lastVersion;
    // List<UnownedStringSlice> extensions;
};
SLANG_MAKE_STRUCT_RTTI_INFO(
    Enumerant,
    SLANG_RTTI_FIELD(enumerant),
    SLANG_RTTI_FIELD(value),
    SLANG_OPTIONAL_RTTI_FIELD(capabilities),
    // SLANG_OPTIONAL_RTTI_FIELD(parameters),
    // SLANG_OPTIONAL_RTTI_FIELD(version),
    // SLANG_OPTIONAL_RTTI_FIELD(lastVersion),
    // SLANG_OPTIONAL_RTTI_FIELD(extensions)
);

struct OperandKind
{
    UnownedStringSlice category;
    UnownedStringSlice kind;
    List<Enumerant> enumerants;
};
SLANG_MAKE_STRUCT_RTTI_INFO(
    OperandKind,
    SLANG_RTTI_FIELD(category),
    SLANG_RTTI_FIELD(kind),
    SLANG_OPTIONAL_RTTI_FIELD(enumerants)
);

struct SPIRVSpec
{
    // List<UnownedStringSlice> copyright;
    // UnownedStringSlice magic_number;
    // UInt32 major_version;
    // UInt32 minor_version;
    // UInt32 revision;
    List<InstructionPrintingClass> instruction_printing_class;
    List<Instruction> instructions;
    List<OperandKind> operand_kinds;
};
SLANG_MAKE_STRUCT_RTTI_INFO(
    SPIRVSpec,
    // SLANG_RTTI_FIELD(copyright),
    // SLANG_RTTI_FIELD(magic_number),
    // SLANG_RTTI_FIELD(major_version)
    // SLANG_RTTI_FIELD(minor_version)
    // SLANG_RTTI_FIELD(revision)
    SLANG_RTTI_FIELD(instruction_printing_class),
    SLANG_RTTI_FIELD(instructions),
    SLANG_RTTI_FIELD(operand_kinds)
);

static Dictionary<String, SpvWord> operandKindToDict(
        JSONContainer& container,
        DiagnosticSink& sink,
        const OperandKind& k)
{
    Dictionary<String, SpvWord> dict;
    dict.reserve(k.enumerants.getCount());
    for(const auto& e : k.enumerants)
    {
        SpvWord valueInt = 0;
        switch(e.value.getKind())
        {
            case JSONValue::Kind::Integer:
            {
                // TODO: Range check here?
                valueInt = SpvWord(container.asInteger(e.value));
                break;
            }
            case JSONValue::Kind::String:
            {
                Int i = 0;
                const auto str = container.getString(e.value);
                if(SLANG_FAILED(StringUtil::parseInt(str, i)))
                    sink.diagnose(e.value.loc, MiscDiagnostics::spirvCoreGrammarJSONParseFailure);
                // TODO: Range check here?
                valueInt = SpvWord(i);
                break;
             }
             default:
                sink.diagnose(e.value.loc, MiscDiagnostics::spirvCoreGrammarJSONParseFailure);
        }
        dict.add(e.enumerant, valueInt);
    }
    return dict;
}

//
//
//
RefPtr<SPIRVCoreGrammarInfo> loadSPIRVCoreGrammarInfo(SourceView& source, DiagnosticSink& sink)
{
    //
    // Load the JSON
    //
    SLANG_ASSERT(source.getSourceManager() == sink.getSourceManager());
    JSONLexer lexer;
    lexer.init(&source, &sink);
    JSONParser parser;
    JSONContainer container(sink.getSourceManager());
    JSONBuilder builder(&container);
    RttiTypeFuncsMap typeMap;
    typeMap = JSONNativeUtil::getTypeFuncsMap();
    SLANG_RETURN_NULL_ON_FAIL(parser.parse(&lexer, &source, &builder, &sink));
    JSONToNativeConverter converter(&container, &typeMap, &sink);
    SPIRVSpec spec;
    if(SLANG_FAILED(converter.convert(builder.getRootValue(), &spec)))
    {
        // TODO: not having a source loc here is not great...
        sink.diagnoseWithoutSourceView(SourceLoc{}, MiscDiagnostics::spirvCoreGrammarJSONParseFailure);
        return nullptr;
    }

    //
    // Convert to the internal representation
    //
    RefPtr<SPIRVCoreGrammarInfo> res{new SPIRVCoreGrammarInfo};
    res->spvOps.dict.reserve(spec.instructions.getCount());
    for(const auto& i : spec.instructions)
        res->spvOps.dict.add(i.opname, SpvOp(i.opcode));
    for(const auto& k : spec.operand_kinds)
    {
        const auto d = operandKindToDict(container, sink, k);
        for(const auto& [n, v] : d)
            res->anyEnum.dict.add(k.kind + n, v);

        if(k.kind == "Capability")
            for(const auto& [k, v] : d)
                res->spvCapabilities.dict.add(k, SpvCapability(v));
    }
    return res;
}
}