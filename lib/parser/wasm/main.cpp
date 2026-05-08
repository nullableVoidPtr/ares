#include <emscripten/bind.h>
#include "hermes_bytecode.h"
#include <kaitai/kaitaistream.h>
#include <fstream>
#include <sstream>
#include <iostream>
#include <vector>
#include <memory>

using namespace emscripten;

struct Uint8Array : public ::emscripten::val {
    explicit Uint8Array(val const &other) : val(other) {};
    Uint8Array() : val(val::global("Uint8Array").new_()) {};
};

struct kinded_string_t {
    uint32_t kind;
    bool isUTF16;
    Uint8Array value;

    kinded_string_t(uint32_t kind, bool isUTF16, const std::string& value) : kind(kind), isUTF16(isUTF16) {
        this->value = Uint8Array(val::global("Uint8Array").new_(
            val(memory_view<uint8_t>(value.size(), reinterpret_cast<const uint8_t*>(value.data())))
        ));
    };
};

struct exception_handler_t {
    uint32_t start;
    uint32_t end;
    uint32_t target;
    exception_handler_t() : start(-1), end(-1), target(-1) {}
    exception_handler_t(uint32_t start, uint32_t end, uint32_t target) : start(start), end(end), target(target) {}
};

struct function_t {
    uint32_t offset;
    uint32_t paramCount;
    uint32_t frameSize;
    uint32_t envSize;
    uint32_t functionNameID;
    uint32_t highestReadCacheIndex;
    uint32_t highestWriteCacheIndex;

    bool strict;
    uint32_t prohibitInvoke;
    std::vector<exception_handler_t> excHandlers;

    Uint8Array bytecode = Uint8Array(val::global("Uint8Array").new_());

    function_t() {}; 
    function_t(hermes_bytecode_t::small_func_header_t* header) {
        auto bytecode = header->bytecode();
        this->bytecode = Uint8Array(val::global("Uint8Array").new_(
            val(memory_view<uint8_t>(bytecode.size(), reinterpret_cast<const uint8_t*>(bytecode.data())))
        ));

        auto info = header->info();

        bool has_exception_handlers;
        bool has_debug_info;
        if (!header->flags()->overflowed()) {
            offset = header->ofs_bytecode();
            paramCount = header->num_params();
            frameSize = header->frame_size();
            envSize = header->environment_size();
            functionNameID = header->function_name_id();
            highestReadCacheIndex = header->highest_read_cache_index();
            highestWriteCacheIndex = header->highest_write_cache_index();

            strict = header->flags()->strict_mode();
            prohibitInvoke = header->flags()->prohibit_invoke();
            has_exception_handlers = header->flags()->has_exception_handler();
            has_debug_info = header->flags()->has_debug_info();
        } else {
            auto large_header = header->large_func_header();
            offset = large_header->ofs_bytecode();
            paramCount = large_header->num_params();
            frameSize = large_header->frame_size();
            envSize = large_header->environment_size();
            functionNameID = large_header->function_name_id();
            highestReadCacheIndex = large_header->highest_read_cache_index();
            highestWriteCacheIndex = large_header->highest_write_cache_index();
            
            strict = header->flags()->strict_mode();
            prohibitInvoke = header->flags()->prohibit_invoke();
            has_exception_handlers = large_header->flags()->has_exception_handler();
            has_debug_info = large_header->flags()->has_debug_info();
        }

        if (has_exception_handlers) {
            for (auto handler : *header->info()->exception_handlers()) {
                excHandlers.emplace_back(handler->start(), handler->end(), handler->target());
            }
        }
    };
};

class HermesBytecode : hermes_bytecode_t {
private:
    std::shared_ptr<kaitai::kstream> m_ks;
public:
    explicit HermesBytecode(std::shared_ptr<kaitai::kstream> ks)
        : hermes_bytecode_t(ks.get()), m_ks(std::move(ks)) {}

    static std::shared_ptr<HermesBytecode> fromBytes(const std::string& data) {
        auto ks = std::make_shared<kaitai::kstream>(data);
        return std::make_shared<HermesBytecode>(std::move(ks));
    }

    uint32_t version() const { return header()->version(); }

    std::vector<kinded_string_t> strings() const {
        std::vector<kinded_string_t> table;

        auto string_kinds = *this->string_kinds();
        auto small_string_table = *this->small_string_table();
        auto overflow_string_table = *this->overflow_string_table();

        uint32_t i = 0;
        for (uint32_t j = 0; j < string_kinds.size(); j++) {
            auto count = string_kinds[j]->count();
            for (uint32_t k = 0; k < count; k++) {
                auto entry = small_string_table[i++];
                std::string s;
                if (entry->len_string() == 0xFF) {
                    s = overflow_string_table[entry->ofs_storage()]->string()->data();
                } else {
                    s = entry->string()->data();
                }

                table.emplace_back(string_kinds[j]->kind(), entry->is_utf16(), s);
            }
        }

        return table;
    }
    
    std::vector<function_t> functions() const {
        std::vector<function_t> functions;

        for (auto header : *this->function_headers()) {
            functions.emplace_back(header);
        }

        return functions;
    }
};

EMSCRIPTEN_BINDINGS(hermes_bytecode) {
    register_type<Uint8Array>("Uint8Array");

	class_<kinded_string_t>("KindedString")
	.property("kind", &kinded_string_t::kind)
	.property("isUTF16", &kinded_string_t::isUTF16)
	.property("value", &kinded_string_t::value)
	;
    register_vector<kinded_string_t>("StringTable")
    ;

	value_object<exception_handler_t>("ExceptionHandler")
	.field("start", &exception_handler_t::start)
	.field("end", &exception_handler_t::end)
	.field("target", &exception_handler_t::target)
	;
    register_vector<exception_handler_t>("ExceptionHandlers")
    ;

	class_<function_t>("Function")
    .property("offset", &function_t::offset)
    .property("paramCount", &function_t::paramCount)
    .property("frameSize", &function_t::frameSize)
    .property("envSize", &function_t::envSize)
    .property("functionNameID", &function_t::functionNameID)
    .property("highestReadCacheIndex", &function_t::highestReadCacheIndex)
    .property("highestWriteCacheIndex", &function_t::highestWriteCacheIndex)
    .property("strict", &function_t::strict)
    .property("prohibitInvoke", &function_t::prohibitInvoke)
    .property("excHandlers", &function_t::excHandlers)
    .property("bytecode", &function_t::bytecode)
	;
    register_vector<function_t>("Functions")
    ;

	class_<HermesBytecode>("HermesBytecode")
	.smart_ptr_constructor("HermesBytecode", &HermesBytecode::fromBytes)
	.property("version", &HermesBytecode::version)
	.property("strings", &HermesBytecode::strings)
	.property("functions", &HermesBytecode::functions)
	;
}



