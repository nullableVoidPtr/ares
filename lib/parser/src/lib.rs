#[allow(unused_parens)]
mod ksy;

use ksy::hermes_bytecode::{
    HermesBytecode as KaitaiHbc,
    HermesBytecode_SmallFuncHeader,
    HermesBytecode_SmallStringTableEntry,
    HermesBytecode_StringKindEntry_Kind as KaitaiStringKind,
};
use ksy::vlq_base128_le::VlqBase128Le;
use kaitai::{BytesReader, KResult, KStruct};
use wasm_bindgen::prelude::*;
extern crate console_error_panic_hook;

#[cfg(test)]
mod tests {
    use super::ksy::hermes_bytecode::HermesBytecode as KaitaiHbc;
    use kaitai::{BytesReader, KStruct};

    /// Every string in the table, resolved the way the schema resolves it --
    /// so a sample with overflow entries exercises that path too.
    fn strings_of(sample: &str) -> Vec<String> {
        let path = format!("{}/../../samples/{sample}", env!("CARGO_MANIFEST_DIR"));
        let data = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
        let reader = BytesReader::from(data);
        let parsed =
            KaitaiHbc::read_into::<BytesReader, KaitaiHbc>(&reader, None, None).unwrap();

        let table = parsed.small_string_table();
        table.iter().map(|entry| super::string_value(entry).unwrap()).collect()
    }

    #[test]
    fn parse_v96() {
        let strings = strings_of("v96/switch.hbc");
        assert!(strings.iter().any(|s| s == "default"), "{strings:?}");
    }

    #[test]
    fn parse_v99() {
        let strings = strings_of("v99/switch.hbc");
        assert!(strings.iter().any(|s| s == "default"), "{strings:?}");
    }

    fn debug_locations_of(sample: &str) -> Vec<super::FunctionDebugSourceLocationsData> {
        let path = format!("{}/../../samples/{sample}", env!("CARGO_MANIFEST_DIR"));
        let data = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
        let reader = BytesReader::from(data);
        let parsed =
            KaitaiHbc::read_into::<BytesReader, KaitaiHbc>(&reader, None, None).unwrap();

        super::parse_debug_source_locations(&parsed).unwrap()
    }

    /// v94..96 carry a scope address and environment register per location,
    /// and scale the line delta by 2.
    #[test]
    fn debug_source_locations_v96() {
        let runs = debug_locations_of("v96/switch.hbc");
        assert_eq!(runs.len(), 2);

        assert_eq!(runs[0].offset, 0);
        assert_eq!(runs[0].function_index, 0);
        assert_eq!((runs[0].start_line, runs[0].start_column), (10, 1));
        assert_eq!(runs[0].locations.len(), 5);
        assert_eq!(runs[0].locations[0].address, 34);
        assert_eq!(runs[0].locations[0].env_reg, 2);

        // Runs sit back to back, so the second starts where the first ended.
        assert_eq!(runs[1].offset, runs[0].offset + runs[0].length);
        assert_eq!(runs[1].function_index, 2);
        assert_eq!((runs[1].locations[0].line, runs[1].locations[0].column), (32, 5));
        // No environment register here, which Hermes writes as NO_REG.
        assert_eq!(runs[1].locations[0].env_reg, u32::MAX);
    }

    /// From v98 the run header carries an env index, a step can encode "no
    /// location at all", and the line delta is scaled by 8.
    #[test]
    fn debug_source_locations_v99() {
        let runs = debug_locations_of("v99/deeplyNestedFinally.hbc");
        assert!(!runs.is_empty());

        assert_eq!(runs[0].offset, 0);
        assert!(!runs[0].locations.is_empty());

        for run in &runs {
            // The fields that only exist for v94..96 stay at their empty
            // values, NO_REG being what Hermes reports for an absent register.
            for location in &run.locations {
                assert_eq!(location.scope_address, 0);
                assert_eq!(location.env_reg, u32::MAX);
            }
        }

        // A line only comes back right if the delta was shifted arithmetically,
        // which a run that jumps backwards is what proves.
        let backwards = runs.iter().any(|run| {
            run.locations.windows(2).any(|w| w[1].line < w[0].line)
        });
        assert!(backwards, "expected a backwards line delta");
    }
}

// ---------------------------------------------------------------------------
// JS-exposed enum
// ---------------------------------------------------------------------------

#[wasm_bindgen]
#[derive(Clone, Copy)]
pub enum StringKind {
    String = 0,
    Identifier = 1,
}

// ---------------------------------------------------------------------------
// Internal plain-data types (not exposed to JS)
// ---------------------------------------------------------------------------

struct KindedStringData {
    kind: StringKind,
    value: String,
}

struct ExcHandlerData {
    start: u32,
    end: u32,
    target: u32,
}

struct ObjectShapeData {
    key_buffer_offset: u32,
    num_props: u32,
}

struct DebugSourceLocationData {
    address: u32,
    line: u32,
    column: u32,
    statement: u32,
    env_idx: u32,
    scope_address: u32,
    env_reg: u32,
}

struct FunctionDebugSourceLocationsData {
    offset: u32,
    length: u32,
    function_index: u32,
    start_line: u32,
    start_column: u32,
    start_env_idx: u32,
    locations: Vec<DebugSourceLocationData>,
}

struct FunctionData {
    offset: u32,
    param_count: u32,
    frame_size: u32,
    env_size: u32,
    loop_depth: u32,
    number_reg_count: u32,
    non_ptr_reg_count: u32,
    function_name_id: u32,
    highest_read_cache_index: u32,
    highest_write_cache_index: u32,
    read_cache_size: u32,
    write_cache_size: u32,
    private_name_cache_size: u32,
    strict: bool,
    prohibit_invoke: u32,
    function_kind: u32,
    exc_handlers: Vec<ExcHandlerData>,
    bytecode: Vec<u8>,
}

// ---------------------------------------------------------------------------
// JS-exposed leaf types
// ---------------------------------------------------------------------------

#[wasm_bindgen]
pub struct KindedString {
    #[wasm_bindgen(readonly)]
    pub kind: StringKind,
    value: String,
}

#[wasm_bindgen]
impl KindedString {
    #[wasm_bindgen(getter)]
    pub fn value(&self) -> String {
        self.value.clone()
    }
}

#[wasm_bindgen]
pub struct ExceptionHandler {
    #[wasm_bindgen(readonly)]
    pub start: u32,
    #[wasm_bindgen(readonly)]
    pub end: u32,
    #[wasm_bindgen(readonly)]
    pub target: u32,
}

#[wasm_bindgen]
pub struct BigIntEntry {
    bytes: Vec<u8>,
}

#[wasm_bindgen]
impl BigIntEntry {
    /// Little-endian two's-complement digits, exactly as Hermes stored them.
    #[wasm_bindgen(getter)]
    pub fn bytes(&self) -> Vec<u8> {
        self.bytes.clone()
    }
}

#[wasm_bindgen]
pub struct ObjectShape {
    #[wasm_bindgen(readonly, js_name = "keyBufferOffset")]
    pub key_buffer_offset: u32,
    #[wasm_bindgen(readonly, js_name = "numProps")]
    pub num_props: u32,
}

/// One resolved location: the deltas the schema hands back have already been
/// accumulated, so these are the absolute values Hermes would report.
#[wasm_bindgen]
pub struct DebugSourceLocation {
    /// Bytecode offset within the owning function.
    #[wasm_bindgen(readonly)]
    pub address: u32,
    #[wasm_bindgen(readonly)]
    pub line: u32,
    #[wasm_bindgen(readonly)]
    pub column: u32,
    #[wasm_bindgen(readonly)]
    pub statement: u32,
    /// 1-based index into the scoping-info side table; 0 is "none". Only ever
    /// set from v98.
    #[wasm_bindgen(readonly, js_name = "envIdx")]
    pub env_idx: u32,
    /// v94..96 only, 0 otherwise.
    #[wasm_bindgen(readonly, js_name = "scopeAddress")]
    pub scope_address: u32,
    /// v94..96 only. `0xffffffff` -- Hermes' `NO_REG` -- means no register,
    /// and is what versions without the field report.
    #[wasm_bindgen(readonly, js_name = "envReg")]
    pub env_reg: u32,
}

/// One function's run of source locations, as stored in `sourcesData`.
#[wasm_bindgen]
pub struct FunctionDebugSourceLocations {
    /// Byte offset of this run within `sourcesData`, which is what a function
    /// header's debug info points at. Not stored: it is how far the walk had
    /// come, so it is re-derived from the encoded lengths.
    #[wasm_bindgen(readonly)]
    pub offset: u32,
    /// Bytes this run occupies, so `offset + length` is where the next one
    /// starts. Also not stored.
    #[wasm_bindgen(readonly)]
    pub length: u32,
    #[wasm_bindgen(readonly, js_name = "functionIndex")]
    pub function_index: u32,
    #[wasm_bindgen(readonly, js_name = "startLine")]
    pub start_line: u32,
    #[wasm_bindgen(readonly, js_name = "startColumn")]
    pub start_column: u32,
    #[wasm_bindgen(readonly, js_name = "startEnvIdx")]
    pub start_env_idx: u32,
    locations: Vec<DebugSourceLocationData>,
}

#[wasm_bindgen]
impl FunctionDebugSourceLocations {
    #[wasm_bindgen(getter)]
    pub fn locations(&self) -> Vec<DebugSourceLocation> {
        self.locations
            .iter()
            .map(|l| DebugSourceLocation {
                address: l.address,
                line: l.line,
                column: l.column,
                statement: l.statement,
                env_idx: l.env_idx,
                scope_address: l.scope_address,
                env_reg: l.env_reg,
            })
            .collect()
    }
}


// ---------------------------------------------------------------------------
// Function (JS-exposed)
// ---------------------------------------------------------------------------

#[wasm_bindgen]
pub struct Function {
    #[wasm_bindgen(readonly)]
    pub offset: u32,
    #[wasm_bindgen(readonly, js_name = "paramCount")]
    pub param_count: u32,
    #[wasm_bindgen(readonly, js_name = "frameSize")]
    pub frame_size: u32,
    #[wasm_bindgen(readonly, js_name = "envSize")]
    pub env_size: u32,
    #[wasm_bindgen(readonly, js_name = "loopDepth")]
    pub loop_depth: u32,
    #[wasm_bindgen(readonly, js_name = "numberRegCount")]
    pub number_reg_count: u32,
    #[wasm_bindgen(readonly, js_name = "nonPtrRegCount")]
    pub non_ptr_reg_count: u32,
    #[wasm_bindgen(readonly, js_name = "functionNameID")]
    pub function_name_id: u32,
    #[wasm_bindgen(readonly, js_name = "highestReadCacheIndex")]
    pub highest_read_cache_index: u32,
    #[wasm_bindgen(readonly, js_name = "highestWriteCacheIndex")]
    pub highest_write_cache_index: u32,
    #[wasm_bindgen(readonly, js_name = "readCacheSize")]
    pub read_cache_size: u32,
    #[wasm_bindgen(readonly, js_name = "writeCacheSize")]
    pub write_cache_size: u32,
    #[wasm_bindgen(readonly, js_name = "privateNameCacheSize")]
    pub private_name_cache_size: u32,
    #[wasm_bindgen(readonly)]
    pub strict: bool,
    #[wasm_bindgen(readonly, js_name = "prohibitInvoke")]
    pub prohibit_invoke: u32,
    #[wasm_bindgen(readonly, js_name = "functionKind")]
    pub function_kind: u32,
    exc_handlers: Vec<ExcHandlerData>,
    bytecode: Vec<u8>,
}

#[wasm_bindgen]
impl Function {
    #[wasm_bindgen(getter, js_name = "excHandlers")]
    pub fn exc_handlers(&self) -> Vec<ExceptionHandler> {
        self.exc_handlers
            .iter()
            .map(|h| ExceptionHandler { start: h.start, end: h.end, target: h.target })
            .collect()
    }

    #[wasm_bindgen(getter)]
    pub fn bytecode(&self) -> Vec<u8> {
        self.bytecode.clone()
    }
}


// ---------------------------------------------------------------------------
// Parsing helpers
// ---------------------------------------------------------------------------

/// The schema follows an overflow entry, sizes the storage and decodes it, so
/// all that is left is picking the arm it decoded into: Kaitai takes `encoding`
/// as a literal, so the two cannot be one field switching on `is_utf16`.
fn string_value(entry: &HermesBytecode_SmallStringTableEntry) -> KResult<String> {
    let string = entry.string()?;
    let value = if *entry.is_utf16() {
        string.utf16_value()
    } else {
        string.ascii_value()
    }
    .clone();

    Ok(value)
}

/// Kinds are the one part of the table the schema leaves alone: they arrive as
/// run lengths over it rather than on each entry.
fn parse_strings(hbc: &KaitaiHbc) -> KResult<Vec<KindedStringData>> {
    let string_kinds = hbc.string_kinds();
    let small_table = hbc.small_string_table();

    let mut table = Vec::new();
    let mut i: usize = 0;

    for kind_entry in string_kinds.iter() {
        let count = *kind_entry.count() as usize;
        let kind = match *kind_entry.kind() {
            KaitaiStringKind::Identifier => StringKind::Identifier,
            _ => StringKind::String,
        };

        for _ in 0..count {
            let entry = &small_table[i];
            i += 1;

            table.push(KindedStringData { kind, value: string_value(entry)? });
        }
    }

    Ok(table)
}

/// Encoded byte length of one LEB128 field. A conditional field that was not
/// present has no groups and so contributes nothing.
fn leb_len(v: &kaitai::OptRc<VlqBase128Le>) -> u32 {
    if v.is_none() { 0 } else { v.groups().len() as u32 }
}

/// The absolute value of one LEB128 field, or 0 when it is absent.
fn leb(v: &kaitai::OptRc<VlqBase128Le>) -> KResult<i64> {
    Ok(if v.is_none() { 0 } else { *v.value_signed()? })
}

/// Walk `sourcesData`, accumulating the deltas the schema decodes.
///
/// The accumulation is the one part that cannot live in the schema: Kaitai has
/// no running state. It can be faked by having each step chain onto the
/// previous one through `_parent.deltas[idx - 1]`, but that recurses once per
/// preceding step, which overruns the stack on a function with more locations
/// than the wasm stack has frames for. A loop has no such limit.
fn parse_debug_source_locations(
    hbc: &KaitaiHbc,
) -> KResult<Vec<FunctionDebugSourceLocationsData>> {
    if *hbc.header().ofs_debug_info() == 0 {
        return Ok(vec![]);
    }

    let debug_info = hbc.debug_info()?;
    let debug_data = debug_info.debug_data();
    let sources = debug_data.sources_data();
    let runs = sources.functions()?;

    let mut functions = Vec::new();
    let mut offset: u32 = 0;

    for run in runs.iter() {
        let start_line = leb(&run.start_line())?;
        let start_column = leb(&run.start_column())?;
        let start_env_idx = leb(&run.start_env_idx())?;

        let mut size = leb_len(&run.function_index())
            + leb_len(&run.start_line())
            + leb_len(&run.start_column())
            + leb_len(&run.start_env_idx());

        let mut address: i64 = 0;
        let mut line = start_line;
        let mut column = start_column;
        let mut statement: i64 = 0;
        let mut env_idx = start_env_idx;
        let mut locations = Vec::new();

        for step in run.deltas().iter() {
            size += leb_len(&step.address_delta())
                + leb_len(&step.line_delta())
                + leb_len(&step.column_delta())
                + leb_len(&step.scope_address())
                + leb_len(&step.env_reg())
                + leb_len(&step.statement_delta())
                + leb_len(&step.env_idx_delta());

            if *step.is_end()? {
                break;
            }

            address += *step.address_step()?;
            if !*step.has_location()? {
                // The address advances, but this range has no location: it is
                // not part of any user-written statement.
                continue;
            }

            line += *step.line_step()?;
            column += *step.column_step()?;
            statement += *step.statement_step()?;
            env_idx += *step.env_idx_step()?;

            // Hermes keeps every one of these in a u32 and lets them wrap, so
            // the truncation here is the model, not a lossy shortcut -- it is
            // what turns a NO_REG written as UINT32_MAX back into UINT32_MAX.
            locations.push(DebugSourceLocationData {
                address: address as u32,
                line: line as u32,
                column: column as u32,
                statement: statement as u32,
                env_idx: env_idx as u32,
                scope_address: leb(&step.scope_address())? as u32,
                env_reg: if step.env_reg().is_none() {
                    u32::MAX
                } else {
                    leb(&step.env_reg())? as u32
                },
            });
        }

        functions.push(FunctionDebugSourceLocationsData {
            offset,
            length: size,
            function_index: leb(&run.function_index())? as u32,
            start_line: start_line as u32,
            start_column: start_column as u32,
            start_env_idx: start_env_idx as u32,
            locations,
        });
        offset += size;
    }

    Ok(functions)
}

fn parse_exc_handlers(info_handlers: &[kaitai::OptRc<ksy::hermes_bytecode::HermesBytecode_ExceptionHandler>]) -> Vec<ExcHandlerData> {
    info_handlers
        .iter()
        .map(|h| ExcHandlerData {
            start: *h.start(),
            end: *h.end(),
            target: *h.target(),
        })
        .collect()
}

fn parse_function(
    header: &HermesBytecode_SmallFuncHeader,
    version: u32,
) -> KResult<FunctionData> {
    let bytecode = header.bytecode()?.to_vec();
    let flags = header.flags();

    let (
        offset,
        param_count,
        frame_size,
        function_name_id,
        loop_depth,
        number_reg_count,
        non_ptr_reg_count,
        env_size,
        highest_read_cache_index,
        highest_write_cache_index,
        read_cache_size,
        write_cache_size,
        private_name_cache_size,
        strict,
        prohibit_invoke,
        function_kind,
        has_exc_handlers,
        exc_handlers,
    );

    if !*flags.overflowed() {
        offset = *header.ofs_bytecode()?;
        param_count = *header.num_params()?;
        frame_size = *header.frame_size()?;
        function_name_id = *header.function_name_id()?;

        if version >= 98 {
            loop_depth = *header.loop_depth()?;
            number_reg_count = *header.num_number_reg()?;
            non_ptr_reg_count = *header.num_nonptr_reg()?;
            env_size = 0;
            highest_read_cache_index = 0;
            highest_write_cache_index = 0;
            read_cache_size = *header.len_read_cache()?;
            write_cache_size = *header.len_write_cache()?;
            private_name_cache_size = *header.len_private_name_cache()?;
        } else {
            loop_depth = 0;
            number_reg_count = 0;
            non_ptr_reg_count = 0;
            env_size = *header.environment_size()?;
            highest_read_cache_index = *header.highest_read_cache_index()?;
            highest_write_cache_index = *header.highest_write_cache_index()?;
            read_cache_size = 0;
            write_cache_size = 0;
            private_name_cache_size = 0;
        }

        strict = *flags.strict_mode();
        prohibit_invoke = i64::from(&*flags.prohibit_invoke()) as u32;
        function_kind = if version >= 98 { i64::from(&*flags.kind()) as u32 } else { 0 };
        has_exc_handlers = *flags.has_exception_handler();

        exc_handlers = if has_exc_handlers {
            parse_exc_handlers(&header.info()?.exception_handlers())
        } else {
            vec![]
        };
    } else {
        let large = header.large_func_header()?;
        let lflags = large.flags();

        offset = *large.ofs_bytecode();
        param_count = *large.num_params();
        frame_size = *large.frame_size();
        function_name_id = *large.function_name_id();

        if version >= 98 {
            loop_depth = *large.loop_depth();
            number_reg_count = *large.num_number_reg();
            non_ptr_reg_count = *large.num_nonptr_reg();
            env_size = 0;
            highest_read_cache_index = 0;
            highest_write_cache_index = 0;
            read_cache_size = *large.len_read_cache() as u32;
            write_cache_size = *large.len_write_cache() as u32;
            private_name_cache_size = *large.len_private_name_cache() as u32;
        } else {
            loop_depth = 0;
            number_reg_count = 0;
            non_ptr_reg_count = 0;
            env_size = *large.environment_size();
            highest_read_cache_index = *large.highest_read_cache_index() as u32;
            highest_write_cache_index = *large.highest_write_cache_index() as u32;
            read_cache_size = 0;
            write_cache_size = 0;
            private_name_cache_size = 0;
        }

        strict = *lflags.strict_mode();
        prohibit_invoke = i64::from(&*lflags.prohibit_invoke()) as u32;
        function_kind = if version >= 98 { i64::from(&*lflags.kind()) as u32 } else { 0 };
        has_exc_handlers = *lflags.has_exception_handler();

        exc_handlers = if has_exc_handlers {
            let info = if version >= 98 { large.info() } else { large.info_legacy() };
            let handlers = info.exception_handlers();
            parse_exc_handlers(&handlers)
        } else {
            vec![]
        };
    }

    Ok(FunctionData {
        offset,
        param_count,
        frame_size,
        env_size,
        loop_depth,
        number_reg_count,
        non_ptr_reg_count,
        function_name_id,
        highest_read_cache_index,
        highest_write_cache_index,
        read_cache_size,
        write_cache_size,
        private_name_cache_size,
        strict,
        prohibit_invoke,
        function_kind,
        exc_handlers,
        bytecode,
    })
}

// ---------------------------------------------------------------------------
// HermesBytecode — the main exported class
// ---------------------------------------------------------------------------

#[wasm_bindgen]
pub struct HermesBytecode {
    version: u32,
    strings: Vec<KindedStringData>,
    functions: Vec<FunctionData>,
    array_buffer: Vec<u8>,
    literal_value_buffer: Vec<u8>,
    object_key_buffer: Vec<u8>,
    object_value_buffer: Vec<u8>,
    object_shapes: Vec<ObjectShapeData>,
    bigints: Vec<Vec<u8>>,
    /// `None` unless the caller asked for it -- see `new`.
    debug_source_locations: Option<Vec<FunctionDebugSourceLocationsData>>,
}

#[wasm_bindgen]
impl HermesBytecode {
    /// Parse a bytecode file.
    ///
    /// `with_debug_info` is off by default because resolving `sourcesData`
    /// costs roughly 2KB per source location -- hundreds of MB on a bundle
    /// that shipped its debug info -- and nothing needs it to disassemble.
    /// Pass `true` to make `debugSourceLocations` available.
    #[wasm_bindgen(constructor)]
    pub fn new(
        data: &[u8],
        with_debug_info: Option<bool>,
    ) -> Result<HermesBytecode, JsValue> {
        console_error_panic_hook::set_once();
        let reader = BytesReader::from(data.to_vec());
        let parsed = KaitaiHbc::read_into::<BytesReader, KaitaiHbc>(&reader, None, None)
            .map_err(|e| JsValue::from_str(&format!("{e:?}")))?;
        let hbc = &*parsed;

        let version = *hbc.header().version();

        let strings =
            parse_strings(hbc).map_err(|e| JsValue::from_str(&format!("{e:?}")))?;

        let functions = hbc
            .function_headers()
            .iter()
            .map(|h| parse_function(h, version))
            .collect::<KResult<Vec<_>>>()
            .map_err(|e| JsValue::from_str(&format!("{e:?}")))?;

        let array_buffer = if version <= 96 {
            hbc.array_buffer().data().to_vec()
        } else {
            vec![]
        };

        let literal_value_buffer = if version >= 97 {
            hbc.literal_value_buffer().data().to_vec()
        } else {
            vec![]
        };

        let object_key_buffer = hbc.object_key_buffer().data().to_vec();

        let object_value_buffer = if version <= 96 {
            hbc.object_value_buffer().data().to_vec()
        } else {
            vec![]
        };

        let object_shapes = if version >= 97 {
            hbc.object_shapes()
                .iter()
                .map(|s| ObjectShapeData {
                    key_buffer_offset: *s.ofs_key_buffer(),
                    num_props: *s.num_props(),
                })
                .collect()
        } else {
            vec![]
        };

        // Stays unparsed unless asked for; empty when the file carries no
        // debug info at all.
        let debug_source_locations = if with_debug_info.unwrap_or(false) {
            Some(
                parse_debug_source_locations(hbc)
                    .map_err(|e| JsValue::from_str(&format!("{e:?}")))?,
            )
        } else {
            None
        };

        // Each entry points into the shared bigint storage; the resolved
        // instance is the entry's own slice of it.
        let bigints = hbc
            .bigint_table()
            .iter()
            .map(|e| match e.bigint() {
                Ok(storage) => storage.data().to_vec(),
                Err(_) => Vec::new(),
            })
            .collect();

        Ok(HermesBytecode {
            version,
            strings,
            functions,
            array_buffer,
            literal_value_buffer,
            object_key_buffer,
            object_value_buffer,
            object_shapes,
            bigints,
            debug_source_locations,
        })
    }

    #[wasm_bindgen(getter)]
    pub fn version(&self) -> u32 {
        self.version
    }

    #[wasm_bindgen(getter)]
    pub fn strings(&self) -> Vec<KindedString> {
        self.strings
            .iter()
            .map(|d| KindedString { kind: d.kind, value: d.value.clone() })
            .collect()
    }

    #[wasm_bindgen(getter)]
    pub fn functions(&self) -> Vec<Function> {
        self.functions
            .iter()
            .map(|d| Function {
                offset: d.offset,
                param_count: d.param_count,
                frame_size: d.frame_size,
                env_size: d.env_size,
                loop_depth: d.loop_depth,
                number_reg_count: d.number_reg_count,
                non_ptr_reg_count: d.non_ptr_reg_count,
                function_name_id: d.function_name_id,
                highest_read_cache_index: d.highest_read_cache_index,
                highest_write_cache_index: d.highest_write_cache_index,
                read_cache_size: d.read_cache_size,
                write_cache_size: d.write_cache_size,
                private_name_cache_size: d.private_name_cache_size,
                strict: d.strict,
                prohibit_invoke: d.prohibit_invoke,
                function_kind: d.function_kind,
                exc_handlers: d.exc_handlers.iter()
                    .map(|h| ExcHandlerData { start: h.start, end: h.end, target: h.target })
                    .collect(),
                bytecode: d.bytecode.clone(),
            })
            .collect()
    }

    #[wasm_bindgen(getter, js_name = "arrayBuffer")]
    pub fn array_buffer(&self) -> Vec<u8> {
        self.array_buffer.clone()
    }

    #[wasm_bindgen(getter, js_name = "literalValueBuffer")]
    pub fn literal_value_buffer(&self) -> Vec<u8> {
        self.literal_value_buffer.clone()
    }

    #[wasm_bindgen(getter, js_name = "objectKeyBuffer")]
    pub fn object_key_buffer(&self) -> Vec<u8> {
        self.object_key_buffer.clone()
    }

    #[wasm_bindgen(getter, js_name = "objectValueBuffer")]
    pub fn object_value_buffer(&self) -> Vec<u8> {
        self.object_value_buffer.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn bigints(&self) -> Vec<BigIntEntry> {
        self.bigints
            .iter()
            .map(|b| BigIntEntry { bytes: b.clone() })
            .collect()
    }

    /// Throws unless the parser was constructed with `withDebugInfo`, rather
    /// than quietly reporting a file with debug info as having none.
    #[wasm_bindgen(getter, js_name = "debugSourceLocations")]
    pub fn debug_source_locations(
        &self,
    ) -> Result<Vec<FunctionDebugSourceLocations>, JsValue> {
        let functions = self.debug_source_locations.as_ref().ok_or_else(|| {
            JsValue::from_str(
                "debug source locations were not parsed: construct \
                 HermesBytecode with with_debug_info = true",
            )
        })?;

        Ok(functions
            .iter()
            .map(|f| FunctionDebugSourceLocations {
                offset: f.offset,
                length: f.length,
                function_index: f.function_index,
                start_line: f.start_line,
                start_column: f.start_column,
                start_env_idx: f.start_env_idx,
                locations: f
                    .locations
                    .iter()
                    .map(|l| DebugSourceLocationData {
                        address: l.address,
                        line: l.line,
                        column: l.column,
                        statement: l.statement,
                        env_idx: l.env_idx,
                        scope_address: l.scope_address,
                        env_reg: l.env_reg,
                    })
                    .collect(),
            })
            .collect())
    }

    #[wasm_bindgen(getter, js_name = "objectShapes")]
    pub fn object_shapes(&self) -> Vec<ObjectShape> {
        self.object_shapes
            .iter()
            .map(|d| ObjectShape { key_buffer_offset: d.key_buffer_offset, num_props: d.num_props })
            .collect()
    }
}
