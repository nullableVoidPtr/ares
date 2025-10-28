meta:
  id: hermes_bytecode
  title: Hermes bytecode file
  file-extension: hbc
  endian: le
  bit-endian: le
  imports:
    - vlq_base128_le
seq:
  - id: header
    type: bytecode_header
  - id: function_headers
    type: small_func_header
    repeat: expr
    repeat-expr: header.num_functions
  - id: string_kinds
    type: string_kind_entry
    size: 4
    repeat: expr
    repeat-expr: header.num_string_kinds
  - id: identifier_hashes
    type: u4
    repeat: expr
    repeat-expr: header.num_identifiers
  - id: small_string_table
    type: small_string_table_entry
    repeat: expr
    repeat-expr: header.num_strings
  - id: overflow_string_table
    type: overflow_string_table_entry
    repeat: expr
    repeat-expr: header.num_overflow_strings
  - id: string_storage
    type: string_storage
    size: header.len_string_storage
  - id: array_buffer
    type: array_buffer
    size: header.len_array_buffer
  - id: object_key_buffer
    type: object_key_buffer
    size: header.len_obj_key_buffer
  - id: object_value_buffer
    type: object_value_buffer
    size: header.len_obj_value_buffer
  - id: bigint_table
    type: bigint_table_entry
    repeat: expr
    repeat-expr: header.num_bigints
  - id: bigint_storage
    type: bigint_storage
    size: header.len_bigint_storage
  - id: regexp_table
    type: regexp_table_entry
    repeat: expr
    repeat-expr: header.num_regexps
  - id: regexp_storage
    type: regexp_storage
    size: header.len_regexp_storage
  - id: cjs_module_table
    type:
      switch-on: header.bytecode_options.cjs_modules_statically_resolved
      cases:
        false: cjs_module_table_entry
        true: cjs_module_table_static_entry
    repeat: expr
    repeat-expr: header.num_cjs_modules
  - id: function_source_table
    type: function_source_table_entry
    repeat: expr
    repeat-expr: header.num_function_sources
instances:
  debug_info:
    if: header.ofs_debug_info != 0
    type: debug_info
    pos: header.ofs_debug_info
  footer:
    if: header.version >= 75
    type: bytecode_footer
    pos: _io.size - 20
types:
  bytecode_header:
    seq:
      - id: magic
        contents: [0xc6, 0x1f, 0xbc, 0x03, 0xc1, 0x03, 0x19, 0x1f]
      - id: version
        type: u4
        valid:
          expr: _ <= 96
      - id: source_hash
        -orig-id: sourceHash
        size: 20
      - id: file_length
        -orig-id: fileLength
        type: u4
      - id: global_code_index
        type: u4
      - id: num_functions
        -orig-id: functionCount
        type: u4
      - id: num_string_kinds
        -orig-id: stringKindCount
        type: u4
      - id: num_identifiers
        -orig-id: identifierCount
        type: u4
      - id: num_strings
        -orig-id: stringCount
        type: u4
      - id: num_overflow_strings
        -orig-id: overflowStringCount
        type: u4
      - id: len_string_storage
        -orig-id: stringStorageSize
        type: u4
      - id: num_bigints
        -orig-id: bigIntCount
        type: u4
        if: version >= 87
      - id: len_bigint_storage
        -orig-id: bigIntStorageSize
        type: u4
        if: version >= 87
      - id: num_regexps
        -orig-id: regExpCount
        type: u4
      - id: len_regexp_storage
        -orig-id: regExpStorageSize
        type: u4
      - id: len_array_buffer
        -orig-id: arrayBufferSize
        type: u4
      - id: len_obj_key_buffer
        -orig-id: objKeyBufferSize
        type: u4
      - id: len_obj_value_buffer
        -orig-id: objValueBufferSize
        type: u4
      - id: segment_id
        -orig-id: segmentId
        type: u4
      - id: num_cjs_modules
        -orig-id: cjsModuleCount
        type: u4
      - id: num_function_sources
        -orig-id: functionSourceCount
        type: u4
        if: version >= 84
      - id: ofs_debug_info
        -orig-id: debugInfoOffset
        type: u4
      - id: bytecode_options
        -orig-id: options
        type: bytecode_options
        size: 1
      - id: padding
        size: (64 + 64 - _io.pos) % 64
  bytecode_options:
    seq:
      - id: static_builtins
        -orig-id: staticBuiltins
        type: b1
      - id: cjs_modules_statically_resolved
        -orig-id: cjsModulesStaticallyResolved
        type: b1
      - id: has_async
        -orig-id: hasAsync
        type: b1
        if: _root.header.version >= 82
  function_header_flag:
    seq:
      - id: prohibit_invoke
        type: b2
        enum: prohibit_invoke
      - id: strict_mode
        type: b1
      - id: has_exception_handler
        type: b1
      - id: has_debug_info
        type: b1
      - id: overflowed
        type: b1
    enums:
      prohibit_invoke:
        0: prohibit_call
        1: prohibit_construct
        2: prohibit_none
  exception_handler:
    seq:
      - id: start
        type: u4
      - id: end
        type: u4
      - id: target
        type: u4
  function_source_location_delta:
    seq:
      - id: address_delta
        type: vlq_base128_le
      - id: line_delta
        type: vlq_base128_le
        if: address_delta.value_signed != -1
      - id: column_delta
        type: vlq_base128_le
        if: address_delta.value_signed != -1
      - id: scope_address
        type: vlq_base128_le
        if: address_delta.value_signed != -1
      - id: env_reg
        type: vlq_base128_le
        if: address_delta.value_signed != -1
      - id: statement_delta
        type: vlq_base128_le
        if: 'address_delta.value_signed != -1 and (line_delta.value & 1) == 1'
  function_source_locations:
    seq:
      - id: function_index
        type: vlq_base128_le
      - id: start_line
        type: vlq_base128_le
      - id: start_column
        type: vlq_base128_le
      - id: deltas
        type: function_source_location_delta
        repeat: until
        repeat-until: _.address_delta.value_signed == -1
  function_debug_info:
    seq:
      - id: ofs_source_locations
        type: u4
      - id: scope_desc_data
        type: u4
      - id: textified_callees
        type: u4
    instances:
      source_locations:
        io: _root.debug_info.debug_data.sources_data._io
        pos: ofs_source_locations
        type: function_source_locations
  function_info:
    seq:
      - id: num_exception_handlers
        type: u4
        if: '_parent.flags.overflowed == false ? _parent.flags.has_exception_handler : _parent.large_func_header.flags.has_exception_handler'
      - id: exception_handlers
        type: exception_handler
        repeat: expr
        repeat-expr: num_exception_handlers
        if: '_parent.flags.overflowed == false ? _parent.flags.has_exception_handler : _parent.large_func_header.flags.has_exception_handler'
      - id: debug_info
        type: function_debug_info
        if: '_parent.flags.overflowed == false ? _parent.flags.has_debug_info: _parent.large_func_header.flags.has_debug_info'
  small_func_header:
    seq:
      - id: ofs_bytecode
        -origId: offset
        type: b25
      - id: num_params
        -origId: paramCount
        type: b7
      - id: len_bytecode
        -origId: bytecodeSizeInBytes
        type: b15
      - id: function_name_id
        -origId: functionName
        type: b17
      - id: ofs_info
        -origId: infoOffset
        type: b25
      - id: frame_size
        type: b7
      - id: environment_size
        type: u1
      - id: highest_read_cache_index
        type: u1
      - id: highest_write_cache_index
        type: u1
      - id: flags
        type: function_header_flag
        size: 1
    instances:
      large_func_header:
        io: _root._io
        pos: ofs_info << 16 | ofs_bytecode
        type: large_func_header
        if: flags.overflowed
      info:
        io: _root._io
        pos: 'flags.overflowed == false ? ofs_info : large_func_header.ofs_info'
        type: function_info
      bytecode:
        io: _root._io
        pos: 'flags.overflowed == false ? ofs_bytecode : large_func_header.ofs_bytecode'
        size: 'flags.overflowed == false ? len_bytecode : large_func_header.len_bytecode'
  large_func_header:
    seq:
      - id: ofs_bytecode
        -origId: offset
        type: u4
      - id: num_params
        -origId: paramCount
        type: u4
      - id: len_bytecode
        -origId: bytecodeSizeInBytes
        type: u4
      - id: function_name_id
        -origId: functionName
        type: u4
      - id: ofs_info
        -origId: infoOffset
        type: u4
      - id: frame_size
        type: u4
      - id: environment_size
        type: u4
      - id: highest_read_cache_index
        type: u1
      - id: highest_write_cache_index
        type: u1
      - id: flags
        type: function_header_flag
        size: 1
  string_kind_entry:
    seq:
      - id: count
        type: b31
      - id: kind
        type: b1
        enum: kind
    enums:
      kind:
        0: string
        1: identifier
  small_string_table_entry:
    seq:
      - id: is_utf16
        type: b1
      - id: ofs_storage
        type: b23
      - id: len_string
        type: u1
    instances:
      string:
        io: _root.string_storage._io
        pos: ofs_storage
        type: string_storage
        size: 'is_utf16 ? len_string * 2 : len_string'
        if: len_string != 0xFF
  overflow_string_table_entry:
    seq:
      - id: ofs_storage
        type: u4
      - id: len_string
        type: u4
    instances:
      string:
        io: _root.string_storage._io
        pos: ofs_storage
        type: string_storage
        size: len_string
  string_storage:
    seq:
      - id: data
        size-eos: true
  array_buffer:
    seq:
      - id: data
        size-eos: true
  object_key_buffer:
    seq:
      - id: data
        size-eos: true
  object_value_buffer:
    seq:
      - id: data
        size-eos: true
  bigint_table_entry:
    seq:
      - id: ofs_storage
        type: u4
      - id: len_bigint
        type: u4
    instances:
      bigint:
        io: _root.bigint_storage._io
        pos: ofs_storage
        type: bigint_storage
        size: len_bigint
  bigint_storage:
    seq:
      - id: data
        size-eos: true
  regexp_table_entry:
    seq:
      - id: ofs_storage
        type: u4
      - id: len_bytecode
        type: u4
    instances:
      bytecode:
        io: _root.regexp_storage._io
        pos: ofs_storage
        size: len_bytecode
  regexp_storage:
    seq:
      - id: data
        size-eos: true
  cjs_module_table_entry:
    seq:
      - id: filename_id
        type: u4
      - id: function_index
        type: u4
  cjs_module_table_static_entry:
    seq:
      - id: module_id
        type: u4
      - id: function_index
        type: u4
  function_source_table_entry:
    seq:
      - id: function_index
        type: u4
      - id: ofs_string_table
        type: u4
  string_table_entry:
    seq:
      - id: ofs_string
        type: u4
      - id: len_filename
        type: b31
      - id: is_utf16
        type: b1
    instances:
      filename:
        io: _root.debug_info.filename_storage._io
        pos: ofs_string
        type: string_storage
        size: len_filename
  debug_file_region:
    seq:
      - id: from_address
        type: u4
      - id: filename_id
        type: u4
      - id: source_mapping_url_id
        type: u4
  sources_location_data:
    seq:
      - id: data
        size-eos: true
  scope_descriptor_data:
    seq:
      - id: data
        size-eos: true
  textified_callee_data:
    seq:
      - id: data
        size-eos: true
  string_table_data:
    seq:
      - id: data
        size-eos: true
  debug_data:
    seq:
      - id: sources_data
        type: sources_location_data
        size: '(_root.header.version < 91 or _root.header.version == 93) ? _parent.ofs_lexical_data : _parent.ofs_scope_desc_data'
      - id: lexical_data
        type: scope_descriptor_data
        size: '(_root.header.version < 91 ? _parent.len_debug_data : _parent.ofs_textified_callee) - _io.pos'
        if: _root.header.version < 91 or _root.header.version == 93
      - id: scope_desc_data
        type: scope_descriptor_data
        size: '(_root.header.version < 91 ? _parent.len_debug_data : _parent.ofs_textified_callee) - _io.pos'
        if: not (_root.header.version < 91 or _root.header.version == 93)
      - id: textified_data
        type: textified_callee_data
        size: _parent.ofs_string_table - _io.pos
        if: _root.header.version >= 91
      - id: string_table
        type: string_table_data
        size: _parent.len_debug_data - _io.pos
        if: _root.header.version >= 91
  debug_info:
    seq:
      - id: num_filenames
        -origId: filenameCount
        type: u4
      - id: len_filename_storage
        -origId: filenameStorageSize
        type: u4
      - id: num_file_regions
        -origId: fileRegionCount
        type: u4
      - id: ofs_lexical_data
        -origId: lexicalDataOffset
        type: u4
        if: _parent.header.version < 91 or _parent.header.version == 93
      - id: ofs_scope_desc_data
        -origId: scopeDescDataOffset
        type: u4
        if: not (_parent.header.version < 91 or _parent.header.version == 93)
      - id: ofs_textified_callee
        -origId: textifiedCalleeOffset
        type: u4
        if: _parent.header.version >= 91
      - id: ofs_string_table
        -origId: stringTableOffset
        type: u4
        if: _parent.header.version >= 91
      - id: len_debug_data
        -origId: debugDataSize
        type: u4
      - id: filenames
        type: string_table_entry
        repeat: expr
        repeat-expr: num_filenames
      - id: filename_storage
        type: string_storage
        size: len_filename_storage
      - id: file_regions
        type: debug_file_region
        repeat: expr
        repeat-expr: num_file_regions
      - id: debug_data
        type: debug_data
        size: len_debug_data
  bytecode_footer:
    seq:
      - id: file_hash
        -orig-id: fileHash
        doc: Hash of everything above the footer
        doc-ref: facebook/hermes@1489997/include/hermes/BCGen/HBC/BytecodeFileFormat.h#L156
        size: 20
