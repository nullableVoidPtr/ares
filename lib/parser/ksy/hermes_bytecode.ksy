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
  - id: function_headers_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: function_headers
    type: small_func_header
    repeat: expr
    repeat-expr: header.num_functions
  - id: string_kinds_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: string_kinds
    type: string_kind_entry
    size: 4
    repeat: expr
    repeat-expr: header.num_string_kinds
  - id: identifier_hashes_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: identifier_hashes
    type: u4
    repeat: expr
    repeat-expr: header.num_identifiers
  - id: small_string_table_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: small_string_table
    type: small_string_table_entry
    repeat: expr
    repeat-expr: header.num_strings
  - id: overflow_string_table_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: overflow_string_table
    type: overflow_string_table_entry
    repeat: expr
    repeat-expr: header.num_overflow_strings
  - id: string_storage_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: string_storage
    type: string_storage
    size: header.len_string_storage
  - id: array_buffer_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: array_buffer
    type: array_buffer
    size: header.len_array_buffer
    if: header.version <= 96
  - id: literal_value_buffer
    type: literal_value_buffer
    size: header.len_literal_value_buffer
    if: header.version >= 97
  - id: object_key_buffer_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: object_key_buffer
    type: object_key_buffer
    size: header.len_obj_key_buffer
  - id: object_value_buffer_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: object_value_buffer
    type: object_value_buffer
    size: header.len_obj_value_buffer
    if: header.version <= 96
  - id: object_shapes_align
    size: '(4 - (_io.pos % 4)) % 4'
    if: header.version >= 97
  - id: object_shapes
    type: object_shape
    repeat: expr
    repeat-expr: header.num_obj_shapes
    if: header.version >= 97
  - id: bigint_table_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: bigint_table
    type: bigint_table_entry
    repeat: expr
    repeat-expr: header.num_bigints
  - id: bigint_storage_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: bigint_storage
    type: bigint_storage
    size: header.len_bigint_storage
  - id: regexp_table_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: regexp_table
    type: regexp_table_entry
    repeat: expr
    repeat-expr: header.num_regexps
  - id: regexp_storage_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: regexp_storage
    type: regexp_storage
    size: header.len_regexp_storage
  - id: cjs_module_table_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: cjs_module_table
    type:
      switch-on: cjs_modules_statically_resolved
      cases:
        false: cjs_module_table_entry
        true: cjs_module_table_static_entry
    repeat: expr
    repeat-expr: header.num_cjs_modules
  - id: function_source_table_align
    size: '(4 - (_io.pos % 4)) % 4'
  - id: function_source_table
    type: function_source_table_entry
    repeat: expr
    repeat-expr: header.num_function_sources
instances:
  # Hoisted from the switch-on in cjs_module_table so the Rust target can
  # cache the value in a RefCell on self. A chained field access like
  # header.bytecode_options.cjs_modules_statically_resolved used directly in
  # switch-on generates a chain of temporary Ref<'_> borrows that are dropped
  # before the switch body executes, causing a compile error.
  cjs_modules_statically_resolved:
    value: header.bytecode_options.cjs_modules_statically_resolved
  debug_info:
    if: header.ofs_debug_info != 0
    type: debug_info
    pos: header.ofs_debug_info
  footer:
    if: header.version >= 75
    type: bytecode_footer
    pos: _io.size - 20
types:
  u3:
    seq:
      - id: b0
        type: u1
      - id: b1
        type: u1
      - id: b2
        type: u1
    instances:
      value:
        value: '(b0.as<u4> | b1.as<u4> << 8 | b2.as<u4> << 16).as<u4>'
  bytecode_header:
    seq:
      - id: magic
        contents: [0xc6, 0x1f, 0xbc, 0x03, 0xc1, 0x03, 0x19, 0x1f]
      - id: version
        type: u4
        valid:
          expr: _ <= 99
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
        if: version <= 96
      - id: len_literal_value_buffer
        -orig-id: literalValueBufferSize
        type: u4
        if: version >= 97
      - id: len_obj_key_buffer
        -orig-id: objKeyBufferSize
        type: u4
      - id: len_obj_value_buffer
        -orig-id: objValueBufferSize
        type: u4
        if: version <= 96
      - id: num_obj_shapes
        -orig-id: objShapeTableCount
        type: u4
        if: version >= 97
      - id: num_string_switch_imms
        -orig-id: numStringSwitchImms
        type: u4
        if: version >= 98
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
        # _parent here is bytecode_header; version is its second seq field, already read
        # before bytecode_options. Using _root.header.version would panic in Rust because
        # the root's header OptRc<> weak pointer is not yet live during this read phase.
        if: _parent.version >= 82
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
      - id: kind
        type: b2
        enum: kind
        if: _root.header.version >= 98
    enums:
      prohibit_invoke:
        0: prohibit_call
        1: prohibit_construct
        2: prohibit_none
      kind:
        0: normal_function
        1: generator_function
        2: async_function
  exception_handler:
    seq:
      - id: start
        type: u4
      - id: end
        type: u4
      - id: target
        type: u4
  function_source_location_delta:
    doc: |
      One step of a function's source location run. Everything is a delta
      against the previous emitted location, so a reader accumulates as it
      goes; the fields present depend on the bytecode version and on flag bits
      packed into the low end of line_delta. An address delta of -1 ends the
      run rather than describing a location.

      The shape has changed three times, all of them visible here:

      * <= 93 -- column, then a statement delta if bit 0 of line_delta is set.
        The line delta is the rest of line_delta, so it is scaled by 2.
      * 94 .. 96 -- as above plus an absolute scope address and environment
        register after the column, added in v94 (facebook/hermes@1c71748).
      * >= 98 -- bit 0 now means "this step has a location at all", bit 1 the
        statement delta and bit 2 an env index delta, so the line delta is
        scaled by 8. Scope address and environment register are gone
        (facebook/hermes@0ebb08c, @900794b, @bdbf40a).

      Version 97 is treated as <= 93. Nothing was ever released as 97 -- it
      existed only on trunk between the bump and the 98 bump -- and for most
      of that window it carried this shape.
    seq:
      - id: address_delta
        type: vlq_base128_le
      - id: line_delta
        type: vlq_base128_le
        if: not is_end
      - id: column_delta
        type: vlq_base128_le
        if: not is_end and has_location
      - id: scope_address
        -origId: scopeAddress
        doc: Absolute, unlike everything else here.
        type: vlq_base128_le
        if: not is_end and has_scope_fields
      - id: env_reg
        -origId: envReg
        doc: 'Absolute. UINT32_MAX means no register: Hermes'' NO_REG.'
        type: vlq_base128_le
        if: not is_end and has_scope_fields
      - id: statement_delta
        type: vlq_base128_le
        if: not is_end and has_statement
      - id: env_idx_delta
        type: vlq_base128_le
        if: not is_end and has_env_idx
    instances:
      is_end:
        doc: An address delta of -1 terminates the run; no other field follows.
        value: address_delta.value_signed == -1
      has_scope_fields:
        value: '_root.header.version >= 94 and _root.header.version <= 96'
      has_location:
        doc: |
          Before 98 every step carried a location, so there was no bit for it.
        value: '_root.header.version <= 97 ? true : (line_delta.value_signed & 1) != 0'
      has_statement:
        value: '_root.header.version <= 97 ? (line_delta.value_signed & 1) != 0 : (has_location and (line_delta.value_signed & 2) != 0)'
      has_env_idx:
        value: '_root.header.version >= 98 and has_location and (line_delta.value_signed & 4) != 0'
      line_flags:
        doc: |
          The flag bits occupying the low end of line_delta, reconstructed so
          they can be subtracted off. The writer builds line_delta by shifting
          the line up and OR-ing these in, which on a cleared low end is the
          same as adding them.
        value: '(_root.header.version <= 97 ? (has_statement ? 1 : 0) : (1 + (has_statement ? 2 : 0) + (has_env_idx ? 4 : 0))).as<s8>'
      line_scale:
        value: '(_root.header.version <= 97 ? 2 : 8).as<s8>'
      line_step:
        doc: |
          Divides rather than shifting right: KSC's Rust target compiles `>>`
          as a logical shift, which mangles a negative line delta. Taking the
          flag bits off first makes the division exact, so it is the arithmetic
          shift the writer meant either way.
        value: '((is_end or not has_location) ? 0 : (line_delta.value_signed - line_flags) / line_scale).as<s8>'
      column_step:
        value: '((is_end or not has_location) ? 0 : column_delta.value_signed).as<s8>'
      statement_step:
        value: '(has_statement ? statement_delta.value_signed : 0).as<s8>'
      env_idx_step:
        value: '(has_env_idx ? env_idx_delta.value_signed : 0).as<s8>'
      address_step:
        doc: |
          Advances even on a step with no location, which is how a bytecode
          range gets marked as belonging to no statement at all.
        value: '(is_end ? 0 : address_delta.value_signed).as<s8>'
  function_source_locations:
    doc: |
      One function's run of source locations, starting from an absolute line
      and column and stepping through deltas until one of them ends the run.
      Runs sit back to back with no table and no padding, and a function
      header's debug info points at one by its byte offset into this section.
    seq:
      - id: function_index
        type: vlq_base128_le
      - id: start_line
        type: vlq_base128_le
      - id: start_column
        type: vlq_base128_le
      - id: start_env_idx
        type: vlq_base128_le
        if: _root.header.version >= 98
      - id: deltas
        type: function_source_location_delta
        repeat: until
        repeat-until: _.is_end
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
  large_function_info:
    seq:
      - id: num_exception_handlers
        type: u4
        if: _parent.flags.has_exception_handler
      - id: exception_handlers
        type: exception_handler
        repeat: expr
        repeat-expr: num_exception_handlers
        if: _parent.flags.has_exception_handler
      - id: debug_info
        type: function_debug_info
        if: _parent.flags.has_debug_info
  small_func_header:
    seq:
      - id: word0
        type: u4
      - id: word1
        type: u4
      - id: word2_legacy
        type: u4
        if: _root.header.version <= 97
      - id: word2
        type: u3
        if: _root.header.version >= 98
      - id: word3_legacy
        type: u3
        if: _root.header.version <= 97
      - id: flags
        type: function_header_flag
        size: 1
    instances:
      ofs_bytecode:
        -origId: offset
        value: '(word0 & 0x1ffffff).as<u4>'
      num_params:
        -origId: paramCount
        value: '((word0 >> 25) & (_root.header.version >= 98 ? 0x1f : 0x7f)).as<u4>'
      loop_depth:
        -origId: loopDepth
        value: '(word0 >> 30).as<u4>'
        if: _root.header.version >= 98
      len_bytecode:
        -origId: bytecodeSizeInBytes
        value: '(word1 & (_root.header.version >= 98 ? 0x3fff : 0x7fff)).as<u4>'
      function_name_id:
        -origId: functionName
        value: '((word1 >> (_root.header.version >= 98 ? 14 : 15)) & (_root.header.version >= 98 ? 0xff : 0x1ffff)).as<u4>'
      num_number_reg:
        -origId: numberRegCount
        value: '((word1 >> 22) & 0x1f).as<u4>'
        if: _root.header.version >= 98
      num_nonptr_reg:
        -origId: nonPtrRegCount
        value: '(word1 >> 27).as<u4>'
        if: _root.header.version >= 98
      ofs_info:
        -origId: infoOffset
        value: '(word2_legacy & 0x1ffffff).as<u4>'
        if: _root.header.version <= 97
      frame_size:
        value: '(_root.header.version >= 98 ? (word2.value & 0xff).as<u4> : (word2_legacy >> 25).as<u4>)'
      environment_size:
        value: '(word3_legacy.value & 0xff).as<u4>'
        if: _root.header.version <= 97
      highest_read_cache_index:
        value: '((word3_legacy.value >> 8) & 0xff).as<u4>'
        if: _root.header.version <= 97
      len_read_cache:
        -origId: readCacheSize
        value: '((word2.value >> 8) & 0xff).as<u4>'
        if: _root.header.version >= 98
      highest_write_cache_index:
        value: '(word3_legacy.value >> 16).as<u4>'
        if: _root.header.version <= 97
      len_write_cache:
        -origId: writeCacheSize
        value: '((word2.value >> 16) & 0x7f).as<u4>'
        if: _root.header.version >= 98
      len_private_name_cache:
        -origId: privateNameCacheSize
        value: '((word2.value >> 23) & 0x1).as<u4>'
        if: _root.header.version >= 98
      large_func_header_offset:
        value: '(_root.header.version >= 98 ? (function_name_id << 24 | ofs_bytecode) : (_root.header.version == 97 ? (function_name_id << 16 | ofs_bytecode) : (ofs_info << 16 | ofs_bytecode))).as<u4>'
        if: flags.overflowed
      large_func_header:
        io: _root._io
        pos: large_func_header_offset
        type: large_func_header
        if: flags.overflowed
      info:
        io: _root._io
        pos: ofs_info
        type: function_info
        if: _root.header.version <= 97 and flags.overflowed == false
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
      - id: loop_depth
        -origId: loopDepth
        type: u4
        if: _root.header.version >= 98 
      - id: len_bytecode
        -origId: bytecodeSizeInBytes
        type: u4
      - id: function_name_id
        -origId: functionName
        type: u4
      - id: num_number_reg
        -origId: numberRegCount
        type: u4
        if: _root.header.version >= 98
      - id: num_nonptr_reg
        -origId: nonPtrRegCount
        type: u4
        if: _root.header.version >= 98
      - id: ofs_info
        -origId: infoOffset
        type: u4
        if: _root.header.version <= 96
      - id: frame_size
        type: u4
      - id: environment_size
        type: u4
        if: _root.header.version <= 96
      - id: highest_read_cache_index
        type: u1
        if: _root.header.version <= 97
      - id: len_read_cache
        -origId: readCacheSize
        type: u1
        if: _root.header.version >= 98
      - id: highest_write_cache_index
        type: u1
        if: _root.header.version <= 97
      - id: len_write_cache
        -origId: writeCacheSize
        type: u1
        if: _root.header.version >= 98
      - id: len_private_name_cache
        -origId: privateNameCacheSize
        type: u1
        if: _root.header.version >= 98
      - id: flags
        type: function_header_flag
        size: 1
      - id: info_align
        size: '(4 - (_io.pos % 4)) % 4'
        if: '_root.header.version >= 98 and (flags.has_exception_handler or flags.has_debug_info)'
      - id: info
        type: large_function_info
        if: '_root.header.version >= 98 and (flags.has_exception_handler or flags.has_debug_info)'
      - id: info_legacy_align
        size: '(4 - (_io.pos % 4)) % 4'
        if: '_root.header.version <= 97 and (flags.has_exception_handler or flags.has_debug_info)'
      - id: info_legacy
        type: large_function_info
        if: '_root.header.version <= 97 and (flags.has_exception_handler or flags.has_debug_info)'
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
      is_overflow:
        doc: |
          A length of 0xff is a sentinel rather than a length: ofs_storage is
          then an index into the overflow table, not an offset into storage.
        value: len_string == 0xFF
      overflow:
        value: _root.overflow_string_table[ofs_storage]
        if: is_overflow
      ofs_data:
        value: '(is_overflow ? overflow.ofs_storage : ofs_storage.as<u4>).as<u4>'
      len_chars:
        doc: |
          Characters, not bytes -- an overflow entry counts them the same way a
          small one does, so the utf-16 scaling below applies to both.
        value: '(is_overflow ? overflow.len_string : len_string.as<u4>).as<u4>'
      len_data:
        value: '(is_utf16 ? len_chars * 2 : len_chars).as<u4>'
      string:
        io: _root.string_storage._io
        pos: ofs_data
        size: len_data
        type: hermes_string
  hermes_string:
    doc: |
      A string as Hermes stores it: one byte per character when every character
      is ASCII, otherwise utf-16le. Only the small string table entry pointing
      here records which, so the encoding comes off _parent -- an overflow
      entry, reached through one, can neither size nor decode itself.

      The two arms are separate fields because `encoding` is a literal and
      cannot switch on is_utf16; exactly one of them is ever present, and a
      caller picks by the same _parent.is_utf16 it was read with.

      The ASCII arm is decoded as utf-8 so that a byte above 0x7f -- which
      Hermes never emits on this path -- becomes U+FFFD rather than silently
      passing through as a latin-1 character.
    seq:
      - id: ascii_value
        type: str
        size-eos: true
        encoding: UTF-8
        if: not _parent.is_utf16
      - id: utf16_value
        type: str
        size-eos: true
        encoding: UTF-16LE
        if: _parent.is_utf16
  overflow_string_table_entry:
    seq:
      - id: ofs_storage
        type: u4
      - id: len_string
        type: u4
  string_storage:
    seq:
      - id: data
        size-eos: true
  array_buffer:
    seq:
      - id: data
        size-eos: true
  literal_value_buffer:
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
  object_shape:
    seq:
      - id: ofs_key_buffer
        -origId: keyBufferOffset
        type: u4
      - id: num_props
        type: u4
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
    doc: |
      The whole section is one run per function, back to back, so it is walked
      from 0 to the end rather than indexed.

      An instance rather than a seq field so that reading a file does not pay
      for it: the runs expand to a couple of KB apiece once parsed, which on a
      bundle that kept its debug info dwarfs everything else in the file.
    instances:
      functions:
        pos: 0
        type: function_source_locations
        repeat: eos
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
      # From 98 the offsets that used to bound this are gone from the header,
      # because source locations are all the debug data holds.
      - id: sources_data
        type: sources_location_data
        size: '_root.header.version >= 98 ? _parent.len_debug_data : ((_root.header.version < 91 or _root.header.version == 93 or _root.header.version == 97) ? _parent.ofs_lexical_data : _parent.ofs_scope_desc_data)'
      - id: lexical_data
        type: scope_descriptor_data
        size: '((_root.header.version < 91 or _root.header.version == 97) ? _parent.len_debug_data : _parent.ofs_textified_callee) - _io.pos'
        if: _root.header.version < 91 or _root.header.version == 93 or _root.header.version == 97
      - id: scope_desc_data
        type: scope_descriptor_data
        size: _parent.ofs_textified_callee - _io.pos
        if: _root.header.version >= 91 and _root.header.version <= 96 and _root.header.version != 93
      - id: textified_data
        type: textified_callee_data
        size: _parent.ofs_string_table - _io.pos
        if: _root.header.version >= 91 and _root.header.version <= 96
      - id: string_table
        type: string_table_data
        size: _parent.len_debug_data - _io.pos
        if: _root.header.version >= 91 and _root.header.version <= 96
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
        if: _parent.header.version < 91 or _parent.header.version == 93 or _parent.header.version == 97
      - id: ofs_scope_desc_data
        -origId: scopeDescDataOffset
        type: u4
        if: _parent.header.version >= 91 and _parent.header.version <= 96 and _parent.header.version != 93
      # These two came in with the textified callee table in v91 and went away
      # again by 98, where the debug data holds nothing but source locations.
      - id: ofs_textified_callee
        -origId: textifiedCalleeOffset
        type: u4
        if: _parent.header.version >= 91 and _parent.header.version <= 96
      - id: ofs_string_table
        -origId: stringTableOffset
        type: u4
        if: _parent.header.version >= 91 and _parent.header.version <= 96
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
