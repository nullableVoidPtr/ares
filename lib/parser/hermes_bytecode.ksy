meta:
  id: hermes_bytecode
  title: Hermes bytecode file
  file-extension: hbc
  endian: le
  bit-endian: le
seq:
  - id: magic
    contents: [0xc6, 0x1f, 0xbc, 0x03, 0xc1, 0x03, 0x19, 0x1f]
  - id: version
    type: u4
    valid: 84
  - id: source_hash
    size: 20
  - id: file_length
    type: u4
  - id: global_code_index
    type: u4
  - id: function_count
    type: u4
  - id: string_kind_count
    type: u4
  - id: identifier_count
    type: u4
  - id: string_count
    type: u4
  - id: overflow_string_count
    type: u4
  - id: string_storage_size
    type: u4
  - id: regexp_count
    type: u4
  - id: regexp_storage_size
    type: u4
  - id: array_buffer_size
    type: u4
  - id: obj_key_buffer_size
    type: u4
  - id: obj_value_buffer_size
    type: u4
  - id: segment_id
    type: u4
  - id: cjs_module_count
    type: u4
  - id: function_source_count
    type: u4
  - id: debug_info_offset
    type: u4
  - id: bytecode_options
    type: bytecode_options
    size: 1
  - id: padding
    size: 27
  - id: function_headers
    type: small_func_header
    repeat: expr
    repeat-expr: function_count
  - id: string_kinds
    type: string_kind_entry
    size: 4
    repeat: expr
    repeat-expr: string_kind_count
  - id: identifier_hashes
    type: u4
    repeat: expr
    repeat-expr: identifier_count
  - id: small_string_table
    type: small_string_table_entry
    repeat: expr
    repeat-expr: string_count
  - id: overflow_string_table
    type: overflow_string_table_entry
    repeat: expr
    repeat-expr: overflow_string_count
  - id: string_storage
    type: string_storage
    size: string_storage_size
  - id: array_buffer
    type: array_buffer
    size: array_buffer_size
  - id: object_key_buffer
    type: object_key_buffer
    size: obj_key_buffer_size
  - id: object_value_buffer
    type: object_value_buffer
    size: obj_value_buffer_size
  - id: regexp_table
    type: regexp_table_entry
    repeat: expr
    repeat-expr: regexp_count
  - id: regexp_storage
    type: regexp_storage
    size: regexp_storage_size
  - id: cjs_module_table
    type:
      switch-on: bytecode_options.cjs_modules_statically_resolved
      cases:
        false: cjs_module_table_entry
        true: cjs_module_table_static_entry
    repeat: expr
    repeat-expr: cjs_module_count
  - id: function_source_table
    type: function_source_table_entry
    repeat: expr
    repeat-expr: function_source_count
instances:
  debug_info:
    if: debug_info_offset != 0
    type: debug_info
    pos: debug_info_offset
  footer:
    type: bytecode_footer
    pos: _io.size - 20
types:
  bytecode_options:
    seq:
      - id: static_builtins
        type: b1
      - id: cjs_modules_statically_resolved
        type: b1
      - id: has_async
        type: b1
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
  small_func_header:
    seq:
      - id: offset
        type: b25
      - id: param_count
        type: b7
      - id: bytecode_size_in_bytes
        type: b15
      - id: function_name
        type: b17
      - id: info_offset
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
    instances:
      bytecode:
        io: _root._io
        pos: offset
        type: u1
        repeat: expr
        repeat-expr: bytecode_size_in_bytes
        if: flags.overflowed == false
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
  utf8_str:
    seq:
      - id: value
        type: str
        encoding: UTF-8
        size-eos: true
  utf16_str:
    seq:
      - id: value
        type: str
        encoding: UTF-16
        size-eos: true
  small_string_table_entry:
    seq:
      - id: is_utf16
        type: b1
      - id: offset
        type: b23
      - id: length
        type: u1
    instances:
      string:
        io: _root.string_storage._io
        pos: offset
        size: length
        type: 
          switch-on: is_utf16
          cases:
            true: utf16_str
            false: utf8_str
  overflow_string_table_entry:
    seq:
      - id: offset
        type: u4
      - id: length
        type: u4
  string_storage:
    seq:
      - id: data
        type: u1
        repeat: eos
  array_buffer:
    seq:
      - id: data
        type: u1
        repeat: eos
  object_key_buffer:
    seq:
      - id: data
        type: u1
        repeat: eos
  object_value_buffer:
    seq:
      - id: data
        type: u1
        repeat: eos
  regexp_table_entry:
    seq:
      - id: offset
        type: u4
      - id: length
        type: u4
    instances:
      bytecode:
        io: _root.regexp_storage._io
        pos: offset
        size: length 
  regexp_storage:
    seq:
      - id: data
        type: u1
        repeat: eos
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
      - id: string_table_offset
        type: u4
  string_table_entry:
    seq:
      - id: offset
        type: u4
      - id: length
        type: b31
      - id: is_utf16
        type: b1
    instances:
      filename:
        io: _root.debug_info.filename_storage._io
        pos: offset
        size: length
        type: 
          switch-on: is_utf16
          cases:
            true: utf16_str
            false: utf8_str
  debug_file_region:
    seq:
      - id: from_address
        type: u4
      - id: filename_id
        type: u4
      - id: source_mapping_url_id
        type: u4
  debug_info:
    seq:
      - id: filename_count
        type: u4
      - id: filename_storage_size
        type: u4
      - id: file_region_count
        type: u4
      - id: lexical_data_offset
        type: u4
      - id: debug_data_size
        type: u4
      - id: filename_table
        type: string_table_entry
        repeat: expr
        repeat-expr: filename_count
      - id: filename_storage
        type: string_storage
        size: filename_storage_size
      - id: file_regions
        type: debug_file_region
        repeat: expr
        repeat-expr: file_region_count
      - id: debug_data
        type: u1
        repeat: expr
        repeat-expr: debug_data_size
  bytecode_footer:
    seq:
      - id: file_hash
        size: 20

