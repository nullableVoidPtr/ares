// This is a generated file! Please edit source .ksy file and use kaitai-struct-compiler to rebuild

(function (root, factory) {
  if (typeof define === 'function' && define.amd) {
    define(['kaitai-struct/KaitaiStream'], factory);
  } else if (typeof module === 'object' && module.exports) {
    module.exports = factory(require('kaitai-struct/KaitaiStream'));
  } else {
    root.HermesBytecode = factory(root.KaitaiStream);
  }
}(this, function (KaitaiStream) {
var HermesBytecode = (function() {
  function HermesBytecode(_io, _parent, _root) {
    this._io = _io;
    this._parent = _parent;
    this._root = _root || this;

    this._read();
  }
  HermesBytecode.prototype._read = function() {
    this.magic = this._io.readBytes(8);
    if (!((KaitaiStream.byteArrayCompare(this.magic, [198, 31, 188, 3, 193, 3, 25, 31]) == 0))) {
      throw new KaitaiStream.ValidationNotEqualError([198, 31, 188, 3, 193, 3, 25, 31], this.magic, this._io, "/seq/0");
    }
    this.version = this._io.readU4le();
    if (!(this.version == 84)) {
      throw new KaitaiStream.ValidationNotEqualError(84, this.version, this._io, "/seq/1");
    }
    this.sourceHash = this._io.readBytes(20);
    this.fileLength = this._io.readU4le();
    this.globalCodeIndex = this._io.readU4le();
    this.functionCount = this._io.readU4le();
    this.stringKindCount = this._io.readU4le();
    this.identifierCount = this._io.readU4le();
    this.stringCount = this._io.readU4le();
    this.overflowStringCount = this._io.readU4le();
    this.stringStorageSize = this._io.readU4le();
    this.regexpCount = this._io.readU4le();
    this.regexpStorageSize = this._io.readU4le();
    this.arrayBufferSize = this._io.readU4le();
    this.objKeyBufferSize = this._io.readU4le();
    this.objValueBufferSize = this._io.readU4le();
    this.segmentId = this._io.readU4le();
    this.cjsModuleCount = this._io.readU4le();
    this.functionSourceCount = this._io.readU4le();
    this.debugInfoOffset = this._io.readU4le();
    this._raw_bytecodeOptions = this._io.readBytes(1);
    var _io__raw_bytecodeOptions = new KaitaiStream(this._raw_bytecodeOptions);
    this.bytecodeOptions = new BytecodeOptions(_io__raw_bytecodeOptions, this, this._root);
    this.padding = this._io.readBytes(27);
    this.functionHeaders = new Array(this.functionCount);
    for (var i = 0; i < this.functionCount; i++) {
      this.functionHeaders[i] = new SmallFuncHeader(this._io, this, this._root);
    }
    this._raw_stringKinds = new Array(this.stringKindCount);
    this.stringKinds = new Array(this.stringKindCount);
    for (var i = 0; i < this.stringKindCount; i++) {
      this._raw_stringKinds[i] = this._io.readBytes(4);
      var _io__raw_stringKinds = new KaitaiStream(this._raw_stringKinds[i]);
      this.stringKinds[i] = new StringKindEntry(_io__raw_stringKinds, this, this._root);
    }
    this.identifierHashes = new Array(this.identifierCount);
    for (var i = 0; i < this.identifierCount; i++) {
      this.identifierHashes[i] = this._io.readU4le();
    }
    this.smallStringTable = new Array(this.stringCount);
    for (var i = 0; i < this.stringCount; i++) {
      this.smallStringTable[i] = new SmallStringTableEntry(this._io, this, this._root);
    }
    this.overflowStringTable = new Array(this.overflowStringCount);
    for (var i = 0; i < this.overflowStringCount; i++) {
      this.overflowStringTable[i] = new OverflowStringTableEntry(this._io, this, this._root);
    }
    this._raw_stringStorage = this._io.readBytes(this.stringStorageSize);
    var _io__raw_stringStorage = new KaitaiStream(this._raw_stringStorage);
    this.stringStorage = new StringStorage(_io__raw_stringStorage, this, this._root);
    this._raw_arrayBuffer = this._io.readBytes(this.arrayBufferSize);
    var _io__raw_arrayBuffer = new KaitaiStream(this._raw_arrayBuffer);
    this.arrayBuffer = new ArrayBuffer(_io__raw_arrayBuffer, this, this._root);
    this._raw_objectKeyBuffer = this._io.readBytes(this.objKeyBufferSize);
    var _io__raw_objectKeyBuffer = new KaitaiStream(this._raw_objectKeyBuffer);
    this.objectKeyBuffer = new ObjectKeyBuffer(_io__raw_objectKeyBuffer, this, this._root);
    this._raw_objectValueBuffer = this._io.readBytes(this.objValueBufferSize);
    var _io__raw_objectValueBuffer = new KaitaiStream(this._raw_objectValueBuffer);
    this.objectValueBuffer = new ObjectValueBuffer(_io__raw_objectValueBuffer, this, this._root);
    this.regexpTable = new Array(this.regexpCount);
    for (var i = 0; i < this.regexpCount; i++) {
      this.regexpTable[i] = new RegexpTableEntry(this._io, this, this._root);
    }
    this._raw_regexpStorage = this._io.readBytes(this.regexpStorageSize);
    var _io__raw_regexpStorage = new KaitaiStream(this._raw_regexpStorage);
    this.regexpStorage = new RegexpStorage(_io__raw_regexpStorage, this, this._root);
    this.cjsModuleTable = new Array(this.cjsModuleCount);
    for (var i = 0; i < this.cjsModuleCount; i++) {
      switch (this.bytecodeOptions.cjsModulesStaticallyResolved) {
      case false:
        this.cjsModuleTable[i] = new CjsModuleTableEntry(this._io, this, this._root);
        break;
      case true:
        this.cjsModuleTable[i] = new CjsModuleTableStaticEntry(this._io, this, this._root);
        break;
      }
    }
    this.functionSourceTable = new Array(this.functionSourceCount);
    for (var i = 0; i < this.functionSourceCount; i++) {
      this.functionSourceTable[i] = new FunctionSourceTableEntry(this._io, this, this._root);
    }
  }

  var RegexpTableEntry = HermesBytecode.RegexpTableEntry = (function() {
    function RegexpTableEntry(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    RegexpTableEntry.prototype._read = function() {
      this.offset = this._io.readU4le();
      this.length = this._io.readU4le();
    }
    Object.defineProperty(RegexpTableEntry.prototype, 'bytecode', {
      get: function() {
        if (this._m_bytecode !== undefined)
          return this._m_bytecode;
        var io = this._root.regexpStorage._io;
        var _pos = io.pos;
        io.seek(this.offset);
        this._m_bytecode = io.readBytes(this.length);
        io.seek(_pos);
        return this._m_bytecode;
      }
    });

    return RegexpTableEntry;
  })();

  var RegexpStorage = HermesBytecode.RegexpStorage = (function() {
    function RegexpStorage(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    RegexpStorage.prototype._read = function() {
      this.data = [];
      var i = 0;
      while (!this._io.isEof()) {
        this.data.push(this._io.readU1());
        i++;
      }
    }

    return RegexpStorage;
  })();

  var SmallFuncHeader = HermesBytecode.SmallFuncHeader = (function() {
    function SmallFuncHeader(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    SmallFuncHeader.prototype._read = function() {
      this.offset = this._io.readBitsIntLe(25);
      this.paramCount = this._io.readBitsIntLe(7);
      this.bytecodeSizeInBytes = this._io.readBitsIntLe(15);
      this.functionName = this._io.readBitsIntLe(17);
      this.infoOffset = this._io.readBitsIntLe(25);
      this.frameSize = this._io.readBitsIntLe(7);
      this._io.alignToByte();
      this.environmentSize = this._io.readU1();
      this.highestReadCacheIndex = this._io.readU1();
      this.highestWriteCacheIndex = this._io.readU1();
      this._raw_flags = this._io.readBytes(1);
      var _io__raw_flags = new KaitaiStream(this._raw_flags);
      this.flags = new FunctionHeaderFlag(_io__raw_flags, this, this._root);
    }
    Object.defineProperty(SmallFuncHeader.prototype, 'bytecode', {
      get: function() {
        if (this._m_bytecode !== undefined)
          return this._m_bytecode;
        if (this.flags.overflowed == false) {
          var io = this._root._io;
          var _pos = io.pos;
          io.seek(this.offset);
          this._m_bytecode = new Array(this.bytecodeSizeInBytes);
          for (var i = 0; i < this.bytecodeSizeInBytes; i++) {
            this._m_bytecode[i] = io.readU1();
          }
          io.seek(_pos);
        }
        return this._m_bytecode;
      }
    });

    return SmallFuncHeader;
  })();

  var CjsModuleTableEntry = HermesBytecode.CjsModuleTableEntry = (function() {
    function CjsModuleTableEntry(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    CjsModuleTableEntry.prototype._read = function() {
      this.filenameId = this._io.readU4le();
      this.functionIndex = this._io.readU4le();
    }

    return CjsModuleTableEntry;
  })();

  var ArrayBuffer = HermesBytecode.ArrayBuffer = (function() {
    function ArrayBuffer(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    ArrayBuffer.prototype._read = function() {
      this.data = [];
      var i = 0;
      while (!this._io.isEof()) {
        this.data.push(this._io.readU1());
        i++;
      }
    }

    return ArrayBuffer;
  })();

  var ObjectValueBuffer = HermesBytecode.ObjectValueBuffer = (function() {
    function ObjectValueBuffer(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    ObjectValueBuffer.prototype._read = function() {
      this.data = [];
      var i = 0;
      while (!this._io.isEof()) {
        this.data.push(this._io.readU1());
        i++;
      }
    }

    return ObjectValueBuffer;
  })();

  var ObjectKeyBuffer = HermesBytecode.ObjectKeyBuffer = (function() {
    function ObjectKeyBuffer(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    ObjectKeyBuffer.prototype._read = function() {
      this.data = [];
      var i = 0;
      while (!this._io.isEof()) {
        this.data.push(this._io.readU1());
        i++;
      }
    }

    return ObjectKeyBuffer;
  })();

  var FunctionSourceTableEntry = HermesBytecode.FunctionSourceTableEntry = (function() {
    function FunctionSourceTableEntry(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    FunctionSourceTableEntry.prototype._read = function() {
      this.functionIndex = this._io.readU4le();
      this.stringTableOffset = this._io.readU4le();
    }

    return FunctionSourceTableEntry;
  })();

  var CjsModuleTableStaticEntry = HermesBytecode.CjsModuleTableStaticEntry = (function() {
    function CjsModuleTableStaticEntry(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    CjsModuleTableStaticEntry.prototype._read = function() {
      this.moduleId = this._io.readU4le();
      this.functionIndex = this._io.readU4le();
    }

    return CjsModuleTableStaticEntry;
  })();

  var BytecodeOptions = HermesBytecode.BytecodeOptions = (function() {
    function BytecodeOptions(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    BytecodeOptions.prototype._read = function() {
      this.staticBuiltins = this._io.readBitsIntLe(1) != 0;
      this.cjsModulesStaticallyResolved = this._io.readBitsIntLe(1) != 0;
      this.hasAsync = this._io.readBitsIntLe(1) != 0;
    }

    return BytecodeOptions;
  })();

  var Utf8Str = HermesBytecode.Utf8Str = (function() {
    function Utf8Str(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    Utf8Str.prototype._read = function() {
      this.value = KaitaiStream.bytesToStr(this._io.readBytesFull(), "UTF-8");
    }

    return Utf8Str;
  })();

  var FunctionHeaderFlag = HermesBytecode.FunctionHeaderFlag = (function() {
    FunctionHeaderFlag.ProhibitInvoke = Object.freeze({
      PROHIBIT_CALL: 0,
      PROHIBIT_CONSTRUCT: 1,
      PROHIBIT_NONE: 2,

      0: "PROHIBIT_CALL",
      1: "PROHIBIT_CONSTRUCT",
      2: "PROHIBIT_NONE",
    });

    function FunctionHeaderFlag(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    FunctionHeaderFlag.prototype._read = function() {
      this.prohibitInvoke = this._io.readBitsIntLe(2);
      this.strictMode = this._io.readBitsIntLe(1) != 0;
      this.hasExceptionHandler = this._io.readBitsIntLe(1) != 0;
      this.hasDebugInfo = this._io.readBitsIntLe(1) != 0;
      this.overflowed = this._io.readBitsIntLe(1) != 0;
    }

    return FunctionHeaderFlag;
  })();

  var DebugFileRegion = HermesBytecode.DebugFileRegion = (function() {
    function DebugFileRegion(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    DebugFileRegion.prototype._read = function() {
      this.fromAddress = this._io.readU4le();
      this.filenameId = this._io.readU4le();
      this.sourceMappingUrlId = this._io.readU4le();
    }

    return DebugFileRegion;
  })();

  var SmallStringTableEntry = HermesBytecode.SmallStringTableEntry = (function() {
    function SmallStringTableEntry(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    SmallStringTableEntry.prototype._read = function() {
      this.isUtf16 = this._io.readBitsIntLe(1) != 0;
      this.offset = this._io.readBitsIntLe(23);
      this._io.alignToByte();
      this.length = this._io.readU1();
    }
    Object.defineProperty(SmallStringTableEntry.prototype, 'string', {
      get: function() {
        if (this._m_string !== undefined)
          return this._m_string;
        var io = this._root.stringStorage._io;
        var _pos = io.pos;
        io.seek(this.offset);
        switch (this.isUtf16) {
        case true:
          this._raw__m_string = io.readBytes(this.length);
          var _io__raw__m_string = new KaitaiStream(this._raw__m_string);
          this._m_string = new Utf16Str(_io__raw__m_string, this, this._root);
          break;
        case false:
          this._raw__m_string = io.readBytes(this.length);
          var _io__raw__m_string = new KaitaiStream(this._raw__m_string);
          this._m_string = new Utf8Str(_io__raw__m_string, this, this._root);
          break;
        default:
          this._m_string = io.readBytes(this.length);
          break;
        }
        io.seek(_pos);
        return this._m_string;
      }
    });

    return SmallStringTableEntry;
  })();

  var BytecodeFooter = HermesBytecode.BytecodeFooter = (function() {
    function BytecodeFooter(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    BytecodeFooter.prototype._read = function() {
      this.fileHash = this._io.readBytes(20);
    }

    return BytecodeFooter;
  })();

  var StringKindEntry = HermesBytecode.StringKindEntry = (function() {
    StringKindEntry.Kind = Object.freeze({
      STRING: 0,
      IDENTIFIER: 1,

      0: "STRING",
      1: "IDENTIFIER",
    });

    function StringKindEntry(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    StringKindEntry.prototype._read = function() {
      this.count = this._io.readBitsIntLe(31);
      this.kind = this._io.readBitsIntLe(1);
    }

    return StringKindEntry;
  })();

  var Utf16Str = HermesBytecode.Utf16Str = (function() {
    function Utf16Str(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    Utf16Str.prototype._read = function() {
      this.value = KaitaiStream.bytesToStr(this._io.readBytesFull(), "UTF-16");
    }

    return Utf16Str;
  })();

  var StringStorage = HermesBytecode.StringStorage = (function() {
    function StringStorage(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    StringStorage.prototype._read = function() {
      this.data = [];
      var i = 0;
      while (!this._io.isEof()) {
        this.data.push(this._io.readU1());
        i++;
      }
    }

    return StringStorage;
  })();

  var OverflowStringTableEntry = HermesBytecode.OverflowStringTableEntry = (function() {
    function OverflowStringTableEntry(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    OverflowStringTableEntry.prototype._read = function() {
      this.offset = this._io.readU4le();
      this.length = this._io.readU4le();
    }

    return OverflowStringTableEntry;
  })();

  var DebugInfo = HermesBytecode.DebugInfo = (function() {
    function DebugInfo(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    DebugInfo.prototype._read = function() {
      this.filenameCount = this._io.readU4le();
      this.filenameStorageSize = this._io.readU4le();
      this.fileRegionCount = this._io.readU4le();
      this.lexicalDataOffset = this._io.readU4le();
      this.debugDataSize = this._io.readU4le();
      this.filenameTable = new Array(this.filenameCount);
      for (var i = 0; i < this.filenameCount; i++) {
        this.filenameTable[i] = new StringTableEntry(this._io, this, this._root);
      }
      this._raw_filenameStorage = this._io.readBytes(this.filenameStorageSize);
      var _io__raw_filenameStorage = new KaitaiStream(this._raw_filenameStorage);
      this.filenameStorage = new StringStorage(_io__raw_filenameStorage, this, this._root);
      this.fileRegions = new Array(this.fileRegionCount);
      for (var i = 0; i < this.fileRegionCount; i++) {
        this.fileRegions[i] = new DebugFileRegion(this._io, this, this._root);
      }
      this.debugData = new Array(this.debugDataSize);
      for (var i = 0; i < this.debugDataSize; i++) {
        this.debugData[i] = this._io.readU1();
      }
    }

    return DebugInfo;
  })();

  var StringTableEntry = HermesBytecode.StringTableEntry = (function() {
    function StringTableEntry(_io, _parent, _root) {
      this._io = _io;
      this._parent = _parent;
      this._root = _root || this;

      this._read();
    }
    StringTableEntry.prototype._read = function() {
      this.offset = this._io.readU4le();
      this.length = this._io.readBitsIntLe(31);
      this.isUtf16 = this._io.readBitsIntLe(1) != 0;
    }
    Object.defineProperty(StringTableEntry.prototype, 'filename', {
      get: function() {
        if (this._m_filename !== undefined)
          return this._m_filename;
        var io = this._root.debugInfo.filenameStorage._io;
        var _pos = io.pos;
        io.seek(this.offset);
        switch (this.isUtf16) {
        case true:
          this._raw__m_filename = io.readBytes(this.length);
          var _io__raw__m_filename = new KaitaiStream(this._raw__m_filename);
          this._m_filename = new Utf16Str(_io__raw__m_filename, this, this._root);
          break;
        case false:
          this._raw__m_filename = io.readBytes(this.length);
          var _io__raw__m_filename = new KaitaiStream(this._raw__m_filename);
          this._m_filename = new Utf8Str(_io__raw__m_filename, this, this._root);
          break;
        default:
          this._m_filename = io.readBytes(this.length);
          break;
        }
        io.seek(_pos);
        return this._m_filename;
      }
    });

    return StringTableEntry;
  })();
  Object.defineProperty(HermesBytecode.prototype, 'debugInfo', {
    get: function() {
      if (this._m_debugInfo !== undefined)
        return this._m_debugInfo;
      if (this.debugInfoOffset != 0) {
        var _pos = this._io.pos;
        this._io.seek(this.debugInfoOffset);
        this._m_debugInfo = new DebugInfo(this._io, this, this._root);
        this._io.seek(_pos);
      }
      return this._m_debugInfo;
    }
  });
  Object.defineProperty(HermesBytecode.prototype, 'footer', {
    get: function() {
      if (this._m_footer !== undefined)
        return this._m_footer;
      var _pos = this._io.pos;
      this._io.seek((this._io.size - 20));
      this._m_footer = new BytecodeFooter(this._io, this, this._root);
      this._io.seek(_pos);
      return this._m_footer;
    }
  });

  return HermesBytecode;
})();
return HermesBytecode;
}));
