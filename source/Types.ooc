
import io/Writer
import structs/ArrayList
import structs/HashMap

import Opcodes


LuaAny: abstract class {
}

LuaBoolean: class extends LuaAny {
    v: Bool

    init: func(=v) {}
}

LuaNil: class extends LuaAny {
    init: func {}
}

LuaNumber: class extends LuaAny {
    v: Double

    init: func(=v) {}

    init: func~int(i: Int) {
        v = i
    }
}

LuaString: class extends LuaAny {
    v: String

    init: func(=v) {}
}

LuaTable: class extends LuaAny {
    v: HashMap<LuaAny, LuaAny>

    init: func() {
        v = HashMap<LuaAny, LuaAny> new()
    }
}

/*
** Description of an upvalue for function prototypes
*/
UpvalDesc: class {
    name: String  /* upvalue name (for debug information) */
    instack: Bool  /* whether it is in stack */
    idx: UInt8  /* index of upvalue (in stack or in outer function's list) */

    init: func(=name, =instack, =idx) {}
}


/*
** Description of a local variable for function prototypes
** (used for debug information)
*/
LocVar: class {
    varname: String
    startpc: Int  /* first point where variable is active */
    endpc: Int    /* first point where variable is dead */

    init: func(=varname) {}
}


LuaProto: class extends LuaAny {
    k: ArrayList<LuaAny>  /* constants used by the function */
    code: ArrayList<Instruction> //~ Instruction *code;
    p: ArrayList<LuaProto>  /* functions defined inside the function */
    lineinfo: ArrayList<Int>  /* map from opcodes to source lines */
    locvars: ArrayList<LocVar>  /* information about local variables */
    upvalues: ArrayList<UpvalDesc>  /* upvalue information */
    source: String
    linedefined: Int
    lastlinedefined: Int
    numparams: UInt8;  /* number of fixed parameters */
    is_vararg: Bool
    maxstacksize: UInt8  /* maximum stack used by this function */

    init: func {
        k = ArrayList<LuaAny> new()
        code = ArrayList<Instruction> new()
        p = ArrayList<LuaProto> new()
        lineinfo = ArrayList<Int> new()
        locvars = ArrayList<LocVar> new()
        upvalues = ArrayList<UpvalDesc> new()
    }

    _header: func -> ArrayList<Char> {
        i := 1 as Int
        h := ArrayList<Char> new(18)
        h add(0x1b as Char)
        h add('L')
        h add('u')
        h add('a')
        h add(0x52 as Char)     /* Lua 5.2 */
        h add(0 as Char)        /* the official format */
        h add((i& as Char*)@ as Char)   /* endianness */
        h add(Int size as Char)
        h add(SizeT size as Char)
        h add(Instruction size as Char)
        h add(Double size as Char)
        h add(0 as Char)        /* is lua_Number integral? */
        h add(0x19 as Char)
        h add(0x93 as Char)
        h add('\r')
        h add('\n')
        h add(0x1a as Char)
        h add('\n')
        return h
    }

    dumpHeader: func(w: Writer) {
        h := _header()
        w write(h data as Char*, h getSize())
    }

    dump: func(w: Writer, strip: Bool) {
        w write(linedefined& as Char*, Int size)
        w write(lastlinedefined& as Char*, Int size)
        w write(numparams as Char)
        w write(is_vararg as Char)
        w write(maxstacksize as Char)
        n := code getSize()
        w write(n& as Char*, Int size)
        w write(code data as Char*, n * Instruction size)
        n = k getSize()
        w write(n& as Char*, Int size)
        for (i in 0 .. n) {
            cst := k get(i)
            match (cst class) {
                case LuaNil =>
                    w write(0 as Char)
                case LuaBoolean =>
                    w write(1 as Char)
                    w write(cst as LuaBoolean v as Char)
                case LuaNumber =>
                    w write(3 as Char)
                    num := cst as LuaNumber v
                    w write(num& as Char*, Double size)
                case LuaString =>
                    w write(4 as Char)
                    str := cst as LuaString v
                    _dumpString(w, str)
            }
        }
        n = p getSize()
        w write(n& as Char*, Int size)
        for (i in 0 .. n)
            p get(i) dump(w, strip)
        n = upvalues getSize()
        w write(n& as Char*, Int size)
        for (i in 0 .. n) {
            upv := upvalues get(i)
            w write(upv instack as Char)
            w write(upv idx as Char)
        }
        if (strip) {
            n = 0
            w write(n& as Char*, Int size) // source
            w write(n& as Char*, Int size) // lineinfo
            w write(n& as Char*, Int size) // locvars
            w write(n& as Char*, Int size) // upvalues
        }
        else {
            _dumpString(w, source)
            n = lineinfo getSize()
            w write(n& as Char*, Int size)
            w write(lineinfo data as Char*, n * Int size)
            n = locvars getSize()
            w write(n& as Char*, Int size)
            for (i in 0 .. n) {
                var := locvars get(i)
                _dumpString(w, var varname)
                pc := var startpc
                w write(pc& as Char*, Int size)
                pc = var endpc
                w write(pc& as Char*, Int size)
            }
            n = upvalues getSize()
            w write(n& as Char*, Int size)
            for (i in 0 .. n)
                _dumpString(w, upvalues get(i) name)
        }
    }

    _dumpString: func(w: Writer, str: String) {
        len := str length()
        if (len == 0)
            w write(len& as Char*, Int size)
        else {
            len1 := len + 1
            w write(len1& as Char*, Int size)
            w write(str, len)
            w write(0 as Char)
        }
    }
}

