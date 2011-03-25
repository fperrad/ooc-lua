
import io/Writer
import math
import structs/ArrayList

import Opcodes


LuaAny: abstract class {
    toBool: func -> Bool {
        return false
    }

    toInt: func -> Int {
        return 0
    }

    toNum: func -> Double {
        return 0.0
    }

    toPtr: func -> Pointer {
        return null
    }

    toStr: func -> String {
        return null
    }

    hashval: abstract func -> SizeT

    type: abstract func -> String

    get: func(key: LuaAny) -> LuaAny {
        _typeError("index")
        return null
    }

    set: func(key, val: LuaAny) {
        _typeError("index")
    }

    getMetatable: func -> LuaTable {
        return null
    }

    setMetatable: func(mt: LuaTable) {
    }

    add: func(op: LuaAny) -> LuaAny {
        return _arithError(op)
    }

    sub: func(op: LuaAny) -> LuaAny {
        return _arithError(op)
    }

    mul: func(op: LuaAny) -> LuaAny {
        return _arithError(op)
    }

    div: func(op: LuaAny) -> LuaAny {
        return _arithError(op)
    }

    mod: func(op: LuaAny) -> LuaAny {
        return _arithError(op)
    }

    pow: func(op: LuaAny) -> LuaAny {
        return _arithError(op)
    }

    unm: func -> LuaAny {
        return _arithError(this)
    }

    len: func -> LuaAny {
        _typeError("get length of")
        return null
    }

    concat: func(op: ArrayList<LuaAny>) -> LuaAny {
        return _concatError()
    }

    eq: func(op: LuaAny) -> Bool {
        return false
    }

    lt: func(op: LuaAny) -> Bool {
        return _orderError(op)
    }

    le: func(op: LuaAny) -> Bool {
        return _orderError(op)
    }

    _arithError: func(op: LuaAny) -> LuaAny {
        _typeError("perform arithmetic on")
        return null
    }

    _concatError: func -> LuaAny {
        _typeError("concatenate")
        return null
    }

    _orderError: func(op: LuaAny) -> Bool {
        t1 := type()
        t2 := op type()
        if (t1 equals?(t2))
            _msgError("attempt to compare two %s values" format(t1))
        else
            _msgError("attempt to compare %s with %s" format(t1, t2))
        return false
    }

    _typeError: func(msg: String) {
        _msgError("attempt to %s %s " format(msg, type()))
    }

    _msgError: func(msg: String) {
        Exception new(This, msg) throw()
    }
}

LuaBoolean: class extends LuaAny {
    v: Bool

    init: func(=v) {}

    toBool: func -> Bool {
        return v
    }

    hashval: func -> SizeT {
        return v as SizeT
    }

    type: func -> String {
        return "boolean"
    }

    eq: func(op: LuaAny) -> Bool {
        if (op class != class)
            return false
        return v == op as LuaBoolean v
    }
}

LuaNil: class extends LuaAny {
    init: func {}

    hashval: func -> SizeT {
        return 0
    }

    type: func -> String {
        return "nil"
    }

    eq: func(op: LuaAny) -> Bool {
        if (op class != class)
            return false
        return true
    }
}

LuaNumber: class extends LuaAny {
    v: Double

    init: func(=v) {}

    init: func~int(i: Int) {
        v = i
    }

    toInt: func -> Int {
        return v as Int
    }

    toNum: func -> Double {
        return v
    }

    toStr: func -> String {
        buff := CString new(20)
        n := sprintf(buff, "%.14g", v)
        return String new(buff, n)
    }

    hashval: func -> SizeT {
        return v as SizeT
    }

    type: func -> String {
        return "number"
    }

    add: func(op: LuaAny) -> LuaAny {
        if (op class != class)
            return _arithError(op)
        return LuaNumber new(v + op as LuaNumber v)
    }

    sub: func(op: LuaAny) -> LuaAny {
        if (op class != class)
            return _arithError(op)
        return LuaNumber new(v - op as LuaNumber v)
    }

    mul: func(op: LuaAny) -> LuaAny {
        if (op class != class)
            return _arithError(op)
        return LuaNumber new(v * op as LuaNumber v)
    }

    div: func(op: LuaAny) -> LuaAny {
        if (op class != class)
            return _arithError(op)
        return LuaNumber new(v / op as LuaNumber v)
    }

    mod: func(op: LuaAny) -> LuaAny {
        if (op class != class)
            return _arithError(op)
        v2 := op as LuaNumber v
        return LuaNumber new(v - (v / v2) floor() * v2)
    }

    pow: func(op: LuaAny) -> LuaAny {
        if (op class != class)
            return _arithError(op)
        return LuaNumber new(v pow(op as LuaNumber v))
    }

    unm: func -> LuaAny {
        return LuaNumber new(- v)
    }

    eq: func(op: LuaAny) -> Bool {
        if (op class != class)
            return false
        return v == op as LuaNumber v
    }

    lt: func(op: LuaAny) -> Bool {
        if (op class != class)
            return _orderError(op)
        return v < op as LuaNumber v
    }

    le: func(op: LuaAny) -> Bool {
        if (op class != class)
            return _orderError(op)
        return v <= op as LuaNumber v
    }
}

LuaString: class extends LuaAny {
    v: String

    init: func(=v) {}

    toStr: func -> String {
        return v
    }

    hashval: func -> SizeT {
        return v as SizeT // internalized string
    }

    type: func -> String {
        return "string"
    }


    len: func -> LuaAny {
        return LuaNumber new(v length())
    }

    concat: func(op: ArrayList<LuaAny>) -> LuaAny {
        str := v
        for (e in op)
            match (e class) {
                case LuaString =>
                    str += e as LuaString v
                case LuaNumber =>
                    str += e toStr()
                case =>
                    return e _concatError()
            }
        return LuaString new(str)
    }

    eq: func(op: LuaAny) -> Bool {
        if (op class != class)
            return false
        return v equals?(op as LuaString v)
    }

    lt: func(op: LuaAny) -> Bool {
        if (op class != class)
            return _orderError(op)
        return strcmp(v, op as LuaString v) < 0
    }

    le: func(op: LuaAny) -> Bool {
        if (op class != class)
            return _orderError(op)
        return strcmp(v, op as LuaString v) <= 0
    }
}

MINPOWER2 := const 4    /* minimum size for "growing" vectors */

Node: cover {
    key: LuaAny
    val: LuaAny
    next: Node*
}

Table: class {
    node: Node*
    firstfree: Node*  /* this position is free; all positions after it are full */
    size: Int

    init: func(narray, nrec: Int) {
        setnodevector(narray + nrec)
    }

    /*
    ** returns the `main' position of an element in a table (that is, the index
    ** of its hash value)
    */
    mainposition: func(key: LuaAny) -> Node* {
        h := key hashval()
        version(debug) {
            assert((h % size) == (h & (size - 1)))
        }
        return node + (h & (size - 1))
    }

    get: func(key: LuaAny) -> LuaAny {
        n := mainposition(key)
        while (n) {
            p := n@ key
            if (p != null && key eq(p))
                return n@ val
            n = n@ next
        }
        return null  /* key not found */
    }

    next: func(key: LuaAny) -> LuaAny {
        return null
    }

    /*
    ** inserts a key into a hash table; first, check whether key is
    ** already present; if not, check whether key's main position is free;
    ** if not, check whether colliding node is in its main position or not;
    ** if it is not, move colliding node to an empty place and put new key
    ** in its main position; otherwise (colliding node is in its main position),
    ** new key goes to an empty position.
    */
    set: func(key, val: LuaAny) {
        mp := mainposition(key)

        /* check whether `key' is somewhere in the chain */
        n := mp
        while (n) {
            /* that's all */
            p := n@ key
            if (p != null && key eq(p)) {
                n@ val = val
                return
            }
            else
                n = n@ next
        }

        /* `key' not found; must insert it */
        /* main position is not free? */
        if (mp@ key) {
            othern := mainposition(mp@ key)        /* main position of colliding node */

            /* get a free place */
            n = firstfree

            /* is colliding node out of its main position? (can only happen if
               its position is after "firstfree") */
            if (mp as Pointer > n as Pointer && othern as Pointer != mp as Pointer) {
                /* yes; move colliding node into free position */
                while (othern@ next as Pointer != mp as Pointer)
                    othern = othern@ next  /* find previous */

                /* redo the chain with `n' in place of `mp' */
                othern@ next = n

                /* copy colliding node into free pos. (mp->next also goes) */
                n@ = mp@

                /* now `mp' is free */
                mp@ next = null
            }
            /* colliding node is in its own main position */
            else {
                /* new node will go into free position */
                /* chain new position */
                n@ next  = mp@ next
                mp@ next = n
                mp       = n
            }
        }

        mp@ key = key

        /* correct `firstfree' */
        while (true) {
            /* OK; table still has a free place */
            if (! firstfree@ key) {
                mp@ val = val
                return
            }
            else if (firstfree as Pointer == node as Pointer)
                break  /* cannot decrement from here */
            else
                firstfree -= 1
        }

        /* no more free places */
        rehash()

        /* `rehash' invalidates this insertion */
        set(key, val)
    }

    setnodevector: func(_size: Int) {
        if (_size < MINPOWER2)
            _size = MINPOWER2
        size = _size
        node = gc_malloc(size * Node size) as Node*
        /* first free position to be used */
        firstfree = node + (size - 1)
    }

    numuse: func -> Int {
        realuse := 0
        for (i in 0..size)
            if (node[i] val)
                realuse += 1
        return realuse
    }

    rehash: func {
        oldsize := size
        nold := node
        nelems := numuse()

        version(debug) {
            assert(nelems <= oldsize) // "wrong count"
        }

        /* using more than 3/4? */
        if (nelems >= oldsize - oldsize / 4)
            setnodevector(oldsize * 2)
        /* less than 1/4? */
        else if (nelems <= oldsize / 4 && oldsize > MINPOWER2)
            setnodevector(oldsize / 2)
        else
            setnodevector(oldsize)

        for (i in 0..oldsize) {
            old := nold + i
            if (old@ val)
                set(old@ key, old@ val)
        }

        /* free old array */
        gc_free(nold)
    }
}

LuaTable: class extends LuaAny {
    v: Table
    mt: LuaTable

    init: func(narray, nrec: Int) {
        v = Table new(narray, nrec)
    }

    toPtr: func -> Pointer {
        return null
    }

    toStr: func -> String {
        buff := CString new(20)
        n := sprintf(buff, "table: %08X", v)
        return String new(buff, n)
    }

    hashval: func -> SizeT {
        return v as SizeT
    }

    type: func -> String {
        return "table"
    }

    len: func -> LuaAny {
        return LuaNumber new(v numuse())
    }

    eq: func(op: LuaAny) -> Bool {
        if (op class != class)
            return false
        return v == op as LuaTable v
    }

    get: func(key: LuaAny) -> LuaAny {
        val := v get(key)
        if (val == null)
            val = LuaNil new()
        return val
    }

    set: func(key, val: LuaAny) {
        if (val instanceOf?(LuaNil))
            val = null
        v set(key, val)
    }

    rawEqual: func(op: LuaAny) -> Bool {
        if (op class != class)
            return false
        return v == op as LuaTable v
    }

    rawGet: func(key: LuaAny) -> LuaAny {
        val := v get(key)
        if (val == null)
            val = LuaNil new()
        return val
    }

    rawSet: func(key, val: LuaAny) {
        if (val instanceOf?(LuaNil))
            val = null
        v set(key, val)
    }

    getMetatable: func -> LuaTable {
        return mt
    }

    setMetatable: func(=mt) {}

    next: func(idx: LuaAny) -> LuaAny {
        return LuaNil new()
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

    hashval: func -> SizeT {
        return 0 //
    }

    type: func -> String {
        return "proto"
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
        len1 := len + 1
        w write(len1& as Char*, Int size)
        if (len != 0)
            w write(str, len)
        w write(0 as Char)
    }
}

