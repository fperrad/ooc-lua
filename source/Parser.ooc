
import io/FileReader
import math
import structs/ArrayList

import Lexer
import Types
import Opcodes

ExpKind: enum {
    VVOID,      /* no value */
    VNIL,
    VTRUE,
    VFALSE,
    VK,         /* info = index of constant in `k' */
    VKNUM,      /* nval = numerical value */
    VNONRELOC,  /* info = result register */
    VLOCAL,     /* info = local register */
    VUPVAL,     /* info = index of upvalue in 'upvalues' */
    VINDEXED,   /* t = table register/upvalue; idx = index R/K */
    VJMP,       /* info = instruction pc */
    VRELOCABLE, /* info = instruction pc */
    VCALL,      /* info = instruction pc */
    VVARARG     /* info = instruction pc */

    vkisvar: inline func -> Bool {
        return (ExpKind VLOCAL <= this) && (this <= ExpKind VINDEXED)
    }

    vkisinreg: inline func -> Bool {
        return (this == ExpKind VNONRELOC) || (this == ExpKind VLOCAL)
    }

    hasmultret: inline func -> Bool {
        return (this == ExpKind VCALL) || (this == ExpKind VVARARG)
    }
}

ExpDesc: cover {
    k: ExpKind
    ind_idx: Int16  /* index (R/K) */
    ind_t: UInt8  /* table (register or upvalue) */
    ind_vt: ExpKind  /* whether 't' is register (VLOCAL) or upvalue (VUPVAL) */
    info: Int  /* for generic use */
    nval: Double  /* for VKNUM     lua_Number */
    t: Int  /* patch list of `exit when true' */
    f: Int  /* patch list of `exit when false' */

    isnumeral: inline func -> Bool {
        return k == ExpKind VKNUM && t == NO_JUMP && f == NO_JUMP
    }

    hasjumps: inline func -> Bool {
        return t != f
    }
}

init_exp: inline func(e: ExpDesc@, k: ExpKind, info: Int) {
    e k = k
    e info = info
    e ind_idx = 0
    e ind_t = 0
    e ind_vt = ExpKind VVOID
    e f = NO_JUMP
    e t = NO_JUMP
}



/* state needed to generate code for a given function */
FuncState: final class {
    f: LuaProto  /* current function header */
    h: LuaTable  /* table to find (and reuse) elements in `k' */
    prev: FuncState  /* enclosing function */
    ls: Parser  /* lexical state */
    bl: BlockCnt*  /* chain of current blocks */
    lasttarget: Int  /* `pc' of last `jump target' */
    jpc: Int  /* list of pending jumps to `pc' */
    freereg: Int  /* first free register */
    firstlocal: Int  /* index of first local var of this function */
    nactvar: Short  /* number of active local variables */

    init: func(=ls, =prev) {
        f = LuaProto new()
        f source = ls source
        f maxstacksize = 2  /* registers 0/1 are always valid */
        h = LuaTable new()
        bl = null
        lasttarget = 0
        jpc = NO_JUMP
        freereg = 0
        firstlocal = ls actvar getSize()
        nactvar = 0
    }


    finalize: func -> FuncState {
        luaK_ret(0, 0)  /* final return */
        removevars(0)
        version(debug) {
            assert(! bl)
        }
        return prev
    }


    getlocvar: func(i: Int) -> LocVar* {
        idx := ls actvar get(firstlocal + i)
        version(debug) {
            assert(idx < f locvars getSize())
        }
        return f locvars data as LocVar* + idx
    }

    enterblock: func(_bl: BlockCnt@, _isbreakable: Bool) {
        _bl breaklist = NO_JUMP
        _bl isbreakable = _isbreakable
        _bl nactvar = nactvar
        _bl upval = false
        _bl previous = bl
        bl = _bl&
        version(debug) {
            assert(freereg == nactvar)
        }
    }

    leaveblock: func {
        _bl := bl
        bl = _bl@ previous
        removevars(_bl@ nactvar)
        if (_bl@ upval)
            luaK_codeABC(OpCode OP_CLOSE, _bl@ nactvar, 0, 0)
        version(debug) {
            /* a block either controls scope or breaks (never both) */
            assert(!_bl@ isbreakable || !_bl@ upval)
            assert(_bl@ nactvar == nactvar)
        }
        freereg = nactvar  /* free registers */
        luaK_patchtohere(_bl@ breaklist)
    }

    removevars: func(tolevel: Int) {
        pc := f code getSize()
        actvar := ls actvar
        while (nactvar > tolevel) {
            nactvar -= 1
            pvar := getlocvar(nactvar)
            pvar@ endpc = pc
            actvar removeAt(actvar lastIndex())
        }
    }


    searchupvalue: func(name: String) -> Int {
        up := f upvalues
        for (i in 0 .. up getSize())
            if (up get(i) name equals?(name))
                return i
        return -1  /* not found */
    }


    newupvalue: func(name: String, v: ExpDesc@) -> Int {
        up := f upvalues
        idx := up getSize()
        up add(UpvalDesc new(name, v k == ExpKind VLOCAL, v info))
        return idx
    }

    searchvar: func(n: String) -> Int {
        i := nactvar - 1
        while (i >= 0) {
            pvar := getlocvar(i)
            if (pvar@ varname equals?(n))
                return i
            i -= 1
        }
        return -1;  /* not found */
    }

/*
  Mark block where variable at given level was defined
  (to emit OP_CLOSE later).
*/
    markupval: func(level: Int) {
        _bl := bl
        while (_bl) {
            if (_bl@ nactvar > level)
                break
            _bl = _bl@ previous
        }
        if (_bl)
            _bl@ upval = true
    }


/*
  Find variable with given name 'n'. If it is an upvalue, add this
  upvalue into all intermediate functions.
*/
    singlevaraux: func(n: String, var: ExpDesc@, base: Int) -> ExpKind {
        v := searchvar(n)  /* look up locals at current level */
        if (v >= 0) {  /* found? */
            init_exp(var&, ExpKind VLOCAL, v)  /* variable is local */
            if (!base)
                markupval(v)  /* local will be used as an upval */
            return ExpKind VLOCAL
        }
        else {  /* not found as local at current level; try upvalues */
            idx := searchupvalue(n)  /* try existing upvalues */
            if (idx < 0) {  /* not found? */
                if (! prev || /* no more levels */
                      prev singlevaraux(n, var&, 0) == ExpKind VVOID) /* try upper levels */
                    return ExpKind VVOID;  /* not found; is a global */
                /* else was LOCAL or UPVAL */
                idx  = newupvalue(n, var&)  /* will be a new upvalue */
            }
            init_exp(var&, ExpKind VUPVAL, idx)
            return ExpKind VUPVAL
        }
    }


    luaK_nil: func(_from, n: Int) {
        pc := f code getSize()
        if (pc > lasttarget) {  /* no jumps to current position? */
            previous := f code data as Instruction* + pc - 1
            if (previous@ getOpcode() == OpCode OP_LOADNIL) {
                pfrom := previous@ getarg_A()
                pto := previous@ getarg_B()
                if (pfrom <= _from && _from <= pto + 1) {  /* can connect both? */
                    if (_from + n - 1 > pto)
                        previous@ = previous@ setarg_B(_from + n - 1)
                    return
                }
            }
        }
        luaK_codeABC(OpCode OP_LOADNIL, _from, _from + n - 1, 0)  /* else no optimization */
    }


    luaK_jump: func -> Int {
        save := jpc  /* save list of jumps to here */
        jpc = NO_JUMP
        j := luaK_codeABx(OpCode OP_JMP, 0, NO_JUMP + MAXARG_sBx)
        luaK_concat(j&, save)  /* keep them on hold */
        return j
    }


    luaK_ret: func(first, nret: Int) {
        luaK_codeABC(OpCode OP_RETURN, first, nret+1, 0)
    }


    _condjump: func(op: OpCode, A, B, C: Int) -> Int {
        luaK_codeABC(op, A, B, C)
        return luaK_jump()
    }


    _fixjump: func(pc, dest: Int) {
        jmp := f code data as Instruction* + pc
        offset := dest - (pc + 1)
        version(debug) {
            assert(dest != NO_JUMP)
        }
        if (offset abs() > MAXARG_sBx)
            ls syntaxError("control structure too long")
        jmp@ = jmp@ setarg_sBx(offset)
    }


/*
** returns current `pc' and marks it as a jump target (to avoid wrong
** optimizations with consecutive instructions not in the same basic block).
*/
    luaK_getlabel: func -> Int {
        lasttarget = f code getSize()
        return lasttarget
    }


    _getjump: func(pc: Int) -> Int {
        offset := f code get(pc) getarg_sBx()
        if (offset == NO_JUMP)  /* point to itself represents end of list */
            return NO_JUMP  /* end of list */
        else
            return pc + 1 + offset  /* turn offset into absolute position */
    }


    _getjumpcontrol: func(pc: Int) -> Instruction* {
        pi := f code data as Instruction* + pc
        if (pc >= 1 && (pi-1)@ getOpcode() testTMode())
            return pi - 1
        else
            return pi
    }


/*
** check whether list has any jump that do not produce a value
** (or produce an inverted value)
*/
    _need_value: func(list: Int) -> Bool {
        while (list != NO_JUMP) {
            i := _getjumpcontrol(list)@
            if (i getOpcode() != OpCode OP_TESTSET)
                return true
            list = _getjump(list)
        }
        return false  /* not found */
    }


    _patchtestreg: func(node, reg: Int) -> Int {
        i := _getjumpcontrol(node)
        if (i@ getOpcode() != OpCode OP_TESTSET)
            return 0;  /* cannot patch other instructions */
        if (reg != NO_REG && reg != i@ getarg_B())
            i@ = i@ setarg_A(reg)
        else  /* no register to put value or register already has the value */
            i@ = Instruction createABC(OpCode OP_TEST, i@ getarg_B(), 0, i@ getarg_C())

        return 1
    }


    _removevalues: func(list: Int) {
        while (list != NO_JUMP) {
            _patchtestreg(list, NO_REG)
            list = _getjump(list)
        }
    }


    _patchlistaux: func(list, vtarget, reg, dtarget: Int) {
        while (list != NO_JUMP) {
            next := _getjump(list)
            if (_patchtestreg(list, reg))
                _fixjump(list, vtarget)
            else
                _fixjump(list, dtarget)  /* jump to default target */
            list = next
        }
    }


    _dischargejpc: func {
        pc := f code getSize()
        _patchlistaux(jpc, pc, NO_REG, pc)
        jpc = NO_JUMP
    }


    luaK_patchlist: func(list, target: Int) {
        pc := f code getSize()
        if (target == pc)
            luaK_patchtohere(list)
        else {
            version(debug) {
                assert(target < pc)
            }
            _patchlistaux(list, target, NO_REG, target)
        }
    }


    luaK_patchtohere: func(list: Int) {
        luaK_getlabel()
        luaK_concat(jpc&, list)
    }


    luaK_concat: func(l1: Int*, l2: Int) {
        if (l2 == NO_JUMP)
            return
        else if (l1@ == NO_JUMP)
            l1@ = l2
        else {
            list := l1@
            next := _getjump(list)
            while (next != NO_JUMP) {  /* find last element */
                list = next
                next = _getjump(next)
            }
            _fixjump(list, l2)
        }
    }


    luaK_code: func(i: Instruction) -> Int{
        _dischargejpc()  /* `pc' will change */
        pc := f code getSize()
        /* put new instruction in code array */
        f code add(i)
        /* save corresponding line information */
        f lineinfo add(ls lastline)
        return pc
    }


   luaK_codeABC: func(o: OpCode, a, b, c: Int) -> Int {
        version(debug) {
            assert(o getOpMode() == OpMode iABC)
            assert(o getBMode() != OpArgMask OpArgN || b == 0)
            assert(o getCMode() != OpArgMask OpArgN || c == 0)
            assert(a <= MAXARG_A)
            assert(b <= MAXARG_B)
            assert(c <= MAXARG_C)
        }
        return luaK_code(Instruction createABC(o, a, b, c))
    }


    luaK_codeABx: func(o: OpCode, a: Int, bc: UInt) -> Int {
        version(debug) {
            assert(o getOpMode() == OpMode iABx || o getOpMode() == OpMode iAsBx)
            assert(o getCMode() == OpArgMask OpArgN)
            assert(a <= MAXARG_A)
            assert(bc <= MAXARG_Bx)
        }
        return luaK_code(Instruction createABx(o, a, bc))
    }


    luaK_codeABxX: func(o: OpCode, reg, k: Int) -> Int {
        if (k < MAXARG_Bx)
            return luaK_codeABx(o, reg, k + 1)
        else {
            p := luaK_codeABx(o, reg, 0)
            version(debug) {
                assert(k <= MAXARG_Ax)
            }
            luaK_code(Instruction createAx(OpCode OP_EXTRAARG, k))
            return p
        }
    }


    luaK_checkstack: func(n: Int) {
        newstack := freereg + n
        if (newstack > f maxstacksize) {
            if (newstack >= MAXSTACK)
                ls syntaxError("function or expression too complex")
            f maxstacksize = newstack
        }
    }


    luaK_reserveregs: func(n: Int) {
        luaK_checkstack(n)
        freereg += n
    }


    _freereg: func(reg: Int) {
        if (!(reg & BITRK) && reg >= nactvar) {
            freereg -= 1
            version(debug) {
                assert(reg == freereg)
            }
        }
    }


    _freeexp: func(e: ExpDesc@) {
        if (e k == ExpKind VNONRELOC)
            _freereg(e info)
    }


    _addk: func(key, v: LuaAny) -> Int {
        if (h v contains?(key)) {
            n := h v get(key) as LuaNumber
            k := n v as Int
            //if (f k[k] rawequal(v))
                return k
                /* else may be a collision (e.g., between 0.0 and "\0\0\0\0\0\0\0\0");
                   go through and create a new entry for this value */
        }
        /* constant not found; create a new entry */
        nk := f k getSize()
        h v put(key, LuaNumber new(nk))
        f k add(v)
        return nk
    }


    luaK_stringK: func(s: String) -> Int {
        o := LuaString new(s)
        return _addk(o, o)
    }


    luaK_numberK: func(r: Double) -> Int {
        o := LuaNumber new(r)
        if (r == 0 || !(r == r)) {  /* handle -0 and NaN */
            /* use raw representation as key to avoid numeric problems */
            k := LuaString new(r toString())
            return _addk(k, o)
        }
        else
            return _addk(o, o)  /* regular case */
    }


    _boolK: func(b: Bool) -> Int {
        o := LuaBoolean new(b)
        return _addk(o, o)
    }


    _nilK: func -> Int {
        v := LuaNil new()
        /* cannot use nil as key; instead use table itself to represent nil */
        return _addk(h, v)
    }


    luaK_setreturns: func(e: ExpDesc@, nresults: Int) {
        pi := f code data as Instruction* + e info
        if (e k == ExpKind VCALL) {  /* expression is an open function call? */
            pi@ = pi@ setarg_C(nresults + 1)
        }
        else if (e k == ExpKind VVARARG) {
            pi@ = pi@ setarg_B(nresults + 1)
            pi@ = pi@ setarg_A(freereg)
            luaK_reserveregs(1)
        }
    }


    luaK_setoneret: func(e: ExpDesc@) {
        pi := f code data as Instruction* + e info
        if (e k == ExpKind VCALL) {  /* expression is an open function call? */
            e k = ExpKind VNONRELOC
            e info = pi@ getarg_A()
        }
        else if (e k == ExpKind VVARARG) {
            pi@ = pi@ setarg_B(2)
            e k = ExpKind VRELOCABLE  /* can relocate its simple result */
        }
    }


    luaK_dischargevars: func(e: ExpDesc@) {
        k := e k
        match {
            case k == ExpKind VLOCAL =>
                e k = ExpKind VNONRELOC
            case k == ExpKind VUPVAL =>
                e info = luaK_codeABC(OpCode OP_GETUPVAL, 0, e info, 0)
                e k = ExpKind VRELOCABLE
            case k == ExpKind VINDEXED =>
                op := OpCode OP_GETTABUP  /* assume 't' is in an upvalue */
                _freereg(e ind_idx)
                if (e ind_vt == ExpKind VLOCAL) {  /* 't' is in a register? */
                    _freereg(e ind_t)
                    op = OpCode OP_GETTABLE
                }
                e info = luaK_codeABC(op, 0, e ind_t, e ind_idx)
                e k = ExpKind VRELOCABLE
            case k == ExpKind VVARARG ||
                 k == ExpKind VCALL =>
                luaK_setoneret(e&)
        }
    }


    _code_label: func(A, b, jump: Int) -> Int {
        luaK_getlabel()  /* those instructions may be jump targets */
        return luaK_codeABC(OpCode OP_LOADBOOL, A, b, jump)
    }


    _discharge2reg: func(e: ExpDesc@, reg: Int) {
        luaK_dischargevars(e&)
        match (e k) {
            case ExpKind VNIL =>
                luaK_nil(reg, 1)
            case ExpKind VFALSE =>
                luaK_codeABC(OpCode OP_LOADBOOL, reg, 0, 0)
            case ExpKind VTRUE =>
                luaK_codeABC(OpCode OP_LOADBOOL, reg, 1, 0)
            case ExpKind VK =>
                luaK_codeABxX(OpCode OP_LOADK, reg, e info)
            case ExpKind VKNUM =>
                luaK_codeABxX(OpCode OP_LOADK, reg, luaK_numberK(e nval))
            case ExpKind VRELOCABLE =>
                pc := f code data as Instruction* + e info
                pc@ = pc@ setarg_A(reg)
            case ExpKind VNONRELOC =>
                if (reg != e info)
                    luaK_codeABC(OpCode OP_MOVE, reg, e info, 0)
            case =>
                version(debug) {
                    assert(e k == ExpKind VVOID || e k == ExpKind VJMP)
                }
                return  /* nothing to do... */
        }
        e info = reg
        e k = ExpKind VNONRELOC
    }


    _discharge2anyreg: func(e: ExpDesc@) {
        if (e k != ExpKind VNONRELOC) {
            luaK_reserveregs(1)
            _discharge2reg(e&, freereg-1)
        }
    }


    _exp2reg: func(e: ExpDesc@, reg: Int) {
        _discharge2reg(e&, reg)
        if (e k == ExpKind VJMP)
            luaK_concat(e t&, e info)  /* put this jump in `t' list */
        if (e hasjumps()) {
            p_f := NO_JUMP  /* position of an eventual LOAD false */
            p_t := NO_JUMP  /* position of an eventual LOAD true */
            if (_need_value(e t) || _need_value(e f)) {
                fj := (e k == ExpKind VJMP) ? NO_JUMP : luaK_jump()
                p_f = _code_label(reg, 0, 1)
                p_t = _code_label(reg, 1, 0)
                luaK_patchtohere(fj)
            }
            _final := luaK_getlabel()  /* position after whole expression */
            _patchlistaux(e f, _final, reg, p_f)
            _patchlistaux(e t, _final, reg, p_t)
        }
        e f = NO_JUMP
        e t = NO_JUMP
        e info = reg
        e k = ExpKind VNONRELOC
    }


    luaK_exp2nextreg: func(e: ExpDesc@) {
        luaK_dischargevars(e&)
        _freeexp(e&)
        luaK_reserveregs(1)
        _exp2reg(e&, freereg - 1)
    }


    luaK_exp2anyreg: func(e: ExpDesc@) -> Int {
        luaK_dischargevars(e&)
        if (e k == ExpKind VNONRELOC) {
            if (! e hasjumps())
                return e info  /* exp is already in a register */
            if (e info >= nactvar) {  /* reg. is not a local? */
                _exp2reg(e&, e info)  /* put value on it */
                return e info
            }
        }
        luaK_exp2nextreg(e&)  /* default */
        return e info
    }


    luaK_exp2anyregup: func(e: ExpDesc@) {
        if (e k != ExpKind VUPVAL || e hasjumps())
            luaK_exp2anyreg(e&)
    }


    luaK_exp2val: func(e: ExpDesc@) {
        if (e hasjumps())
            luaK_exp2anyreg(e&)
        else
            luaK_dischargevars(e&)
    }


    luaK_exp2RK: func(e: ExpDesc@) -> Int {
        luaK_exp2val(e&)
        k := e k
        nk := f k getSize()
        match {
            case k == ExpKind VTRUE ||
                 k == ExpKind VFALSE ||
                 k == ExpKind VNIL =>
                if (nk <= MAXINDEXRK) {  /* constant fits in RK operand? */
                    e info = (e k == ExpKind VNIL) ? _nilK() : _boolK(e k == ExpKind VTRUE)
                    e k =  ExpKind VK
                    return e info | BITRK
                }
            case k == ExpKind VKNUM =>
                e info = luaK_numberK(e nval)
                e k = ExpKind VK
                if (e info <= MAXINDEXRK)  /* constant fits in argC? */
                    return e info | BITRK
            case k == ExpKind VK =>
                if (e info <= MAXINDEXRK)  /* constant fits in argC? */
                    return e info | BITRK
        }
        /* not a constant in the right range: put it in a register */
        return luaK_exp2anyreg(e&)
    }


    luaK_storevar: func(var, ex: ExpDesc@) {
        match (var k) {
            case ExpKind VLOCAL =>
                _freeexp(ex&)
                _exp2reg(ex&, var info)
            case ExpKind VUPVAL =>
                e := luaK_exp2anyreg(ex&)
                luaK_codeABC(OpCode OP_SETUPVAL, e, var info, 0)
            case ExpKind VINDEXED =>
                op := (var ind_vt == ExpKind VLOCAL) ? OpCode OP_SETTABLE : OpCode OP_SETTABUP
                e := luaK_exp2RK(ex&)
                luaK_codeABC(op, var ind_t, var ind_idx, e)
            case =>
                version(debug) {
                    assert(false)  /* invalid var kind to store */
                }
        }
        _freeexp(ex&)
    }


    luaK_self: func(e, key: ExpDesc@) {
        luaK_exp2anyreg(e&)
        _freeexp(e&)
        _func := freereg
        luaK_codeABC(OpCode OP_SELF, _func, e info, luaK_exp2RK(key&))
        _freeexp(key&)
        luaK_reserveregs(2)
        e info = _func
        e k = ExpKind VNONRELOC
    }


    _invertjump: func(e: ExpDesc@) {
        pc := _getjumpcontrol(e info)
        version(debug) {
            op := pc@ getOpcode()
            assert(op testTMode())
            assert(op != OpCode OP_TESTSET)
            assert(op != OpCode OP_TEST)
        }
        pc@ = pc@ setarg_A(pc@ getarg_A() == 0 ? 1 : 0)
    }


    _jumponcond: func(e: ExpDesc@, cond: Int) -> Int {
        if (e k == ExpKind VRELOCABLE) {
            ie := f code get(e info)
            if (ie getOpcode() == OpCode OP_NOT) {
                f code removeAt(f code lastIndex()) /* remove previous OP_NOT */
                return _condjump(OpCode OP_TEST, ie getarg_B(), 0, cond == 0 ? 1 : 0)
            }
            /* else go through */
        }
        _discharge2anyreg(e&)
        _freeexp(e&)
        return _condjump(OpCode OP_TESTSET, NO_REG, e info, cond)
    }


    luaK_goiftrue: func(e: ExpDesc@) {
        pc: Int  /* pc of last jump */
        luaK_dischargevars(e&)
        k := e k
        match {
            case k == ExpKind VK ||
                 k == ExpKind VKNUM ||
                 k == ExpKind VTRUE =>
                pc = NO_JUMP  /* always true; do nothing */
            case k == ExpKind VJMP =>
                _invertjump(e&)
                pc = e info
            case k == ExpKind VFALSE =>
                if (! e hasjumps())
                    pc = luaK_jump()  /* always jump */
                else
                    pc = _jumponcond(e&, 0)
            case =>
                pc = _jumponcond(e&, 0)
        }
        luaK_concat(e f&, pc)  /* insert last jump in `f' list */
        luaK_patchtohere(e t)
        e t = NO_JUMP
    }


    luaK_goiffalse: func(e: ExpDesc@) {
        pc: Int  /* pc of last jump */
        luaK_dischargevars(e&)
        k := e k
        match {
            case k == ExpKind VNIL ||
                 k == ExpKind VFALSE =>
                pc = NO_JUMP  /* always false; do nothing */
            case k == ExpKind VJMP =>
                pc = e info
            case k == ExpKind VTRUE =>
                if (! e hasjumps())
                    pc = luaK_jump()  /* always jump */
                else
                    pc = _jumponcond(e&, 1)
            case =>
                pc = _jumponcond(e&, 1)
        }
        luaK_concat(e t&, pc)  /* insert last jump in `t' list */
        luaK_patchtohere(e f)
        e f = NO_JUMP
    }


    _codenot: func(e: ExpDesc@) {
        luaK_dischargevars(e&)
        k := e k
        match {
            case k == ExpKind VNIL ||
                 k == ExpKind VFALSE =>
                e k = ExpKind VTRUE
            case k == ExpKind VK ||
                 k == ExpKind VKNUM ||
                 k == ExpKind VTRUE =>
                e k = ExpKind VFALSE
            case k == ExpKind VJMP =>
                _invertjump(e&)
            case k == ExpKind VRELOCABLE ||
                 k == ExpKind VNONRELOC =>
                _discharge2anyreg(e&)
                _freeexp(e&)
                e info = luaK_codeABC(OpCode OP_NOT, 0, e info, 0)
                e k = ExpKind VRELOCABLE
            case =>
                version(debug) {
                    assert(false)  /* cannot happen */
                }
        }
        /* interchange true and false lists */
        temp := e f; e f = e t; e t = temp
        _removevalues(e f)
        _removevalues(e t)
    }


    luaK_indexed: func(t, k: ExpDesc@) {
        version(debug) {
            assert(! t hasjumps())
        }
        t ind_t = t info
        t ind_idx = luaK_exp2RK(k&)
        version(debug) {
            if (t k != ExpKind VUPVAL)
                assert(t k vkisinreg())
        }
        t ind_vt = (t k == ExpKind VUPVAL) ? ExpKind VUPVAL : ExpKind VLOCAL
        t k = ExpKind VINDEXED
    }


    _constfolding: func(op: OpCode, e1, e2: ExpDesc@) -> Bool {
        if (! e1 isnumeral() || ! e2 isnumeral())
            return false
        if ((op == OpCode OP_DIV || op == OpCode OP_MOD) && e2 nval == 0)
            return false  /* do not attempt to divide by 0 */
        match (op) {
            case OpCode OP_ADD =>
                e1 nval = e1 nval + e2 nval
            case OpCode OP_SUB =>
                e1 nval = e1 nval - e2 nval
            case OpCode OP_MUL =>
                e1 nval = e1 nval * e2 nval
            case OpCode OP_DIV =>
                e1 nval = e1 nval / e2 nval
            case OpCode OP_MOD =>
                e1 nval = e1 nval mod(e2 nval)
            case OpCode OP_POW =>
                e1 nval = e1 nval pow(e2 nval)
            case =>
                assert(false)
        }
        return true
    }


    _codearith: func(op: OpCode, e1, e2: ExpDesc@, line: Int) {
        if (_constfolding(op, e1&, e2&))
            return
        else {
            o2 := (op != OpCode OP_UNM && op != OpCode OP_LEN) ? luaK_exp2RK(e2&) : 0
            o1 := luaK_exp2RK(e1&)
            if (o1 > o2) {
                _freeexp(e1&)
                _freeexp(e2&)
            }
            else {
                _freeexp(e2&)
                _freeexp(e1&)
            }
            e1 info = luaK_codeABC(op, 0, o1, o2)
            e1 k = ExpKind VRELOCABLE
            luaK_fixline(line)
        }
    }


    _codecomp: func(op: OpCode, cond: Int, e1, e2: ExpDesc@) {
        o1 := luaK_exp2RK(e1&)
        o2 := luaK_exp2RK(e2&)
        _freeexp(e2&)
        _freeexp(e1&)
        if (! cond && op != OpCode OP_EQ) {
            /* exchange args to replace by `<' or `<=' */
            temp := o1; o1 = o2; o2 = temp;  /* o1 <==> o2 */
            cond = 1
        }
        e1 info = _condjump(op, cond, o1, o2)
        e1 k = ExpKind VJMP
    }


    luaK_prefix: func(op: UnOpr, e: ExpDesc@, line: Int) {
        e2: ExpDesc
        e2 t = NO_JUMP
        e2 f = NO_JUMP
        e2 k = ExpKind VKNUM
        e2 nval = 0
        match (op) {
            case UnOpr OPR_MINUS =>
                if (e isnumeral())  /* minus constant? */
                    e nval = - e nval  /* fold it */
                else {
                    luaK_exp2anyreg(e&)
                    _codearith(OpCode OP_UNM, e&, e2&, line)
                }
            case UnOpr OPR_NOT =>
                _codenot(e&)
            case UnOpr OPR_LEN =>
                luaK_exp2anyreg(e&)  /* cannot operate on constants */
                _codearith(OpCode OP_LEN, e&, e2&, line)
            case =>
                version(debug) {
                    assert(false)
                }
        }
    }


    luaK_infix: func(op: BinOpr, v: ExpDesc@) {
        match {
            case op == BinOpr OPR_AND =>
                luaK_goiftrue(v&)
            case op == BinOpr OPR_OR =>
                luaK_goiffalse(v&)
            case op == BinOpr OPR_CONCAT =>
                luaK_exp2nextreg(v&)  /* operand must be on the `stack' */
            case op == BinOpr OPR_ADD ||
                 op == BinOpr OPR_SUB ||
                 op == BinOpr OPR_MUL ||
                 op == BinOpr OPR_DIV ||
                 op == BinOpr OPR_MOD ||
                 op == BinOpr OPR_POW =>
                if (! v isnumeral())
                    luaK_exp2RK(v&)
            case =>
                luaK_exp2RK(v&)
        }
    }


    luaK_posfix: func(op: BinOpr, e1, e2: ExpDesc@, line: Int) {
        match {
            case op == BinOpr OPR_AND =>
                version(debug) {
                    assert(e1 t == NO_JUMP)  /* list must be closed */
                }
                luaK_dischargevars(e2&)
                luaK_concat(e2 f&, e1 f)
                e1 = e2
            case op == BinOpr OPR_OR =>
                version(debug) {
                    assert(e1 f == NO_JUMP)  /* list must be closed */
                }
                luaK_dischargevars(e2&)
                luaK_concat(e2 t&, e1 t)
                e1 = e2
            case op == BinOpr OPR_CONCAT =>
                luaK_exp2val(e2&)
                pi := f code data as Instruction* + e2 info
                if (e2 k == ExpKind VRELOCABLE && pi@ getOpcode() == OpCode OP_CONCAT) {
                    version(debug) {
                        assert(e1 info == pi@ getarg_B() - 1)
                    }
                    _freeexp(e1&)
                    pi@ = pi@ setarg_B(e1 info)
                    e1 k = ExpKind VRELOCABLE
                    e1 info = e2 info
                }
                else {
                    luaK_exp2nextreg(e2&)  /* operand must be on the 'stack' */
                    _codearith(OpCode OP_CONCAT, e1&, e2&, line)
                }
            case op == BinOpr OPR_ADD =>
                _codearith(OpCode OP_ADD, e1&, e2&, line)
            case op == BinOpr OPR_SUB =>
                _codearith(OpCode OP_SUB, e1&, e2&, line)
            case op == BinOpr OPR_MUL =>
                _codearith(OpCode OP_MUL, e1&, e2&, line)
            case op == BinOpr OPR_DIV =>
                _codearith(OpCode OP_DIV, e1&, e2&, line)
            case op == BinOpr OPR_MOD =>
                _codearith(OpCode OP_MOD, e1&, e2&, line)
            case op == BinOpr OPR_POW =>
                _codearith(OpCode OP_POW, e1&, e2&, line)
            case op == BinOpr OPR_EQ =>
                _codecomp(OpCode OP_EQ, 1, e1&, e2&)
            case op == BinOpr OPR_LT =>
                _codecomp(OpCode OP_LT, 1, e1&, e2&)
            case op == BinOpr OPR_LE =>
                _codecomp(OpCode OP_LE, 1, e1&, e2&)
            case op == BinOpr OPR_NE =>
                _codecomp(OpCode OP_EQ, 0, e1&, e2&)
            case op == BinOpr OPR_GT =>
                _codecomp(OpCode OP_LE, 0, e1&, e2&)
            case op == BinOpr OPR_GE =>
                _codecomp(OpCode OP_LT, 0, e1&, e2&)
            case =>
                version(debug) {
                    assert(false)
                }
        }
    }


    luaK_fixline: func(line: Int) {
        f lineinfo set(f code getSize() - 1, line)
    }


    luaK_setlist: func(base, nelems, tostore: Int) {
        c :=  (nelems - 1)/LFIELDS_PER_FLUSH + 1
        b := (tostore == LUA_MULTRET) ? 0 : tostore
        version(debug) {
            assert(tostore != 0)
        }
        if (c <= MAXARG_C)
            luaK_codeABC(OpCode OP_SETLIST, base, b, c)
        else if (c <= MAXARG_Ax) {
            luaK_codeABC(OpCode OP_SETLIST, base, b, 0)
            version(debug) {
                assert(c <= MAXARG_Ax)
            }
            luaK_code(Instruction createAx(OpCode OP_EXTRAARG, c))
        }
        else
            ls syntaxError("constructor too long")
        freereg = base + 1  /* free registers with list values */
    }

    checklimit: func(v, l: Int, what: String) {
        if (v > l) {
            line := f linedefined
            where := (line == 0) ? "main function" : "function at line %d" format(line)
            msg := "too many %s (limit is %d) in %s" format(what, l, where)
            ls syntaxError(msg)
        }
    }

}


/*
** nodes for block list (list of active blocks)
*/
BlockCnt: cover {
    previous: BlockCnt*  /* chain */
    breaklist: Int  /* list of jumps out of this loop */
    nactvar: UInt8  /* # active locals outside the breakable structure */
    upval: Bool  /* true if some variable in the block is an upvalue */
    isbreakable: Bool  /* true if `block' is a loop */
}

/*
** structure to chain all variables in the left-hand side of an
** assignment
*/
LHS_assign: cover {
    prev: LHS_assign*
    v: ExpDesc  /* variable (global, local, upvalue, or indexed) */
}


ConsControl: cover {
    v: ExpDesc  /* last list item read */
    t: ExpDesc*  /* table descriptor */
    nh: Int  /* total number of `record' elements */
    na: Int  /* total number of array elements */
    tostore: Int  /* number of array elements pending to be stored */
}



Parser: final class extends Lexer {
    fs: FuncState  /* `FuncState' is private to the parser */
    actvar: ArrayList<UInt16>  /* list of all active local variables */

    init: func {}


    loadfile: func(filename: String) -> LuaProto {
        srcname: String
        reader: FileReader
        if (filename equals?("-")) {
            srcname = "=stdin"
//            reader = FileReader new(stdin)
        }
        else {
            srcname = "@" + filename
            reader = FileReader new(filename)
        }
        setInput(reader, srcname)
        shebang()
//        if (_testnext(0x1b)) {
//            return undump
//        }
//        else
            return parse(ArrayList<UInt16> new())
    }


    parse: func(=actvar) -> LuaProto {
        _mainfunc()
        next()  /* read first token */
        chunk()  /* read main chunk */
        _check(TK_EOS)
        fs finalize()
        version(debug) {
            assert(! fs prev)
            assert(fs f upvalues getSize() == 1)
        }
        return fs f
    }

/*============================================================*/
/* GRAMMAR RULES */
/*============================================================*/


    fieldsel: func(v: ExpDesc@) {
        /* fieldsel -> ['.' | ':'] NAME */
        key: ExpDesc
        fs luaK_exp2anyregup(v&)
        next()  /* skip the dot or colon */
        _checkname(key&)
        fs luaK_indexed(v&, key&)
    }


    yindex: func(v: ExpDesc@) {
        /* index -> '[' expr ']' */
        next()  /* skip the '[' */
        expr(v&)
        fs luaK_exp2val(v&)
        _checknext(']' as Int)
    }


/*
** {======================================================================
** Rules for Constructors
** =======================================================================
*/


    recfield: func(cc: ConsControl@) {
        /* recfield -> (NAME | `['exp1`]') = exp1 */
        reg := fs freereg
        key: ExpDesc
        if (t token == TK_NAME) {
            fs checklimit(cc nh, MAX_INT, "items in a constructor")
            _checkname(key&)
        }
        else  /* ls->t.token == '[' */
            yindex(key&)
        cc nh += 1
        _checknext('=' as Int)
        rkkey := fs luaK_exp2RK(key&)
        val: ExpDesc
        expr(val&)
        fs luaK_codeABC(OpCode OP_SETTABLE, cc t@ info, rkkey, fs luaK_exp2RK(val&))
        fs freereg = reg  /* free registers */
    }


    closelistfield: func(cc: ConsControl@) {
        if (cc v k == ExpKind VVOID)
            return;  /* there is no list item */
        fs luaK_exp2nextreg(cc v&)
        cc v k = ExpKind VVOID
        if (cc tostore == LFIELDS_PER_FLUSH) {
            fs luaK_setlist(cc t@ info, cc na, cc tostore)  /* flush */
            cc tostore = 0  /* no more items pending */
        }
    }


    lastlistfield: func(cc: ConsControl@) {
        if (cc tostore == 0)
            return
        if (cc v k hasmultret()) {
            fs luaK_setreturns(cc v&, LUA_MULTRET)
            fs luaK_setlist(cc t@ info, cc na, LUA_MULTRET)
            cc na -= 1  /* do not count last expression (unknown number of elements) */
        }
        else {
            if (cc v k != ExpKind VVOID)
                fs luaK_exp2nextreg(cc v&)
            fs luaK_setlist(cc t@ info, cc na, cc tostore)
        }
    }


    listfield: func(cc: ConsControl@) {
        /* listfield -> exp */
        expr(cc v&)
        fs checklimit(cc na, MAX_INT, "items in a constructor")
        cc na += 1
        cc tostore += 1
    }


    field: func(cc: ConsControl@) {
        /* field -> listfield | recfield */
        match (t token) {
            case TK_NAME =>  /* may be 'listfield' or 'recfield' */
                if (lookahead() != '=')  /* expression? */
                    listfield(cc&)
                else
                    recfield(cc&)
            case '[' =>
                recfield(cc&)
            case =>
                listfield(cc&)
        }
    }


    constructor: func(_t: ExpDesc@) {
        /* constructor -> '{' [ field { sep field } [sep] ] '}'
           sep -> ',' | ';' */
        line := linenumber
        pc := fs luaK_codeABC(OpCode OP_NEWTABLE, 0, 0, 0)
        cc: ConsControl
        cc na = 0
        cc nh = 0
        cc tostore = 0
        cc t = _t&
        init_exp(_t&, ExpKind VRELOCABLE, pc)
        init_exp(cc v&, ExpKind VVOID, 0)  /* no value (yet) */
        fs luaK_exp2nextreg(_t&)  /* fix it at stack top (for gc) */
        _checknext('{' as Int)
        while (true) {
            version(debug) {
                assert(cc v k == ExpKind VVOID || cc tostore > 0)
            }
            if (t token == '}')
                break
            closelistfield(cc&)
            field(cc&)
            if (! _testnext(',' as Int) && ! _testnext(';' as Int))
                break
        }
        _check_match('}' as Int, '{' as Int, line)
        lastlistfield(cc&)
        pi := fs f code data as Instruction* + pc
        pi@ = pi@ setarg_B(int2fb(cc na))  /* set initial array size */
        pi@ = pi@ setarg_C(int2fb(cc nh))  /* set initial table size */
    }

/* }====================================================================== */



    parlist: func {
        /* parlist -> [ param { `,' param } ] */
        f := fs f
        nparams := 0
        f is_vararg = false
        if (t token != ')') {  /* is `parlist' not empty? */
            while (! f is_vararg) {
                match (t token) {
                    case TK_NAME =>  /* param -> NAME */
                        _new_localvar(_str_checkname())
                        nparams += 1
                    case TK_DOTS =>  /* param -> `...' */
                        next()
                        f is_vararg = true
                    case =>
                        syntaxError("<name> or '...' expected")
                }
                if (! _testnext(',' as Int))
                    break
            }
        }
        _adjustlocalvars(nparams)
        f numparams = fs nactvar
        fs luaK_reserveregs(fs nactvar)  /* reserve register for parameters */
    }


    body: func(e: ExpDesc@, needself: Bool, line: Int) {
        /* body ->  `(' parlist `)' chunk END */
        fs = FuncState new(this, fs)
        f := fs f
        f linedefined = line
        _checknext('(' as Int)
        if (needself) {
            _new_localvarliteral("self")
            _adjustlocalvars(1)
        }
        parlist()
        _checknext(')' as Int)
        chunk()
        f lastlinedefined = linenumber
        _check_match(TK_END, TK_FUNCTION, line)
        _codeclosure(f, e&)
        fs = fs finalize()
    }


    explist1: func(v: ExpDesc@) -> Int {
        /* explist1 -> expr { `,' expr } */
        n := 1  /* at least one expression */
        expr(v&)
        while (_testnext(',' as Int)) {
            fs luaK_exp2nextreg(v&)
            expr(v&)
            n += 1
        }
        return n
    }


    funcargs: func(f: ExpDesc@, line: Int) {
        args: ExpDesc
        match (t token) {
            case '(' =>  /* funcargs -> `(' [ explist1 ] `)' */
                next()
                if (t token == ')')  /* arg list is empty? */
                    args k = ExpKind VVOID
                else {
                    explist1(args&)
                    fs luaK_setreturns(args&, LUA_MULTRET)
                }
                _check_match(')' as Int, '(' as Int, line)
            case '{' =>  /* funcargs -> constructor */
                constructor(args&)
            case TK_STRING =>  /* funcargs -> STRING */
                _codestring(args&, t str);
                next()  /* must use `seminfo' before `next' */
            case =>
                syntaxError("function arguments expected")
        }
        version(debug) {
            assert(f k == ExpKind VNONRELOC)
        }
        nparams: Int
        base := f info  /* base register for call */
        if (args k hasmultret())
            nparams = LUA_MULTRET  /* open call */
        else {
            if (args k != ExpKind VVOID)
                fs luaK_exp2nextreg(args&)  /* close last argument */
            nparams = fs freereg - (base+1)
        }
        init_exp(f&, ExpKind VCALL, fs luaK_codeABC(OpCode OP_CALL, base, nparams+1, 2))
        fs luaK_fixline(line)
        fs freereg = base+1  /* call remove function and arguments and leaves
                                 (unless changed) one result */
    }




/*
** {======================================================================
** Expression parsing
** =======================================================================
*/


    prefixexp: func(v: ExpDesc@) {
        /* prefixexp -> NAME | '(' expr ')' */
        match (t token) {
            case '(' =>
                line := linenumber
                next()
                expr(v&)
                _check_match(')' as Int, '(' as Int, line)
                fs luaK_dischargevars(v&)
            case TK_NAME =>
                _singlevar(v&)
            case =>
                syntaxError("unexpected symbol")
        }
    }


    primaryexp: func(v: ExpDesc@) {
        /* primaryexp ->
            prefixexp { `.' NAME | `[' exp `]' | `:' NAME funcargs | funcargs } */
        line := linenumber
        prefixexp(v&)
        while (true) {
            match {
                case t token == '.' =>  /* fieldsel */
                    fieldsel(v&)
                case t token == '[' =>  /* `[' exp1 `]' */
                    key: ExpDesc
                    fs luaK_exp2anyregup(v&)
                    yindex(key&)
                    fs luaK_indexed(v&, key&)
                case t token == ':' =>  /* `:' NAME funcargs */
                    key: ExpDesc
                    next()
                    _checkname(key&)
                    fs luaK_self(v&, key&)
                    funcargs(v&, line)
                case t token == '(' ||
                     t token == TK_STRING ||
                     t token == '{' =>  /* funcargs */
                    fs luaK_exp2nextreg(v&)
                    funcargs(v&, line)
                case =>
                    return
            }
        }
    }


    simpleexp: func(v: ExpDesc@) {
        /* simpleexp -> NUMBER | STRING | NIL | TRUE | FALSE | ... |
                        constructor | FUNCTION body | primaryexp */
        match (t token) {
            case TK_NUMBER =>
                init_exp(v&, ExpKind VKNUM, 0)
                v nval = t num
            case TK_STRING =>
                _codestring(v&, t str);
            case TK_NIL =>
                init_exp(v&, ExpKind VNIL, 0)
            case TK_TRUE =>
                init_exp(v&, ExpKind VTRUE, 0)
            case TK_FALSE =>
                init_exp(v&, ExpKind VFALSE, 0)
            case TK_DOTS =>  /* vararg */
                _check_condition(fs f is_vararg,
                                "cannot use '...' outside a vararg function")
                init_exp(v&, ExpKind VVARARG, fs luaK_codeABC(OpCode OP_VARARG, 0, 1, 0))
            case '{' =>  /* constructor */
                constructor(v&)
                return
            case TK_FUNCTION =>
                next()
                body(v&, false, linenumber)
                return
            case =>
                primaryexp(v&)
                return
        }
        next()
    }


    getunopr: func(op: Int) -> UnOpr {
        match (op) {
            case TK_NOT =>
                return UnOpr OPR_NOT
            case '-' =>
                return UnOpr OPR_MINUS
            case '#' =>
                return UnOpr OPR_LEN
            case =>
                return UnOpr OPR_NOUNOPR
        }
        return UnOpr OPR_NOUNOPR // avoir error
    }


    getbinopr: func(op: Int) -> BinOpr {
        match (op) {
            case '+' =>
                return BinOpr OPR_ADD
            case '-' =>
                return BinOpr OPR_SUB
            case '*' =>
                return BinOpr OPR_MUL
            case '/' =>
                return BinOpr OPR_DIV
            case '%' =>
                return BinOpr OPR_MOD
            case '^' =>
                return BinOpr OPR_POW
            case TK_CONCAT =>
                return BinOpr OPR_CONCAT
            case TK_NE =>
                return BinOpr OPR_NE
            case TK_EQ =>
                return BinOpr OPR_EQ
            case '<' =>
                return BinOpr OPR_LT
            case TK_LE =>
                return BinOpr OPR_LE
            case '>' =>
                return BinOpr OPR_GT
            case TK_GE =>
                return BinOpr OPR_GE
            case TK_AND =>
                return BinOpr OPR_AND
            case TK_OR =>
                return BinOpr OPR_OR
            case =>
                return BinOpr OPR_NOBINOPR
        }
        return BinOpr OPR_NOBINOPR // avoid error
    }


/*
** subexpr -> (simpleexp | unop subexpr) { binop subexpr }
** where `binop' is any binary operator with a priority higher than `limit'
*/
    subexpr: func(v: ExpDesc@, limit: Int) -> BinOpr {
        _enterlevel()
        uop := getunopr(t token)
        if (uop != UnOpr OPR_NOUNOPR) {
            line := linenumber
            next()
            subexpr(v&, UNARY_PRIORITY)
            fs luaK_prefix(uop, v&, line)
        }
        else
            simpleexp(v&)
        /* expand while operators have priorities higher than `limit' */
        op := getbinopr(t token)
        while (op != BinOpr OPR_NOBINOPR && PRIORITY_LEFT[op] > limit) {
            v2: ExpDesc
            line := linenumber
            next()
            fs luaK_infix(op, v&)
            /* read sub-expression with higher priority */
            nextop := subexpr(v2&, PRIORITY_RIGHT[op])
            fs luaK_posfix(op, v&, v2&, line)
            op = nextop
        }
        _leavelevel()
        return op;  /* return first untreated operator */
    }


    expr: func(v: ExpDesc@) {
        subexpr(v&, 0)
    }

/* }==================================================================== */



/*
** {======================================================================
** Rules for Statements
** =======================================================================
*/

    block_follow: func(token: Int) -> Bool {
        return (token == TK_ELSE ||
                token == TK_ELSEIF ||
                token == TK_END ||
                token == TK_UNTIL ||
                token == TK_EOS)
    }


    block: func {
        /* block -> chunk */
        bl: BlockCnt
        fs enterblock(bl&, false)
        chunk()
        version(debug) {
            assert(bl breaklist == NO_JUMP)
        }
        fs leaveblock()
    }


/*
** check whether, in an assignment to a local variable, the local variable
** is needed in a previous assignment (to a table). If so, save original
** local value in a safe place and use this safe copy in the previous
** assignment.
*/
    _check_conflict: func(lh: LHS_assign*, v: ExpDesc@) {
        extra := fs freereg  /* eventual position to save local variable */
        conflict := false
        while (lh) {
            /* conflict in table 't'? */
            if (lh@ v ind_vt == v k && lh@ v ind_t == v info) {
                conflict = true
                lh@ v ind_vt = ExpKind VLOCAL
                lh@ v ind_t = extra  /* previous assignment will use safe copy */
            }
            /* conflict in index 'idx'? */
            if (v k == ExpKind VLOCAL && lh@ v ind_idx == v info) {
                conflict = true
                lh@ v ind_idx = extra  /* previous assignment will use safe copy */
            }
            lh = lh@ prev
        }
        if (conflict) {
            op := (v k == ExpKind VLOCAL) ? OpCode OP_MOVE : OpCode OP_GETUPVAL
            fs luaK_codeABC(op, fs freereg, v info, 0)  /* make copy */
            fs luaK_reserveregs(1)
        }
    }


    assignment: func(lh: LHS_assign@, nvars: Int) {
        e: ExpDesc
        _check_condition(lh v k vkisvar(), "syntax error")
        if (_testnext(',' as Int)) {  /* assignment -> `,' primaryexp assignment */
            nv: LHS_assign
            nv prev = lh&
            primaryexp(nv v&)
            if (nv v k != ExpKind VINDEXED)
                _check_conflict(lh&, nv v&)
            assignment(nv&, nvars+1)
        }
        else {  /* assignment -> `=' explist1 */
            _checknext('=' as Int)
            nexps := explist1(e&)
            if (nexps != nvars) {
                _adjust_assign(nvars, nexps, e&)
                if (nexps > nvars)
                    fs freereg -= nexps - nvars  /* remove extra values */
            }
            else {
                fs luaK_setoneret(e&)  /* close last expression */
                fs luaK_storevar(lh v&, e&)
                return  /* avoid default */
            }
        }
        init_exp(e&, ExpKind VNONRELOC, fs freereg - 1)  /* default assignment */
        fs luaK_storevar(lh v&, e&)
    }


    cond: func -> Int {
        /* cond -> exp */
        v: ExpDesc
        expr(v&)  /* read condition */
        if (v k == ExpKind VNIL)
            v k = ExpKind VFALSE  /* `falses' are all equal here */
        fs luaK_goiftrue(v&)
        return v f
    }


    breakstat: func {
        bl := fs bl
        upval := false
        while (bl) {
            if (bl@ isbreakable)
                break
            upval |= bl@ upval
            bl = bl@ previous
        }
        if (! bl)
            syntaxError("no loop to break")
        if (upval)
            fs luaK_codeABC(OpCode OP_CLOSE, bl@ nactvar, 0, 0)
        fs luaK_concat(bl@ breaklist&, fs luaK_jump())
    }


    whilestat: func(line: Int) {
        /* whilestat -> WHILE cond DO block END */
        bl: BlockCnt
        next()  /* skip WHILE */
        whileinit := fs luaK_getlabel()
        condexit := cond()
        fs enterblock(bl&, true)
        _checknext(TK_DO)
        block()
        fs luaK_patchlist(fs luaK_jump(), whileinit)
        _check_match(TK_END, TK_WHILE, line)
        fs leaveblock()
        fs luaK_patchtohere(condexit)  /* false conditions finish the loop */
    }


    repeatstat: func(line: Int) {
        /* repeatstat -> REPEAT block UNTIL cond */
        repeat_init := fs luaK_getlabel()
        bl1, bl2: BlockCnt
        fs enterblock(bl1&, true);  /* loop block */
        fs enterblock(bl2&, false);  /* scope block */
        next()  /* skip REPEAT */
        chunk()
        _check_match(TK_UNTIL, TK_REPEAT, line)
        condexit := cond()  /* read condition (inside scope block) */
        if (!bl2 upval) {  /* no upvalues? */
            fs leaveblock()  /* finish scope */
            fs luaK_patchlist(condexit, repeat_init)  /* close the loop */
        }
        else {  /* complete semantics when there are upvalues */
            breakstat()  /* if condition then break */
            fs luaK_patchtohere(condexit)  /* else... */
            fs leaveblock()  /* finish scope... */
            fs luaK_patchlist(fs luaK_jump(), repeat_init)  /* and repeat */
        }
        fs leaveblock()  /* finish loop */
    }


    exp1: func {
        e: ExpDesc
        expr(e&)
        fs luaK_exp2nextreg(e&)
        version(debug) {
            assert(e k == ExpKind VNONRELOC)
        }
        return e info
    }


    forbody: func(base, line, nvars: Int, isnum: Bool) {
        /* forbody -> DO block */
        bl: BlockCnt
        _adjustlocalvars(3)  /* control variables */
        _checknext(TK_DO)
        prep := isnum ? fs luaK_codeABx(OpCode OP_FORPREP, base, NO_JUMP + MAXARG_sBx) : fs luaK_jump()
        fs enterblock(bl&, false)  /* scope for declared variables */
        _adjustlocalvars(nvars)
        fs luaK_reserveregs(nvars)
        block()
        fs leaveblock()  /* end of scope for declared variables */
        fs luaK_patchtohere(prep)
        endfor: Int
        if (isnum)  /* numeric for? */
            endfor = fs luaK_codeABx(OpCode OP_FORLOOP, base, NO_JUMP + MAXARG_sBx);
        else {  /* generic for */
            fs luaK_codeABC(OpCode OP_TFORCALL, base, 0, nvars)
            fs luaK_fixline(line)
            endfor = fs luaK_codeABx(OpCode OP_TFORLOOP, base + 2, NO_JUMP + MAXARG_sBx);
        }
        fs luaK_patchlist(endfor, prep + 1)
        fs luaK_fixline(line)
    }


    fornum: func(varname: String, line: Int) {
        /* fornum -> NAME = exp1,exp1[,exp1] forbody */
        base := fs freereg
        _new_localvarliteral("(for index)")
        _new_localvarliteral("(for limit)")
        _new_localvarliteral("(for step)")
        _new_localvar(varname)
        _checknext('=' as Int)
        exp1()  /* initial value */
        _checknext(',' as Int)
        exp1()  /* limit */
        if (_testnext(',' as Int))
            exp1()  /* optional step */
        else {  /* default step = 1 */
            fs luaK_codeABxX(OpCode OP_LOADK, fs freereg, fs luaK_numberK(1))
            fs luaK_reserveregs(1)
        }
        forbody(base, line, 1, true)
    }


    forlist: func(indexname: String) {
        /* forlist -> NAME {,NAME} IN explist1 forbody */
        nvars := 4  /* gen, state, control, plus at least one declared var */
        base := fs freereg
        /* create control variables */
        _new_localvarliteral("(for generator)")
        _new_localvarliteral("(for state)")
        _new_localvarliteral("(for control)")
        /* create declared variables */
        _new_localvar(indexname)
        while (_testnext(',' as Int)) {
            _new_localvar(_str_checkname())
            nvars += 1
        }
        _checknext(TK_IN)
        line := linenumber
        e: ExpDesc
        _adjust_assign(3, explist1(e&), e&)
        fs luaK_checkstack(3)  /* extra space to call generator */
        forbody(base, line, nvars - 3, false)
   }


    forstat: func(line: Int) {
        /* forstat -> FOR (fornum | forlist) END */
        bl: BlockCnt
        fs enterblock(bl&, true)  /* scope for loop and control variables */
        next()  /* skip `for' */
        varname := _str_checkname()  /* first variable name */
        match (t token) {
            case '=' =>
                fornum(varname, line)
            case ',' =>
                forlist(varname)
            case TK_IN =>
                forlist(varname)
            case =>
                syntaxError("'=' or 'in' expected")
        }
        _check_match(TK_END, TK_FOR, line)
        fs leaveblock()  /* loop scope (`break' jumps to this point) */
    }


    test_then_block: func -> Int {
        /* test_then_block -> [IF | ELSEIF] cond THEN block */
        next()  /* skip IF or ELSEIF */
        condexit := cond()
        _checknext(TK_THEN)
        block()  /* `then' part */
        return condexit
    }


    ifstat: func(line: Int) {
        /* ifstat -> IF cond THEN block {ELSEIF cond THEN block} [ELSE block] END */
        escapelist := NO_JUMP
        flist := test_then_block()  /* IF cond THEN block */
        while (t token == TK_ELSEIF) {
            fs luaK_concat(escapelist&, fs luaK_jump())
            fs luaK_patchtohere(flist)
            flist = test_then_block()  /* ELSEIF cond THEN block */
        }
        if (t token == TK_ELSE) {
            fs luaK_concat(escapelist&, fs luaK_jump())
            fs luaK_patchtohere(flist)
            next()  /* skip ELSE (after patch, for correct line info) */
            block()  /* `else' part */
        }
        else
            fs luaK_concat(escapelist&, flist)
        fs luaK_patchtohere(escapelist)
        _check_match(TK_END, TK_IF, line)
    }


    localfunc: func {
        v, b: ExpDesc
        _new_localvar(_str_checkname())
        init_exp(v&, ExpKind VLOCAL, fs freereg)
        fs luaK_reserveregs(1)
        _adjustlocalvars(1)
        body(b&, false, linenumber)
        fs luaK_storevar(v&, b&)
    }


    localstat: func {
        /* stat -> LOCAL NAME {`,' NAME} [`=' explist1] */
        nvars := 0
        nexps: Int
        e: ExpDesc
        while (true) {
            _new_localvar(_str_checkname())
            nvars += 1
            if (! _testnext(',' as Int))
                break
        }
        if (_testnext('=' as Int))
            nexps = explist1(e&)
        else {
            e k = ExpKind VVOID
            nexps = 0
        }
        _adjust_assign(nvars, nexps, e&)
        _adjustlocalvars(nvars)
    }


    funcname: func(v: ExpDesc@) -> Bool {
        /* funcname -> NAME {fieldsel} [`:' NAME] */
        needself := false
        _singlevar(v&)
        while (t token == '.')
            fieldsel(v&)
        if (t token == ':') {
            needself = true
            fieldsel(v&)
        }
        return needself
    }

    funcstat: func(line: Int) {
        /* funcstat -> FUNCTION funcname body */
        v, b: ExpDesc
        next()  /* skip FUNCTION */
        needself := funcname(v&)
        body(b&, needself, line)
        fs luaK_storevar(v&, b&)
        fs luaK_fixline(line)  /* definition `happens' in the first line */
    }


    exprstat: func {
        /* stat -> func | assignment */
        v: LHS_assign
        primaryexp(v v&)
        if (v v k == ExpKind VCALL) { /* stat -> func */
            pi := fs f code data as Instruction* + v v info
            pi@ = pi@ setarg_C(1)  /* call statement uses no results */
        }
        else {  /* stat -> assignment */
            v prev = null
            assignment(v&, 1)
        }
    }


    retstat: func {
        /* stat -> RETURN explist */
        e: ExpDesc
        first, nret: Int  /* registers with returned values */
        if (block_follow(t token) || t token == ';') {
            first = 0
            nret = 0  /* return no values */
        }
        else {
            nret = explist1(e&)  /* optional return values */
            if (e k hasmultret()) {
                fs luaK_setreturns(e&, LUA_MULTRET)
                if (e k == ExpKind VCALL && nret == 1) {  /* tail call? */
                    pi := fs f code data as Instruction* + e info
                    pi@ = pi@ setOpcode(OpCode OP_TAILCALL)
                    version(debug) {
                        assert(pi@ getarg_A() == fs nactvar)
                    }
                }
                first = fs nactvar
                nret = LUA_MULTRET  /* return all values */
            }
            else {
                if (nret == 1)  /* only one single value? */
                    first = fs luaK_exp2anyreg(e&)
                else {
                    fs luaK_exp2nextreg(e&)  /* values must go to the `stack' */
                    first = fs nactvar  /* return all `active' values */
                    version(debug) {
                        assert(nret == fs freereg - first)
                    }
                }
            }
        }
        fs luaK_ret(first, nret)
    }


    statement: func -> Bool {
        line := linenumber  /* may be needed for error messages */
        match (t token) {
            case ';' =>  /* stat -> ';' (empty statement) */
                next()  /* skip ';' */
                return false
            case TK_IF =>  /* stat -> ifstat */
                ifstat(line)
                return false
            case TK_WHILE =>  /* stat -> whilestat */
                whilestat(line)
                return false
            case TK_DO =>  /* stat -> DO block END */
                next()  /* skip DO */
                block()
                _check_match(TK_END, TK_DO, line)
                return false
            case TK_FOR =>  /* stat -> forstat */
                forstat(line)
                return false
            case TK_REPEAT =>  /* stat -> repeatstat */
                repeatstat(line)
                return false
            case TK_FUNCTION =>  /* stat -> funcstat */
                funcstat(line)
                return false
            case TK_LOCAL =>  /* stat -> localstat */
                next()  /* skip LOCAL */
                if (_testnext(TK_FUNCTION))  /* local function? */
                    localfunc()
                else
                    localstat()
                return false
            case TK_RETURN =>  /* stat -> retstat */
                next()  /* skip RETURN */
                retstat()
                return true  /* must be last statement */
            case TK_BREAK =>  /* stat -> breakstat */
                next()  /* skip BREAK */
                breakstat()
                return true  /* must be last statement */
            case =>  /* stat -> func | assignment */
                exprstat()
                return false
        }
        return false
    }


    chunk: func {
        /* chunk -> { stat [`;'] } */
        last := false
        _enterlevel()
        while (!last && !block_follow(t token)) {
            last = statement()
            if (last)
                _testnext(';' as Int)
            version(debug) {
                assert(fs f maxstacksize >= fs freereg)
                assert(fs freereg >= fs nactvar)
            }
            fs freereg = fs nactvar
        }
        _leavelevel()
    }


    _testnext: func(c: Int) -> Bool {
        if (t token == c) {
            next()
            return true
        }
        else
            return false
    }

    _check: func(c: Int) {
        if (t token != c)
            _error_expected(c)
    }

    _checknext: func(c: Int) {
        _check(c)
        next()
    }

    _check_condition: func(c: Bool, msg: String) {
        if (! c)
            syntaxError(msg)
    }

    _check_match: func(what, who, where: Int) {
        if (! _testnext(what)) {
            if (where == linenumber)
                _error_expected(what)
            else
                syntaxError("%s expected (to close %s at line %d)" format(
                    token2str(what),
                    token2str(who),
                    where
                ))
        }
    }

    _str_checkname: func -> String {
        _check(TK_NAME)
        ts := t str
        next()
        return ts
    }

    _codestring: func(e: ExpDesc@, s: String) {
        init_exp(e&, ExpKind VK, fs luaK_stringK(s))
    }

    _checkname: func(e: ExpDesc@) {
        _codestring(e&, _str_checkname())
    }

    _registerlocalvar: func(varname: String) -> Int {
        locvars := fs f locvars
        idx := locvars getSize()
        locvars add(LocVar new(varname))
        return idx
    }


    _new_localvar: func(name: String) {
        reg := _registerlocalvar(name)
        fs checklimit(actvar getSize() + 1 - fs firstlocal, MAXVARS, "local variables")
        actvar add(reg)
    }


    _new_localvarliteral: func(name: String) {
        _new_localvar(name)
    }


    _adjustlocalvars: func(nvars: Int) {
        fs nactvar += nvars
        while (nvars) {
            pvar := fs getlocvar(fs nactvar - nvars)
            pvar@ startpc = fs f code getSize()
            nvars -= 1
        }
    }


    _singlevar: func(var: ExpDesc@) {
        varname := _str_checkname()
        if (fs singlevaraux(varname, var&, 1) == ExpKind VVOID) {  /* global name? */
            key: ExpDesc
            fs singlevaraux(envn, var&, 1)  /* get environment variable */
            version(debug) {
                assert(var k == ExpKind VLOCAL || var k == ExpKind VUPVAL)
            }
            _codestring(key&, varname)  /* key is variable name */
            fs luaK_indexed(var&, key&)  /* env[varname] */
        }
    }


    _adjust_assign: func(nvars, nexps: Int, e: ExpDesc@) {
        extra := nvars - nexps
        if (e k hasmultret()) {
            extra += 1  /* includes call itself */
            if (extra < 0)
                extra = 0
            fs luaK_setreturns(e&, extra)  /* last exp. provides the difference */
            if (extra > 1)
                fs luaK_reserveregs(extra-1)
        }
        else {
            if (e k != ExpKind VVOID)
                fs luaK_exp2nextreg(e&)  /* close last expression */
            if (extra > 0) {
                reg := fs freereg
                fs luaK_reserveregs(extra)
                fs luaK_nil(reg, extra)
            }
        }
    }


    _enterlevel: func {
    }


    _leavelevel: func {
    }


/*
** adds prototype being created into its parent list of prototypes
** and codes instruction to create new closure
*/
    _codeclosure: func(clp: LuaProto, v: ExpDesc@) {
        f := fs prev f  /* prototype of function creating new closure */
        np := f p getSize()
        f p add(clp)
        init_exp(v&, ExpKind VRELOCABLE, fs prev luaK_codeABx(OpCode OP_CLOSURE, 0, np))
    }


/*
** opens the main function, which is a regular vararg function with an
** upvalue named LUA_ENV
*/
    _mainfunc: func {
        fs = FuncState new(this, null as FuncState)
        fs f is_vararg = true  /* main function is always vararg */
        v: ExpDesc
        init_exp(v&, ExpKind VLOCAL, 0)
        fs newupvalue(envn, v&)  /* create environment upvalue */
    }


    _error_expected: func(c: Int) {
        syntaxError("%s expected" format(token2str(c)))
    }

}

PRIORITY_LEFT := const [
    6, 6, 7, 7, 7,  /* `+' `-' `*' `/' `%' */
    10, 5,          /* ^, .. (right associative) */
    3, 3, 3,        /* ==, <, <= */
    3, 3, 3,        /* ~=, >, >= */
    2, 1            /* and, or */
]

PRIORITY_RIGHT := const [
    6, 6, 7, 7, 7,  /* `+' `-' `*' `/' `%' */
    9, 4,           /* ^, .. (right associative) */
    3, 3, 3,        /* ==, <, <= */
    3, 3, 3,        /* ~=, >, >= */
    2, 1            /* and, or */
]

UNARY_PRIORITY := const 8  /* priority for unary operators */


/*
** Marks the end of a patch list. It is an invalid value both as an absolute
** address, and as a list link (would link an element to itself).
*/
NO_JUMP := const -1


/*
** grep "ORDER OPR" if you change these enums  (ORDER OP)
*/
BinOpr: enum {
    OPR_ADD, OPR_SUB, OPR_MUL, OPR_DIV, OPR_MOD, OPR_POW,
    OPR_CONCAT,
    OPR_EQ, OPR_LT, OPR_LE,
    OPR_NE, OPR_GT, OPR_GE,
    OPR_AND, OPR_OR,
    OPR_NOBINOPR
}


UnOpr: enum {
    OPR_MINUS,
    OPR_NOT,
    OPR_LEN,
    OPR_NOUNOPR
}

/* maximum number of local variables per function (must be smaller
   than 250, due to the bytecode format) */
MAXVARS := const 200

/* option for multiple returns in 'lua_pcall' and 'lua_call' */
LUA_MULTRET := const -1


/* maximum stack for a Lua function */
MAXSTACK := const 250

MAX_INT := const INT_MAX-2  /* maximum value of an int (-2 for safety) */

/*
** maximum depth for nested C calls and syntactical nested non-terminals
** in a program. (Value must fit in an unsigned short int.)
*/
LUAI_MAXCCALLS := const 200

/*
** maximum number of upvalues in a closure (both C and Lua). (Value
** must fit in an unsigned char.)
*/
MAXUPVAL := const 255 // UCHAR_MAX
