
include stdint


/*===========================================================================
  We assume that instructions are unsigned numbers.
  All instructions have an opcode in the first 6 bits.
  Instructions can have the following fields:
        `A' : 8 bits
        `B' : 9 bits
        `C' : 9 bits
        'Ax' : 26 bits ('A', 'B', and 'C' together)
        `Bx' : 18 bits (`B' and `C' together)
        `sBx' : signed Bx

  A signed argument is represented in excess K; that is, the number
  value is the unsigned value minus K. K is exactly the maximum value
  for that argument (so that -max is represented by 0, and +max is
  represented by 2*max), which is half the maximum for the corresponding
  unsigned argument.
===========================================================================*/


OpMode: enum {  /* basic instruction format */
    iABC,
    iABx,
    iAsBx,
    iAx
}


/*
** size and position of opcode arguments.
*/
SIZE_C  := const        9
SIZE_B  := const        9
SIZE_Bx := const        SIZE_C + SIZE_B
SIZE_A  := const        8
SIZE_Ax := const        SIZE_C + SIZE_B + SIZE_A

SIZE_OP := const        6

POS_OP  := const        0
POS_A   := const        POS_OP + SIZE_OP
POS_C   := const        POS_A + SIZE_A
POS_B   := const        POS_C + SIZE_C
POS_Bx  := const        POS_C
POS_Ax  := const        POS_A


/*
** limits for opcode arguments.
** we use (signed) int to manipulate most arguments,
** so they must fit in LUAI_BITSINT-1 bits (-1 for sign)
*/
MAXARG_Bx   := const    (1 << SIZE_Bx) - 1
MAXARG_sBx  := const    MAXARG_Bx >> 1         /* `sBx' is signed */
MAXARG_Ax   := const    (1 << SIZE_Ax) - 1
MAXARG_A    := const    (1 << SIZE_A) - 1
MAXARG_B    := const    (1 << SIZE_B) - 1
MAXARG_C    := const    (1 << SIZE_C) - 1


Instruction: cover from uint32_t {
    createABC: static inline func(o: OpCode, a, b, c: UInt) -> This {
        return (o as UInt << POS_OP | a << POS_A | b << POS_B | c << POS_C) as Instruction
    }

    createABx: static inline func(o: OpCode, a, bc: UInt) -> This {
        return (o as UInt << POS_OP | a << POS_A | bc << POS_Bx) as Instruction
    }

    createAx: static inline func(o: OpCode, a: UInt) -> This {
        return (o as UInt << POS_OP | a << POS_Ax) as Instruction
    }

    getOpcode: inline func -> OpCode {
        return ((this >> POS_OP) & ~(~0 << SIZE_OP)) as OpCode
    }

    setOpcode: inline func(o: OpCode) -> Instruction {
        return (this & ~(~(~0 << SIZE_OP) << POS_OP)) | ((o << POS_OP) & (~(~0 << SIZE_OP)) << POS_OP)
    }

    getarg_A: inline func -> Int {
        return ((this >> POS_A) & ~(~0 << SIZE_A)) as Int
    }

    setarg_A: inline func(a: UInt) -> Instruction {
        return (this & ~(~(~0 << SIZE_A) << POS_A)) | ((a << POS_A) & (~(~0 << SIZE_A)) << POS_A)
    }

    getarg_B: inline func -> Int {
        return ((this >> POS_B) & ~(~0 << SIZE_B)) as Int
    }

    setarg_B: inline func(b: UInt) -> Instruction {
        return (this & ~(~(~0 << SIZE_B) << POS_B)) | ((b << POS_B) & (~(~0 << SIZE_B)) << POS_B)
    }

    getarg_C: inline func -> Int {
        return ((this >> POS_C) & ~(~0 << SIZE_C)) as Int
    }

    setarg_C: inline func(c: UInt) -> Instruction {
        return (this & ~(~(~0 << SIZE_C) << POS_C)) | ((c << POS_C) & (~(~0 << SIZE_C)) << POS_C)
    }

    getarg_Bx: inline func -> Int {
        return ((this >> POS_Bx) & ~(~0 << SIZE_Bx)) as Int
    }

    setarg_Bx: inline func(b: UInt) -> Instruction {
        return (this & ~(~(~0 << SIZE_Bx) << POS_Bx)) | ((b << POS_Bx) & (~(~0 << SIZE_Bx)) << POS_Bx)
    }

    getarg_Ax: inline func -> Int {
        return ((this >> POS_Ax) & ~(~0 << SIZE_Ax)) as Int
    }

    setarg_Ax: inline func(a: UInt) -> Instruction {
        return (this & ~(~(~0 << SIZE_Ax) << POS_Ax)) | ((a << POS_Ax) & (~(~0 << SIZE_Ax)) << POS_Ax)
    }

    getarg_sBx: inline func -> Int {
        return (((this >> POS_Bx) & ~(~0 << SIZE_Bx)) - MAXARG_sBx) as Int
    }

    setarg_sBx: inline func(b: Int) -> Instruction {
        return (this & ~(~(~0 << SIZE_Bx) << POS_Bx)) | (((b + MAXARG_sBx) << POS_Bx) & (~(~0 << SIZE_Bx)) << POS_Bx)
    }
}


/* this bit 1 means constant (0 means register) */
BITRK   := const        1 << (SIZE_B - 1)
MAXINDEXRK := const     BITRK - 1


/*
** invalid register that fits in 8 bits
*/
NO_REG  := const        MAXARG_A


/*
** R(x) - register
** Kst(x) - constant (in constant table)
** RK(x) == if ISK(x) then Kst(INDEXK(x)) else R(x)
*/

/*
** grep "ORDER OP" if you change these enums
*/

OpCode: enum {
    /*----------------------------------------------------------------------
    name            args    description
    ------------------------------------------------------------------------*/
    OP_MOVE,/*      A B     R(A) := R(B)                                    */
    OP_LOADK,/*     A Bx    R(A) := Kst(Bx - 1)                             */
    OP_LOADBOOL,/*  A B C   R(A) := (Bool)B; if (C) pc++                    */
    OP_LOADNIL,/*   A B     R(A) := ... := R(B) := nil                      */
    OP_GETUPVAL,/*  A B     R(A) := UpValue[B]                              */

    OP_GETTABUP,/*  A B C   R(A) := UpValue[B][RK(C)]                       */
    OP_GETTABLE,/*  A B C   R(A) := R(B)[RK(C)]                             */

    OP_SETTABUP,/*  A B C   UpValue[A][RK(B)] := RK(C)                      */
    OP_SETUPVAL,/*  A B     UpValue[B] := R(A)                              */
    OP_SETTABLE,/*  A B C   R(A)[RK(B)] := RK(C)                            */

    OP_NEWTABLE,/*  A B C   R(A) := {} (size = B,C)                         */

    OP_SELF,/*      A B C   R(A+1) := R(B); R(A) := R(B)[RK(C)]             */

    OP_ADD,/*       A B C   R(A) := RK(B) + RK(C)                           */
    OP_SUB,/*       A B C   R(A) := RK(B) - RK(C)                           */
    OP_MUL,/*       A B C   R(A) := RK(B) * RK(C)                           */
    OP_DIV,/*       A B C   R(A) := RK(B) / RK(C)                           */
    OP_MOD,/*       A B C   R(A) := RK(B) % RK(C)                           */
    OP_POW,/*       A B C   R(A) := RK(B) ^ RK(C)                           */
    OP_UNM,/*       A B     R(A) := -R(B)                                   */
    OP_NOT,/*       A B     R(A) := not R(B)                                */
    OP_LEN,/*       A B     R(A) := length of R(B)                          */

    OP_CONCAT,/*    A B C   R(A) := R(B).. ... ..R(C)                       */

    OP_JMP,/*       sBx     pc+=sBx                                         */

    OP_EQ,/*        A B C   if ((RK(B) == RK(C)) ~= A) then pc++            */
    OP_LT,/*        A B C   if ((RK(B) <  RK(C)) ~= A) then pc++            */
    OP_LE,/*        A B C   if ((RK(B) <= RK(C)) ~= A) then pc++            */

    OP_TEST,/*      A C     if not (R(A) <=> C) then pc++                   */
    OP_TESTSET,/*   A B C   if (R(B) <=> C) then R(A) := R(B) else pc++     */

    OP_CALL,/*      A B C   R(A), ... ,R(A+C-2) := R(A)(R(A+1), ... ,R(A+B-1)) */
    OP_TAILCALL,/*  A B C   return R(A)(R(A+1), ... ,R(A+B-1))              */
    OP_RETURN,/*    A B     return R(A), ... ,R(A+B-2)      (see note)      */

    OP_FORLOOP,/*   A sBx   R(A)+=R(A+2);
                            if R(A) <?= R(A+1) then { pc+=sBx; R(A+3)=R(A) }*/
    OP_FORPREP,/*   A sBx   R(A)-=R(A+2); pc+=sBx                           */

    OP_TFORCALL,/*  A C     R(A+3), ... ,R(A+2+C) := R(A)(R(A+1), R(A+2));  */
    OP_TFORLOOP,/*  A sBx   if R(A+1) ~= nil then { R(A)=R(A+1); pc += sBx }*/

    OP_SETLIST,/*   A B C   R(A)[(C-1)*FPF+i] := R(A+i), 1 <= i <= B        */

    OP_CLOSE,/*     A       close all variables in the stack up to (>=) R(A)*/
    OP_CLOSURE,/*   A Bx    R(A) := closure(KPROTO[Bx])                     */

    OP_VARARG,/*    A B     R(A), R(A+1), ..., R(A+B-2) = vararg            */

    OP_EXTRAARG/*   Ax      extra (larger) argument for previous opcode     */

    getOpMode: inline func -> OpMode {
        return (OP_MODES[this] & 3) as OpMode
    }

    getBMode: inline func -> OpArgMask {
        return ((OP_MODES[this] >> 4) & 3) as OpArgMask
    }

    getCMode: inline func -> OpArgMask {
        return ((OP_MODES[this] >> 2) & 3) as OpArgMask
    }

    testAMode: inline func -> Bool {
        return (OP_MODES[this] & (1 << 6)) != 0
    }

    testTMode: inline func -> Bool {
        return (OP_MODES[this] & (1 << 7)) != 0
    }
}


OP_NAMES := const [
    "MOVE",
    "LOADK",
    "LOADBOOL",
    "LOADNIL",
    "GETUPVAL",
    "GETTABUP",
    "GETTABLE",
    "SETTABUP",
    "SETUPVAL",
    "SETTABLE",
    "NEWTABLE",
    "SELF",
    "ADD",
    "SUB",
    "MUL",
    "DIV",
    "MOD",
    "POW",
    "UNM",
    "NOT",
    "LEN",
    "CONCAT",
    "JMP",
    "EQ",
    "LT",
    "LE",
    "TEST",
    "TESTSET",
    "CALL",
    "TAILCALL",
    "RETURN",
    "FORLOOP",
    "FORPREP",
    "TFORCALL",
    "TFORLOOP",
    "SETLIST",
    "CLOSE",
    "CLOSURE",
    "VARARG",
    "EXTRAARG"
]

/*
** masks for instruction properties. The format is:
** bits 0-1: op mode
** bits 2-3: C arg mode
** bits 4-5: B arg mode
** bit 6: instruction set register A
** bit 7: operator is a test (next instruction must be a jump)
*/

OpArgMask: enum {
    OpArgN,  /* argument is not used */
    OpArgU,  /* argument is used */
    OpArgR,  /* argument is a register or a jump offset */
    OpArgK   /* argument is a constant or register/constant */
}

OP_MODES := const [
/*   T        A                  B                       C                   mode      opcode */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_MOVE */
    (0<<7) | (1<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgN<<2) | OpMode iABx,  /* OP_LOADK */
    (0<<7) | (1<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgU<<2) | OpMode iABC,  /* OP_LOADBOOL */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_LOADNIL */
    (0<<7) | (1<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_GETUPVAL */
    (0<<7) | (1<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_GETTABUP */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_GETTABLE */
    (0<<7) | (0<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_SETTABUP */
    (0<<7) | (0<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_SETUPVAL */
    (0<<7) | (0<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_SETTABLE */
    (0<<7) | (1<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgU<<2) | OpMode iABC,  /* OP_NEWTABLE */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_SELF */
    (0<<7) | (1<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_ADD */
    (0<<7) | (1<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_SUB */
    (0<<7) | (1<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_MUL */
    (0<<7) | (1<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_DIV */
    (0<<7) | (1<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_MOD */
    (0<<7) | (1<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_POW */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_UNM */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_NOT */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_LEN */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgR<<2) | OpMode iABC,  /* OP_CONCAT */
    (0<<7) | (0<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgN<<2) | OpMode iAsBx, /* OP_JMP */
    (1<<7) | (0<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_EQ */
    (1<<7) | (0<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_LT */
    (1<<7) | (0<<6) | (OpArgMask OpArgK<<4) | (OpArgMask OpArgK<<2) | OpMode iABC,  /* OP_LE */
    (1<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgU<<2) | OpMode iABC,  /* OP_TEST */
    (1<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgU<<2) | OpMode iABC,  /* OP_TESTSET */
    (0<<7) | (1<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgU<<2) | OpMode iABC,  /* OP_CALL */
    (0<<7) | (1<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgU<<2) | OpMode iABC,  /* OP_TAILCALL */
    (0<<7) | (0<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_RETURN */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgN<<2) | OpMode iAsBx, /* OP_FORLOOP */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgN<<2) | OpMode iAsBx, /* OP_FORPREP */
    (0<<7) | (0<<6) | (OpArgMask OpArgN<<4) | (OpArgMask OpArgU<<2) | OpMode iABC,  /* OP_TFORCALL */
    (0<<7) | (1<<6) | (OpArgMask OpArgR<<4) | (OpArgMask OpArgN<<2) | OpMode iAsBx, /* OP_TFORLOOP */
    (0<<7) | (0<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgU<<2) | OpMode iABC,  /* OP_SETLIST */
    (0<<7) | (0<<6) | (OpArgMask OpArgN<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_CLOSE */
    (0<<7) | (1<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgN<<2) | OpMode iABx,  /* OP_CLOSURE */
    (0<<7) | (1<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgN<<2) | OpMode iABC,  /* OP_VARARG */
    (0<<7) | (0<<6) | (OpArgMask OpArgU<<4) | (OpArgMask OpArgU<<2) | OpMode iAx,   /* OP_EXTRAARG */
]

/* number of list items to accumulate before a SETLIST instruction */
LFIELDS_PER_FLUSH := const 50

/* option for multiple returns in 'lua_pcall' and 'lua_call' */
LUA_MULTRET := const -1


/*
** converts an integer to a "floating point byte", represented as
** (eeeeexxx), where the real value is (1xxx) * 2^(eeeee - 1) if
** eeeee != 0 and (xxx) otherwise.
*/
int2fb: func(x: UInt32) -> Int {
    e := 0  /* exponent */
    if (x < 8)
        return x
    while (x >= 0x10) {
        x = (x+1) >> 1
        e += 1
    }
    return ((e+1) << 3) | (x as Int - 8)
}

/* converts back */
fb2int: func(x: Int) -> Int {
    e := (x >> 3) & 0x1f
    if (e == 0)
        return x
    else
        return ((x & 7) + 8) << (e - 1)
}

