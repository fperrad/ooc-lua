
import io/FileReader
import io/FileWriter
import structs/ArrayList

import Types
import Parser
import Opcodes


main: func(args: ArrayList<String>) {
    n := args getSize()
    i := doargs(args)
    if (n == i)
        usage("no input files given")

    args = args slice(i .. n - 1)
    parser := Parser new()
    l := ArrayList<LuaProto> new()
    for (i in 0 .. args getSize())
        l add(parser loadfile(args get(i)))
    proto := combine(l)
    if (listing)
        proto printFunction(listing > 1)
    if (dumping) {
        writer := FileWriter new(output)
        proto dumpHeader(writer)
        proto dump(writer, stripping)
        writer close()
    }
}

progname := "ooc-luac"
output := "ooc-luac.out"
listing := 0
dumping := true
stripping := false

doargs: func(args: ArrayList<String>) -> Int {
    progname = args get(0)
    version := 0
    i := 1
    while (i < args getSize()) {
        arg := args get(i)
        if (! arg startsWith?("-"))     /* end of options; keep it */
            break
        else if (arg equals?("--")) {   /* end of options; skip it */
            i += 1
            if (version)
                version += 1
            break
        }
        else if (arg equals?("-"))      /* end of options; use stdin */
            break
        else if (arg equals?("-l"))     /* list */
            listing += 1
        else if (arg equals?("-o")) {   /* output file */
            i += 1
            output = args get(i) // TODO
        }
        else if (arg equals?("-p"))     /* parse only */
            dumping = false
        else if (arg equals?("-s"))     /* strip debug information */
            stripping = true
        else if (arg equals?("-v"))     /* show version */
            version += 1
        else                            /* unknown option */
            usage(arg)

        i += 1
    }
    if (version) {
        "Lua 5.2 / ooc" println()
        if (version + 1 == args getSize())
            exit(EXIT_SUCCESS)
    }
    return i
}

usage: func(message: String) {
    if (message startsWith?("-"))
        fprintf(stderr, "%s: unrecognized option '%s'\n" format(progname, message))
    else
        fprintf(stderr, "%s: %s\n" format(progname, message))
    msg := ("usage: %s [options] [filenames]\n" +
            "Available options are:\n" +
            "  -l       list\n" +
            "  -o name  output to file \"name\" (default is \"%s\")\n" +
            "  -p       parse only\n" +
            "  -s       strip debug information\n" +
            "  -v       show version information\n" +
            "  --       stop handling options\n" +
            "  -        stop handling options and process stdin\n") format(progname, "luac.out")
    fprintf(stderr, msg)
    exit(EXIT_FAILURE)
}

combine: func(l: ArrayList<LuaProto>) -> LuaProto {
    // TODO
    return l get(0)
}

extend Parser {
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
}

extend LuaProto {
    printFunction: func(full: Bool) {
        printHeader()
        printCode()
        if (full)
            printDebug()
        for (f in p)
            f printFunction(full)
    }

    printHeader: func {
        s := source ? source : "=?"
        if (s startsWith?("@") || s startsWith?("="))
            s = s substring(1)
        else if (s startsWith?("\x1b"))
            s = "(bstring)"
        else
            s = "(string)"
        sizecode := code getSize()
        "\n%s <%s:%d,%d> (%d instruction%s at %p)" format(
            (linedefined == 0) ? "main" : "function", s,
            linedefined, lastlinedefined,
            sizecode, (sizecode == 1) ? "": "s", this
        ) println()
        sizeupvalues := upvalues getSize()
        sizelocvars := locvars getSize()
        sizek := k getSize()
        sizep := p getSize()
        "%d%s param%s, %d slot%s, %d upvalue%s, %d local%s, %d constant%s, %d function%s" format(
            numparams, is_vararg ? "+" : "", (numparams == 1) ? "": "s",
            maxstacksize, (maxstacksize == 1) ? "": "s",
            sizeupvalues, (sizeupvalues == 1) ? "": "s",
            sizelocvars, (sizelocvars == 1) ? "": "s",
            sizek, (sizek == 1) ? "": "s",
            sizep, (sizep == 1) ? "": "s"
        ) println()
    }

    printCode: func {
        for (pc in 0 .. code getSize()) {
            "\t%d\t" format(pc + 1) print()
            line := lineinfo getSize() > pc ? lineinfo get(pc) : 0
            if (line > 0)
                "[%d]\t" format(line) print()
            else
                "[-]\t" print()
            i := code get(pc)
            o := i getOpcode()
            s := OP_NAMES[o]
            while (s length() < 9) s += " " // workaround
            "%-9s\t" format(s) print()
            a := i getarg_A()
            b := i getarg_B()
            c := i getarg_C()
            ax := i getarg_Ax()
            bx := i getarg_Bx()
            sbx := i getarg_sBx()
            match (o getOpMode()) {
                case OpMode iABC =>
                    "%d" format(a) print()
                    if (o getBMode() != OpArgMask OpArgN)
                        " %d" format(b & BITRK ? (-1 - (b & ~BITRK)) : b) print()
                    if (o getCMode() != OpArgMask OpArgN)
                        " %d" format(c & BITRK ? (-1 - (c & ~BITRK)) : c) print()
                case OpMode iABx =>
                    if (o getBMode() == OpArgMask OpArgK)
                        "%d %d" format(a, -bx) print()
                    else
                        "%d %d" format(a, bx) print()
                case OpMode iAsBx =>
                    if (o == OpCode OP_JMP)
                        "%d" format(sbx) print()
                    else
                        "%d %d" format(a,sbx) print()
                case OpMode iAx =>
                    "%d" format(-1 - ax) print()
            }
            match {
                case o == OpCode OP_LOADK =>
                    if (bx>0) {
                        "\t; " print()
                        printConstant(bx - 1)
                    }
                case o == OpCode OP_GETUPVAL ||
                     o == OpCode OP_SETUPVAL =>
                    "\t; " print()
                    upvalues get(b) name print()
                case o == OpCode OP_GETTABUP =>
                    "\t; " print()
                    upvalues get(b) name print()
                    if (c & BITRK) {
                        " " print()
                        printConstant(c & ~BITRK)
                    }
                case o == OpCode OP_SETTABUP =>
                    "\t; " print()
                    upvalues get(a) name print()
                    if (b & BITRK) {
                        " " print()
                        printConstant(b & ~BITRK)
                    }
                    if (c & BITRK) {
                        " " print()
                        printConstant(c & ~BITRK)
                    }
                case o == OpCode OP_GETTABLE ||
                     o == OpCode OP_SELF =>
                    if (c & BITRK) {
                        "\t; " print()
                        printConstant(c & ~BITRK)
                    }
                case o == OpCode OP_SETTABLE ||
                     o == OpCode OP_ADD ||
                     o == OpCode OP_SUB ||
                     o == OpCode OP_MUL ||
                     o == OpCode OP_DIV ||
                     o == OpCode OP_POW ||
                     o == OpCode OP_EQ ||
                     o == OpCode OP_LT ||
                     o == OpCode OP_LE =>
                    if (b & BITRK || c & BITRK) {
                        "\t; " print()
                        if (b & BITRK)
                            printConstant(b & ~BITRK)
                        else
                            "-" print()
                        " " print()
                        if (c & BITRK)
                            printConstant(c & ~BITRK)
                        else
                            "-" print()
                    }
                case o == OpCode OP_JMP ||
                     o == OpCode OP_FORLOOP ||
                     o == OpCode OP_FORPREP ||
                     o == OpCode OP_TFORLOOP =>
                    "\t; to %d" format(sbx + pc + 2) print()
                case o == OpCode OP_CLOSURE =>
                    "\t; %p" format(p get(bx)) print()
                case o == OpCode OP_SETLIST =>
                    if (c == 0) {
                        pc += 1
                        "\t; %d" format(code get(pc)) print()
                    }
                    else
                        "\t; %d" format(c) print()
                case o == OpCode OP_EXTRAARG =>
                    "\t; " print()
                    printConstant(ax)
            }
            "\n" print()
        }
    }

    printConstant: func(idx: Int) {
        cst := k get(idx)
        match (cst class) {
            case LuaNil =>
                "nil" print()
            case LuaBoolean =>
                cst as LuaBoolean v toString() print()
            case LuaNumber =>
                buff := CString new(20)
                n := sprintf(buff, "%.14g", cst as LuaNumber v)
                String new(buff, n) print()
            case LuaString =>
                str := cst as LuaString v
                "\"" print()
                for (c in str)
                    match (c) {
                        case '"' =>
                            "\\\"" print()
                        case '\\' =>
                            "\\\\" print()
                        case '\a' =>
                            "\\a" print()
                        case '\b' =>
                            "\\b" print()
                        case '\f' =>
                            "\\f" print()
                        case '\n' =>
                            "\\n" print()
                        case '\r' =>
                            "\\r" print()
                        case '\t' =>
                            "\\t" print()
                        case '\v' =>
                            "\\v" print()
                        case =>
                            if (c printable?())
                                c print()
                            else
                                "\\%03d" format(c) print()
                    }
                "\"" print()
        }
    }

    printDebug: func {
        sizek := k getSize()
        "constants (%d) for %p:" format(sizek, k data) println()
        for (i in 0 .. sizek) {
            "\t%d\t" format(i + 1) print()
            printConstant(i)
            "\n" print()
        }
        sizelocvars := locvars getSize()
        "locals (%d) for %p:" format(sizelocvars, locvars data) println()
        for (i in 0 .. sizelocvars) {
            var := locvars get(i)
            "\t%d\t%s\t%d\t%d" format(i, var varname, var startpc + 1, var endpc + 1) println()
        }
        sizeupvalues := upvalues getSize()
        "upvalues (%d) for %p:" format(sizeupvalues, upvalues data) println()
        for (i in 0 .. sizeupvalues) {
            upv := upvalues get(i)
            "\t%d\t%s\t%d\t%d" format(i, upv name, upv instack, upv idx) println()
        }
    }
}

