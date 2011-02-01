
import io/Reader
import structs/ArrayList
import structs/HashMap

LUA_MINBUFFER := const 32

Token: cover {
    token: Int
    str: String
    num: Double
}

Lexer: class {
    current: Int  /* current character (charint) */
    linenumber: Int  /* input line counter */
    lastline: Int  /* line of last token `consumed' */
    t: Token  /* current token */
    lookahead: Token  /* look ahead token */
    z: Reader  /* input stream */
    buff: ArrayList<Char>  /* buffer for tokens */
    source: String  /* current source name */
    envn: String  /* environment variable name */

    init: func {}

    setInput: func(=z, =source) {
        lookahead token = TK_EOS  /* no look-ahead token */
        linenumber = 1
        lastline = 1
        envn = "_ENV"
        buff = ArrayList<Char> new(LUA_MINBUFFER)  /* initialize buffer */
        _next()  /* read first char */
    }

    next: func {
        lastline = linenumber
        if (lookahead token != TK_EOS) {  /* is there a look-ahead token? */
            t = lookahead  /* use this one */
            lookahead token = TK_EOS  /* and discharge it */
        }
        else
            t token = _lex(t&)  /* read next token */
    }

    lookahead: func -> Int {
        version(debug) {
            assert(lookahead token == TK_EOS)
        }
        lookahead token = _lex(lookahead&)
        return lookahead token
    }

    shebang: func {
        if (current == '#') {
            while (current != '\n')
                _next()
            _incLineNumber()
        }
    }

    syntaxError: func(msg: String) {
        _error(msg, t token)
    }

    _error: func(message: String, token: Int) {
        msg := "%s:%d: %s" format(source, linenumber, message)
        if (token)
            msg += " near " + _txtToken(token)
        Exception new(This, msg) throw()
    }

    _txtToken: func(token: Int) -> String {
        if (token == TK_NAME || token == TK_STRING || token == TK_NUMBER) {
            s := String new(buff data as CString, buff getSize())
            return "'%s'" format(s)
        }
        else
            return token2str(token)
    }

    token2str: func(token: Int) -> String {
        if (token < FIRST_RESERVED) {
            if (token as Char printable?())
                return "'%c'" format(token)
            else
                return "char(%d)" format(token)
        }
        else
            match (token) {
                case TK_AND     => return "and"
                case TK_BREAK   => return "break"
                case TK_DO      => return "do"
                case TK_ELSE    => return "else"
                case TK_ELSEIF  => return "elseif"
                case TK_END     => return "end"
                case TK_FALSE   => return "false"
                case TK_FOR     => return "for"
                case TK_FUNCTION=> return "function"
                case TK_IF      => return "if"
                case TK_IN      => return "in"
                case TK_LOCAL   => return "local"
                case TK_NIL     => return "nil"
                case TK_NOT     => return "not"
                case TK_OR      => return "or"
                case TK_REPEAT  => return "repeat"
                case TK_RETURN  => return "return"
                case TK_THEN    => return "then"
                case TK_TRUE    => return "true"
                case TK_UNTIL   => return "until"
                case TK_WHILE   => return "while"
                // other terminal symbols
                case TK_CONCAT  => return ".."
                case TK_DOTS    => return "..."
                case TK_EQ      => return "=="
                case TK_GE      => return ">="
                case TK_LE      => return "<="
                case TK_NE      => return "~="
            }
        return "???"
    }

    _lex: func(tok: Token@) -> Int {
        buff clear()
        while (true) {
            match current {
                case '\n' =>
                    _incLineNumber()
                case '\r' =>
                    _incLineNumber()
                case ' ' =>
                    _next()
                case '\f' =>
                    _next()
                case '\t' =>
                    _next()
                case '\v' =>
                    _next()
                case '-' => /* '-' or '--' (comment) */
                    _next()
                    if (current != '-')
                        return '-' as Int
                    /* else is a comment */
                    _next()
                    if (current == '[') {  /* long comment? */
                        sep := _skipSep()
                        buff clear()  /* `skip_sep' may dirty the buffer */
                        if (sep >= 0) {
                            _readLongString(null, sep)  /* skip long comment */
                            buff clear()  /* previous call may dirty the buff. */
                            continue
                        }
                    }
                    /* else short comment */
                    while (!(current == '\n' || current == '\r') && current != -1)
                        _next() /* skip until end of line (or end of file) */
                case '[' =>  /* long string or simply '[' */
                    sep := _skipSep()
                    if (sep >= 0) {
                        _readLongString(tok&, sep)
                       return TK_STRING
                    }
                    else if (sep == -1)
                        return '[' as Int
                    else
                        _error("invalid long string delimiter", TK_STRING)
                case '=' =>
                    _next()
                    if (current != '=')
                        return '=' as Int
                    else {
                        _next()
                        return TK_EQ
                    }
                case '<' =>
                    _next()
                    if (current != '=')
                        return '<' as Int
                    else {
                        _next()
                        return TK_LE
                    }
                case '>' =>
                    _next()
                    if (current != '=')
                        return '>' as Int
                    else {
                        _next()
                        return TK_GE
                    }
                case '~' =>
                    _next()
                    if (current != '=')
                        return '~' as Int
                    else {
                        _next()
                        return TK_NE
                    }
                case '"' =>  /* short literal strings */
                    _readString(current, tok&)
                    return TK_STRING
                case '\'' =>
                    _readString(current, tok&)
                    return TK_STRING
                case '.' =>  /* '.', '..', '...', or number */
                    buff add(current as Char)
                    _next()
                    if (_checkNext(".")) {
                        if (_checkNext("."))
                            return TK_DOTS;   /* '...' */
                        else
                            return TK_CONCAT;   /* '..' */
                    }
                    else if (! current as Char digit?())
                        return '.' as Int
                    else {
                        _readNumeral(tok&)
                        return TK_NUMBER
                    }
                case -1 =>
                    return TK_EOS
                case =>
                    if (current as Char digit?()) {
                        _readNumeral(tok&)
                        return TK_NUMBER
                    }
                    else if (current as Char alpha?() ||  /* identifier or reserved word? */
                             current == '_') {
                        buff add(current as Char)
                        _next()
                        while (current as Char alphaNumeric?() ||
                               current == '_') {
                            buff add(current as Char)
                            _next()
                        }
                        s := String new(buff data as CString, buff getSize())
                        if (keywords contains?(s))
                            return keywords get(s)
                        else {
                            tok str = s
                            return TK_NAME
                        }
                    }
                    else {  /* single-char tokens (+ - / ...) */
                        c := current
                        _next()
                        return c
                    }
            }
        }
        return 0 // avoid error
    }

    _next: func -> Int {
        current = z hasNext?() ? z read() as Int : -1
        if (current == 0 && ! z hasNext?())
            current = -1
        return current
    }

    _checkNext: func(set: String) -> Bool {
//        if (current == '\0' || ! set contains?(current as Char))
        if (! set contains?(current as Char))
            return false
        buff add(current as Char)
        _next()
        return true
    }

    _incLineNumber: func {
        old := current
        _next()
        if ((current == '\n' || current == '\r') && current != old)
            _next()
        linenumber += 1
    }

    _readString: func(delim: Int, tok: Token@) {
        buff add(current as Char)  /* keep delimiter (for error messages) */
        _next()
        while (current != delim) {
            match current {
                case -1 =>
                    _error("unfinished string", TK_EOS)
                case '\n' =>
                    _error("unfinished string", TK_STRING)
                case '\r' =>
                    _error("unfinished string", TK_STRING)
                case '\\' =>  /* escape sequences */
                    nextDone := false
                    c: Char  /* final character to be saved */
                    _next()  /* do not save the `\' */
                    match current {
                        case 'a' =>
                            c = '\a'
                        case 'b' =>
                            c = '\b'
                        case 'f' =>
                            c = '\f'
                        case 'n' =>
                            c = '\n'
                        case 'r' =>
                            c = '\r'
                        case 't' =>
                            c = '\t'
                        case 'v' =>
                            c = '\v'
                        case 'x' =>
                            c = _readHexaEsc()
                        case '\n' =>
                            buff add('\n')
                            _incLineNumber()
                            continue
                        case '\r' =>
                            buff add('\n')
                            _incLineNumber()
                            continue
                        case -1 =>
                            continue  /* will raise an error next loop */
                        case '*' =>  /* skip following span of spaces */
                            _next()  /* skip the '*' */
                            while (current as Char whitespace?()) {
                                if (current == '\n' || current == '\r')
                                    _incLineNumber()
                                else
                                    _next()
                            }
                            continue  /* do not save 'c' */
                        case =>
                            if (! current as Char digit?())
                                c = current as Char /* handles \\, \", \', and \? */
                            else { /* digital escape \ddd */
                                c = _readDecEsc(nextDone&)
                            }
                    }
                    buff add(c)
                    if (! nextDone)
                        _next()
                case =>
                    buff add(current as Char)
                    _next()
            }
        }
        buff add(current as Char)  /* skip delimiter */
       _next()
        tmp := buff slice(1, buff getSize() -2)
        tok str = String new(tmp data as CString, tmp getSize())
    }

    _readHexaEsc: func() -> Char {
        c1 := _next() as Char
        c2 := _next() as Char
        if (! c1 hexDigit?() || ! c2 hexDigit?()) {
            buff clear()
            buff add('\\')
            buff add('x')
            if (c1 == -1)
                buff add(c1)
            if (c2 == -1)
                buff add(c2)
            _error("hexadecimal digit expected", TK_STRING)
        }
        return (_hexaValue(c1) << 4) + _hexaValue(c2) as Char
    }

    _hexaValue: func(c: Char) -> Char {
        if (c digit?())
            return c - '0'
        else if (c upper?())
            return c - 'A' + 10
        else
            return c - 'a' + 10
    }

    _readDecEsc: func(nextDone: Bool@) -> Char {
        c1 := current as Char
        c := (c1 - '0') as Int
        c2 := _next() as Char
        if (c2 digit?()) {
            c = 10 * c + (c2 - '0') as Int
            c3 := _next() as Char
            if (c3 digit?()) {
                c = 10 * c + (c3 - '0') as Int
                if (c > 255) {
                    buff clear()
                    buff add('\\')
                    buff add(c1)
                    buff add(c2)
                    buff add(c3)
                    _error("decimal escape too large", TK_STRING)
                 }
                 return c as Char
            }
        }
        /* else, has read one character that was not a digit */
        nextDone = true
        return c as Char
    }

    _readNumeral: func(tok: Token@) {
        buff add(current as Char)
        _next()
        while (current as Char alphaNumeric?() || current == '.') {
            buff add(current as Char)
            _next()
            if (_checkNext("EePp"))  /* exponent part? */
                _checkNext("+-")  /* optional exponent sign */

        }
        buff add('\0')
        s1, s2: CString
        s1 = buff data as CString
        d := strtod(s1, s2&)
        if (s1 != s2 && s2[0] == '\0')
            tok num = d
        else {
            n := strtoul(s1, s2&, 0)
            if (s1 != s2 && s2[0] == '\0')
                tok num = n
            else
                _error("malformed number", TK_NUMBER)
        }
    }

    _skipSep: func -> Int {
        count := 0
        s := current
        buff add(current as Char)
        _next()
        while (current == '=') {
            buff add(current as Char)
            _next()
            count += 1
        }
        return (current == s) ? count : - 1
    }

    _readLongString: func(tok: Token@, sep: Int) {
        buff add(current as Char) /* skip 2nd `[' */
        _next()
        if (current == '\n' || current == '\r')  /* string starts with a newline? */
            _incLineNumber()  /* skip it */
        while (true) {
            match current {
                case -1 =>
                    _error(tok& ? "unfinished long string" :
                                  "unfinished long comment", TK_EOS)
                case ']' =>
                    if (_skipSep() == sep) {
                        buff add(current as Char) /* skip 2nd `]' */
                        _next()
                        break
                    }
                case '\n' =>
                    buff add('\n')
                    _incLineNumber()
                    if (! tok&)
                        buff clear()  /* avoid wasting space */
                case '\r' =>
                    buff add('\n')
                    _incLineNumber()
                    if (! tok&)
                        buff clear()  /* avoid wasting space */
                case =>
                    if (tok&)
                        buff add(current as Char)
                    _next()
            }
        }
        if (tok&) {
            tmp := buff slice(2 + sep, buff getSize() - 2*(2 + sep))
            tok str = String new(tmp data as CString, tmp getSize())
        }
    }
}

FIRST_RESERVED  := const 257

TK_AND      := const 257
TK_BREAK    := const 258
TK_DO       := const 259
TK_ELSE     := const 260
TK_ELSEIF   := const 261
TK_END      := const 262
TK_FALSE    := const 263
TK_FOR      := const 264
TK_FUNCTION := const 265
TK_IF       := const 266
TK_IN       := const 267
TK_LOCAL    := const 268
TK_NIL      := const 269
TK_NOT      := const 270
TK_OR       := const 271
TK_REPEAT   := const 272
TK_RETURN   := const 273
TK_THEN     := const 274
TK_TRUE     := const 275
TK_UNTIL    := const 276
TK_WHILE    := const 277
// other terminal symbols
TK_CONCAT   := const 278
TK_DOTS     := const 279
TK_EQ       := const 280
TK_GE       := const 281
TK_LE       := const 282
TK_NE       := const 283
TK_EOS      := const 284
TK_NUMBER   := const 285
TK_NAME     := const 286
TK_STRING   := const 287

keywords := HashMap<String, Int> new()
keywords put("and", TK_AND)
keywords put("break", TK_BREAK)
keywords put("do", TK_DO)
keywords put("else", TK_ELSE)
keywords put("elseif", TK_ELSEIF)
keywords put("end", TK_END)
keywords put("false", TK_FALSE)
keywords put("for", TK_FOR)
keywords put("function", TK_FUNCTION)
keywords put("if", TK_IF)
keywords put("in", TK_IN)
keywords put("local", TK_LOCAL)
keywords put("nil", TK_NIL)
keywords put("not", TK_NOT)
keywords put("or", TK_OR)
keywords put("repeat", TK_REPEAT)
keywords put("return", TK_RETURN)
keywords put("then", TK_THEN)
keywords put("true", TK_TRUE)
keywords put("until", TK_UNTIL)
keywords put("while", TK_WHILE)

