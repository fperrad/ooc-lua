
import io/FileReader
import structs/ArrayList

import Lexer

extend Lexer {
    printToken: func {
        if (t token != TK_EOS)
            "%d %s" format(t token, _txtToken(t token)) println()
        else
            "EOF" println()
    }
}

main: func(args: ArrayList<String>) {
    progname := args removeAt(0)

    lexer := Lexer new()
    if (args getSize() > 0) {
        fname := args removeAt(0)
        lexer setInput(FileReader new(fname), fname)
    }
    else
        exit(0)
//        lexer setInput(FileReader new(stdin), "=stdin")

    lexer shebang()
    lexer next()
    lexer printToken()
    while (lexer t token != TK_EOS) {
        lexer next()
        lexer printToken()
    }
}
