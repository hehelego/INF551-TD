let of_string s = Parser.expr Lexer.token (Lexing.from_string s)
let to_string : Expr.expr -> string = Expr.show_expr
