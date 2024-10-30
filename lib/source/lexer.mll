
{
    open Program
    open Lexing
    exception UnexpectedChar of string
    exception UnterminatedComment 

    let current_loc = 
      let prev_pos = ref Reporting.Pos.empty in 
      fun lexbuf ->
        let p = Lexing.lexeme_start_p lexbuf in
        let new_pos = 
        Reporting.Pos.(
          { line = p.Lexing.pos_lnum
          ; offset= p.Lexing.pos_cnum 
          ; bol =  p.Lexing.pos_bol
          } 
        )
        in 
        let span = Reporting.Span.({ start_ = !prev_pos; end_ = new_pos}) in 
        prev_pos := new_pos;
        span
}

(* ~~ Regex aliases ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let whitespace = [' ' '\t'  '\011' '\012' '\n' '\r']
let newline = ("\r"|"\n"|"\r\n")
let any_char = (_ | ['\n'] )

let name0= ['a'-'z''A'-'Z''_']
let name = name0 ['a'-'z''A'-'Z''0'-'9''_']*

let lnum = ['0'-'9']+
let dnum = (['0'-'9']*['.']['0'-'9']+) | (['0'-'9']+['.']['0'-'9']* )
let exponent_dnum = ((lnum|dnum)['e''E']['+''-']?lnum)
let hexnum = ("0x" | "0X")['0'-'9''a'-'f''A'-'F']+
let binnum = "0b"['0'-'1']+


let double_quotes_literal_dollar =
  ("$"+([^'a'-'z''A'-'Z''_''$''"''\\' '{']|('\\' any_char)))
let double_quotes_chars =
  ("{"*([^'$''"''\\''{']|
    ("\\" any_char))| double_quotes_literal_dollar)

rule token = parse
  (* ~~ Whitespace ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | newline                 { new_line lexbuf; 
                              let _ : Reporting.Span.t = current_loc lexbuf in 
                              token lexbuf 
                            }
  | whitespace +            { let _ : Reporting.Span.t = current_loc lexbuf in
                              token lexbuf 
                            }
  | "/*"                    { multiline_comment lexbuf;
                              let _ : Reporting.Span.t = current_loc lexbuf in
                              token lexbuf 
                            }
  | "/**"                   { multiline_comment lexbuf;
                              let _ : Reporting.Span.t = current_loc lexbuf in
                              token lexbuf 
                            }
  | "//"                    { singleline_comment lexbuf;
                              let _ : Reporting.Span.t = current_loc lexbuf in  
                              token lexbuf 
                            }

  (* ~~ Keywords ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* | "while"                 { WHILE (current_loc lexbuf) } *)
  (* | "do"                    { DO (current_loc lexbuf) } *)
  (* | "for"                   { FOR (current_loc lexbuf) } *)
  (* | "foreach"               { FOREACH (current_loc lexbuf) } *)
  | "if"                    { IF (current_loc lexbuf) }
  | "else"                  { ELSE (current_loc lexbuf) }
  (* | "break"                 { BREAK (current_loc lexbuf) } *)
  (* | "continue"              { CONTINUE (current_loc lexbuf) } *)
  (* | "switch"                { SWITCH (current_loc lexbuf) } *)
  (* | "case"                  { CASE (current_loc lexbuf) } *)
  (* | "default"               { DEFAULT (current_loc lexbuf) } *)
  (* | "exit"                  { EXIT (current_loc lexbuf) } *) 
  | "return"                { RETURN (current_loc lexbuf) }
  | "as"                    { AS (current_loc lexbuf) }
  | "class"                 { CLASS (current_loc lexbuf) }
  | "interface"             { INTERFACE (current_loc lexbuf) }
  | "trait"                 { TRAIT (current_loc lexbuf) }
  | "extends"               { EXTENDS (current_loc lexbuf) }
  | "implements"            { IMPLEMENTS (current_loc lexbuf) }
  | "require"               { REQUIRE (current_loc lexbuf) }
  | "new"                   { NEW (current_loc lexbuf) }
  | "use"                   { USE (current_loc lexbuf) }
  | "abstract"              { ABSTRACT (current_loc lexbuf) }
  | "final"                 { FINAL (current_loc lexbuf) }
  | "public"                { PUBLIC (current_loc lexbuf) }
  (* | "protected"             { PROTECTED (current_loc lexbuf) } *)
  | "private"               { PRIVATE (current_loc lexbuf) }
  | "function"              { FUNCTION (current_loc lexbuf) }
  | "static"                { STATIC (current_loc lexbuf) }
  (* | "newtype"               { NEWTYPE (current_loc lexbuf) } *)
  | "is"                    { IS (current_loc lexbuf) }
  (* | "enum"                  { ENUM (current_loc lexbuf) } *)
  | "super"                 { SUPER (current_loc lexbuf) }
  | "const"                 { CONST (current_loc lexbuf) }
  | "type"                  { TYPE (current_loc lexbuf) }
  (* | "shape"                 { SHAPE (current_loc lexbuf) } *)
  | "where"                 { WHERE (current_loc lexbuf) }
  | "optional"              { OPTIONAL (current_loc lexbuf) }
  | "some"                  { SOME (current_loc lexbuf) }
  | "let"                   { LET (current_loc lexbuf) } 
  | "bool"                  { BOOL (current_loc lexbuf) }
  | "int"                   { INT (current_loc lexbuf) }
  | "float"                 { FLOAT (current_loc lexbuf) }
  | "string"                { STRING (current_loc lexbuf) }
  | "nonnull"               { NONNULL (current_loc lexbuf) }
  | "this"                  { THIS (current_loc lexbuf) }

 (* ~~ Symbols & punctuation ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | '+'                     { PLUS (current_loc lexbuf) }
  | '-'                     { MINUS (current_loc lexbuf) }
  (* | '*'                     { MUL (current_loc lexbuf) } *)
  (* | '/'                     { DIV (current_loc lexbuf) } *)
  | ','                     { COMMA (current_loc lexbuf) }
  | '.'                     { DOT (current_loc lexbuf) }
  | '?'                     { QUESTION (current_loc lexbuf) }
  | "="                     { EQUAL (current_loc lexbuf) }
  (* | "=="                    { IS_EQUAL (current_loc lexbuf) } *)
  (* | "!="                    { IS_NOT_EQUAL  (current_loc lexbuf)} *)
  (* | "<>"                    { IS_NOT_EQUAL (current_loc lexbuf) } *)
  (* | "==="                   { IS_IDENTICAL  (current_loc lexbuf)} *)
  (* | "!=="                   { IS_NOT_IDENTICAL (current_loc lexbuf) } *)
  (* | "<="                    { IS_LESS_THAN_OR_EQUAL (current_loc lexbuf) } *)
  (* | ">="                    { IS_GREATER_THAN_OR_EQUAL (current_loc lexbuf) } *)
  | "<"                     { LANGLE (current_loc lexbuf) }
  | ">"                     { RANGLE (current_loc lexbuf) }
  | "&&"                    { LOGICAL_AND (current_loc lexbuf) }
  | "||"                    { LOGICAL_OR (current_loc lexbuf) }
  | ";"                     { SEMICOLON (current_loc lexbuf)}
  (* | "!"                     { BANG (current_loc lexbuf)} *)
  | '('                     { LPAREN (current_loc lexbuf)}
  | ')'                     { RPAREN (current_loc lexbuf)}
  (* | '['                     { LBRACKET (current_loc lexbuf)} *)
  (* | ']'                     { RBRACKET (current_loc lexbuf)} *)
  | '{'                     { LBRACE (current_loc lexbuf)}
  | '}'                     { RBRACE (current_loc lexbuf)}
  | ":"                     { COLON (current_loc lexbuf)}
  (* | "=>"                    { DOUBLE_ARROW (current_loc lexbuf)} *)
  (* | "==>"                   { LONG_DOUBLE_ARROW (current_loc lexbuf)} *)
  (* | "->"                    { ARROW (current_loc lexbuf)} *)
  (* | "?->"                   { QUESTION_ARROW (current_loc lexbuf)} *)
  | "..."                   { ELLIPSIS (current_loc lexbuf)}
  | "&"                     { AMPERSAND (current_loc lexbuf)}
  | "|"                     { PIPE (current_loc lexbuf)}
  | "_"                     { UNDERSCORE (current_loc lexbuf)}

  (* ~~ Literals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  | "null"                  { NULL (current_loc lexbuf) }
  (* ~~ Bools ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | "true"                  { TRUE (current_loc lexbuf) }
  | "false"                 { FALSE (current_loc lexbuf) }
  (* ~~ Numbers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | lnum | binnum | hexnum
    { (* more? cf original lexer *)
      let s = Lexing.lexeme lexbuf in
      match int_of_string s with
      | _ -> LNUMBER (s, current_loc lexbuf)
      | exception Failure _ -> DNUMBER (s,current_loc lexbuf)
    }
  | dnum | exponent_dnum
    { DNUMBER (Lexing.lexeme lexbuf, current_loc lexbuf) }

  (* ~~ Static strings ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | 'b'? (['"'] ((double_quotes_chars* ("{"*|"$"* )) as s) ['"'])
      { CONSTANT_ENCAPSED_STRING (s, current_loc lexbuf) }

  | 'b'? (['\''] (([^'\'' '\\']|('\\' any_char))* as s)  ['\''])
      { (* more? cf original lexer *)
        CONSTANT_ENCAPSED_STRING (s, current_loc lexbuf) }


  
  (* ~~ Names & locals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | name                    { IDENT (Lexing.lexeme lexbuf, current_loc lexbuf) }
  | "$this"                 { IDENT_THIS (current_loc lexbuf) }
  | "$" (name as nm)        { LOCAL (Lexing.lexeme lexbuf, current_loc lexbuf) }

  (* ~~ End states ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | eof                     { EOF }
  | _ 
    { raise (UnexpectedChar (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) 
    }

and multiline_comment = parse
  | "*/"                    { () }
  | eof                     { raise UnterminatedComment }
  | '\n'                    { new_line lexbuf; multiline_comment lexbuf }
  | _                       { multiline_comment lexbuf }

and singleline_comment = parse
  | '\n'                    { new_line lexbuf }
  | eof                     { () }
  | _                       { singleline_comment lexbuf }