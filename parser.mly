%{
(* parserが利用する変数、関数、型などの定義 *)
open Syntax
let addtyp x = (x, Type.gentyp ())
let getpos () =
    let pos = Parsing.symbol_start_pos () in
    let linenum = pos.Lexing.pos_lnum in
    let charnum = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in
    {line=linenum;characters=charnum}
%}

/* (* 字句を表すデータ型の定義 (caml2html: parser_token) *) */
%token <bool> BOOL
%token <int> INT
%token <float> FLOAT
%token NOT
%token MINUS
%token PLUS
%token AST
%token SLASH
%token MINUS_DOT
%token PLUS_DOT
%token AST_DOT
%token SLASH_DOT
%token EQUAL
%token LESS_GREATER
%token LESS_EQUAL
%token GREATER_EQUAL
%token LESS
%token GREATER
%token IF
%token THEN
%token ELSE
%token <Id.t> IDENT
%token LET
%token IN
%token REC
%token COMMA
%token ARRAY_CREATE

%token READ_INT
%token READ_FLOAT
%token PRINT_CHAR
%token FTOI
%token ITOF
%token FSQRT
%token FABS
%token FNEG
%token FLESS
%token FISPOS
%token FISNEG
%token FISZERO

%token DOT
%token LESS_MINUS
%token SEMICOLON
%token LPAREN
%token RPAREN
%token EOF

/* (* 優先順位とassociativityの定義（低い方から高い方へ） (caml2html: parser_prior) *) */
%right prec_let
%right SEMICOLON
%right prec_if
%right LESS_MINUS
%left COMMA
%left EQUAL LESS_GREATER LESS GREATER LESS_EQUAL GREATER_EQUAL
%left PLUS MINUS AST SLASH PLUS_DOT MINUS_DOT
%left AST_DOT SLASH_DOT
%right prec_unary_minus
%left prec_app
%left DOT

/* (* 開始記号の定義 *) */
%type <Syntax.t> exp
%start exp

%%

simple_exp: /* (* 括弧をつけなくても関数の引数になれる式 (caml2html: parser_simple) *) */
| LPAREN exp RPAREN
    { $2 }
| LPAREN RPAREN
    { Unit(getpos ()) }
| BOOL
    { Bool($1,getpos()) }
| INT
    { Int($1,getpos()) }
| FLOAT
    { Float($1,getpos()) }
| IDENT
    { Var($1,getpos()) }
| simple_exp DOT LPAREN exp RPAREN
    { Get($1, $4) }

exp: /* (* 一般の式 (caml2html: parser_exp) *) */
| simple_exp
    { $1 }
| NOT exp
    %prec prec_app
    { Not($2) }
| exp SEMICOLON
    { $1 }
| MINUS exp
    %prec prec_unary_minus
    { match $2 with
    | Float(f,_) -> Float(-.f,getpos()) (* -1.23などは型エラーではないので別扱い *)
    | e -> Neg(e) }
| exp PLUS exp /* (* 足し算を構文解析するルール (caml2html: parser_add) *) */
    { Add($1, $3) }
| exp MINUS exp
    { Sub($1, $3) }
| exp AST exp
    { Mul($1, $3) }
| exp SLASH exp
    { Div($1, $3) }
| exp EQUAL exp
    { Eq($1, $3) }
| exp LESS_GREATER exp
    { Not(Eq($1, $3)) }
| exp LESS exp
    { Not(LE($3, $1)) }
| exp GREATER exp
    { Not(LE($1, $3)) }
| exp LESS_EQUAL exp
    { LE($1, $3) }
| exp GREATER_EQUAL exp
    { LE($3, $1) }
| IF exp THEN exp ELSE exp
    %prec prec_if
    { If($2, $4, $6) }
| MINUS_DOT exp
    %prec prec_unary_minus
    { FNeg($2) }
| exp PLUS_DOT exp
    { FAdd($1, $3) }
| exp MINUS_DOT exp
    { FSub($1, $3) }
| exp AST_DOT exp
    { FMul($1, $3) }
| exp SLASH_DOT exp
    { FDiv($1, $3) }
| LET IDENT EQUAL exp IN exp
    %prec prec_let
    { Let(addtyp $2, $4, $6) }
| LET REC fundef IN exp
    %prec prec_let
    { LetRec($3, $5) }
| exp actual_args
    %prec prec_app
    { App($1, $2) }
| elems
    { Tuple($1) }
| LET LPAREN pat RPAREN EQUAL exp IN exp
    { LetTuple($3, $6, $8) }
| simple_exp DOT LPAREN exp RPAREN LESS_MINUS exp
    { Put($1, $4, $7) }
| exp SEMICOLON exp
    { Let((Id.gentmp Type.Unit, Type.Unit), $1, $3) }
| ARRAY_CREATE simple_exp simple_exp
    %prec prec_app
    { Array($2, $3) }
| FLESS simple_exp simple_exp
   %prec prec_app
   { LE($2, $3) }
| FISPOS simple_exp
  %prec prec_app
  { LE( Float(0.0,getpos () ), $2) }
| FISNEG simple_exp
  %prec prec_app
  { LE( $2, Float(0.0,getpos ())) }
| FISZERO simple_exp
  %prec prec_app
  { Eq($2, Float(0.0,getpos ())) }
| READ_INT simple_exp
    %prec prec_app
    { Read_int($2) }
| READ_FLOAT simple_exp
    %prec prec_app
    { Read_float($2) }
| PRINT_CHAR simple_exp
    %prec prec_app
    { Print_char($2) }
| FTOI simple_exp
   %prec prec_app
    { Ftoi($2) }
| ITOF simple_exp
   %prec prec_app
    { Itof($2) }
| FABS simple_exp
   %prec prec_app
    { FAbs($2) }
| FSQRT simple_exp
   %prec prec_app
    { FSqrt($2) }
| FNEG simple_exp
   %prec prec_app
    { FNeg($2) }



| error
    { failwith
     (let line_pos=(Parsing.symbol_start_pos ()).Lexing.pos_bol in
	(Printf.sprintf "parse error near line %d charactfers %d-%d"
	   ((Parsing.symbol_start_pos ()).Lexing.pos_lnum)
	   ((Parsing.symbol_start_pos ()).Lexing.pos_cnum-line_pos)
	   ((Parsing.symbol_end_pos ()).Lexing.pos_cnum-line_pos))) }

fundef:
| IDENT formal_args EQUAL exp
    { { name = (addtyp $1,getpos()); args = $2; body = $4 } }/*(*addtypeは変数に型変数を追加*)*/

formal_args:
| IDENT formal_args
    { addtyp $1 :: $2 }
| IDENT
    { [addtyp $1] }

actual_args:
| actual_args simple_exp
    %prec prec_app
    { $1 @ [$2] }
| simple_exp
    %prec prec_app
    { [$1] }

elems:
| elems COMMA exp
    { $1 @ [$3] }
| exp COMMA exp
    { [$1; $3] }

pat:
| pat COMMA IDENT
    { $1 @ [addtyp $3] }
| IDENT COMMA IDENT
    { [addtyp $1; addtyp $3] }
