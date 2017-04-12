open Parser

let _ =
	let inchan = open_in "rayracer/minrt.ml" in
	let l = Lexing.from_channel inchan in
	let rec f m =
		let token = Lexer.token l in
		if token = EOF
		then m
		else
			let count = try M.find token m with Not_found -> 0 in
			f (M.add token (count+1) m)
	in
	let m = f M.empty in
	let outchan = open_out "result.txt" in
	let string_of_token = function
		| BOOL(b) -> Printf.sprintf "BOOL(%B)" b
		| INT(i) -> Printf.sprintf "INT(%d)" i
		| FLOAT(f) -> Printf.sprintf "FLOAT(%F)" f
		| NOT -> "NOT"
		| MINUS -> "MINUS"
		| PLUS -> "PLUS"
		| AST -> "AST"
		| SLASH -> "SLASH"
		| MINUS_DOT -> "MINUS_DOT"
		| PLUS_DOT -> "PLUS_DOT"
		| AST_DOT -> "AST_DOT"
		| SLASH_DOT -> "SLASH_DOT"
		| EQUAL -> "EQUAL"
		| LESS_GREATER -> "LESS_GREATER"
		| LESS_EQUAL -> "LESS_EQUAL"
		| GREATER_EQUAL -> "GREATER_EQUAL"
		| LESS -> "LESS"
		| GREATER -> "GREATER"
		| IF -> "IF"
		| THEN -> "THEN"
		| ELSE -> "ELSE"
		| IDENT(x) -> Printf.sprintf "IDENT(%s)" x
		| LET -> "LET"
		| IN -> "IN"
		| REC -> "REC"
		| COMMA -> "COMMA"
		| ARRAY_CREATE -> "ARRAY_CREATE"
		| READ_INT -> "READ_INT"
		| READ_FLOAT -> "READ_FLOAT"
		| PRINT_CHAR -> "PRINT_CHAR"
		| FTOI -> "FTOI"
		| ITOF -> "ITOF"
		| FSQRT -> "FSQRT"
		| FABS -> "FABS"
		| FNEG -> "FNEG"
		| FLESS -> "FLESS"
		| FISPOS -> "FISPOS"
		| FISNEG -> "FISNEG"
		| FISZERO -> "FISZERO"
		| DOT -> "DOT"
		| LESS_MINUS -> "LESS_MINUS"
		| SEMICOLON -> "SEMICOLON"
		| LPAREN -> "LPAREN"
		| RPAREN -> "RPAREN"
		| EOF -> failwith "unexpected EOF"
	in
	let print token count = Printf.fprintf outchan "%s %d\n" (string_of_token token) count in
	M.iter print m
