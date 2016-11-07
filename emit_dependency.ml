open Syntax

let f oc e =
	let rec g (nodes, edges) = function
		| LetRec({name=(x0,t); args=yts; body=e1}, e2) ->
			let nodes = x0::nodes in
			let rec h edges = function
				| App(e,es) ->
					(match e with
					| Var(x) -> List.fold_left h ((x0, x)::edges) es
					| _ -> failwith "App(not Var, _)"
					)
				| Unit
				| Bool(_)
				| Int(_)
				| Float(_)
				| Var(_) ->
					edges
				| Not(e)
				| Neg(e)
				| FNeg(e) ->
					h edges e
				| Add(e1,e2)
				| Sub(e1,e2)
				| Mul(e1,e2)
				| Div(e1,e2)
				| FAdd(e1,e2)
				| FSub(e1,e2)
				| FMul(e1,e2)
				| FDiv(e1,e2)
				| Eq(e1,e2)
				| LE(e1,e2)
				| Let(_,e1,e2)
				| LetTuple(_,e1,e2)
				| Array(e1,e2)
				| Get(e1,e2) ->
					h (h edges e1) e2
				| If(e1,e2,e3)
				| Put(e1,e2,e3) ->
					h (h (h edges e1) e2) e3
				| Tuple(es) ->
					List.fold_left h edges es
				| LetRec(_,_) ->
					failwith "nested LetRec"
			in
			let edges = h edges e1 in
			g (nodes, edges) e2
		| _ -> (nodes, edges)
	in
	Printf.fprintf oc "digraph G {\n";
	let (nodes, edges) = g ([], []) e in
	List.iter (Printf.fprintf oc "%s [style=filled, fillcolor=green];\n") nodes;
	Printf.fprintf oc "\n";
	List.iter (fun (x1,x2) -> Printf.fprintf oc "%s -> %s;\n" x1 x2) edges;
	Printf.fprintf oc "}\n";
		e
