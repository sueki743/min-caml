open Syntax

module NodeSet =
	Set.Make
		(struct
			type t = string
			let compare = compare
		end)
module EdgeSet =
	Set.Make
		(struct
			type t = string * string
			let compare = compare
		end)

let input_nodes ic =
	let rec iter_input_nodes nodes =
		try
			let line = input_line ic in
			if line.[0] = '#' then iter_input_nodes nodes
			                  else iter_input_nodes (NodeSet.add line nodes)
		with
		| End_of_file -> nodes
		| Invalid_argument _ -> iter_input_nodes nodes
	in iter_input_nodes NodeSet.empty

let f oc e =
	let ignore_nodes =
		let ic = open_in "test/minrt.ignore" in
		let ignore_nodes = input_nodes ic in
			close_in ic; ignore_nodes
	in
	let rec g (nodes, edges) = function
		| LetRec({name=(x0,t); args=yts; body=e1}, e2) when NodeSet.mem x0 ignore_nodes ->
			g (nodes, edges) e2
		| LetRec({name=(x0,t); args=yts; body=e1}, e2) ->
			let nodes = x0::nodes in
			let rec h edges = function
				| App(e,es) ->
					(match e with
					| Var(x) when NodeSet.mem x ignore_nodes -> List.fold_left h edges es
					| Var(x) -> List.fold_left h (EdgeSet.add (x0, x) edges) es
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
	let (nodes, edges) = g ([], EdgeSet.empty) e in
	List.iter (Printf.fprintf oc "%s [style=filled, fillcolor=green];\n") nodes;
	Printf.fprintf oc "\n";
	EdgeSet.iter (fun (x1,x2) -> Printf.fprintf oc "%s -> %s;\n" x1 x2) edges;
	Printf.fprintf oc "}\n";
		e
