(* type inference/reconstruction *)

open Syntax

exception Unify of Type.t * Type.t
exception Error of Type.t * Type.t * pos
exception Occur of Type.t * Type.t * pos

let extenv = ref M.empty

(* for pretty printing (and type normalization) *)
let rec deref_typ = function (* 型変数を中身でおきかえる関数 (caml2html: typing_deref) *)
  | Type.Fun(t1s, t2) -> Type.Fun(List.map deref_typ t1s, deref_typ t2)
  | Type.Tuple(ts) -> Type.Tuple(List.map deref_typ ts)
  | Type.Array(t) -> Type.Array(deref_typ t)
  | Type.Var({ contents = None } as r) ->
      Format.eprintf "uninstantiated type variable detected; assuming int@.";
      r := Some(Type.Int);
      Type.Int
  | Type.Var({ contents = Some(t) } as r) ->
      let t' = deref_typ t in
      r := Some(t');
      t'
  | t -> t
let rec deref_id_typ (x, t) = (x, deref_typ t)
let rec deref_term = function
  | Not(e) -> Not(deref_term e)
  | Neg(e) -> Neg(deref_term e)
  | Add(e1, e2) -> Add(deref_term e1, deref_term e2)
  | Sub(e1, e2) -> Sub(deref_term e1, deref_term e2)
  | Mul(e1, e2) -> Mul(deref_term e1, deref_term e2)
  | Div(e1, e2) -> Div(deref_term e1, deref_term e2)
  | Eq(e1, e2) -> Eq(deref_term e1, deref_term e2)
  | LE(e1, e2) -> LE(deref_term e1, deref_term e2)
  | FNeg(e) -> FNeg(deref_term e)
  | FAdd(e1, e2) -> FAdd(deref_term e1, deref_term e2)
  | FSub(e1, e2) -> FSub(deref_term e1, deref_term e2)
  | FMul(e1, e2) -> FMul(deref_term e1, deref_term e2)
  | FDiv(e1, e2) -> FDiv(deref_term e1, deref_term e2)
  | If(e1, e2, e3) -> If(deref_term e1, deref_term e2, deref_term e3)
  | Let(xt, e1, e2) -> Let(deref_id_typ xt, deref_term e1, deref_term e2)
  | LetRec({ name = (xt,pos); args = yts; body = e1 }, e2) ->
      LetRec({ name = (deref_id_typ xt,pos);
	       args = List.map deref_id_typ yts;
	       body = deref_term e1 },
	     deref_term e2)
  | App(e, es) -> App(deref_term e, List.map deref_term es)
  | Tuple(es) -> Tuple(List.map deref_term es)
  | LetTuple(xts, e1, e2) -> LetTuple(List.map deref_id_typ xts, deref_term e1, deref_term e2)
  | Array(e1, e2) -> Array(deref_term e1, deref_term e2)
  | Get(e1, e2) -> Get(deref_term e1, deref_term e2)
  | Put(e1, e2, e3) -> Put(deref_term e1, deref_term e2, deref_term e3)
  | Ftoi(e) ->Ftoi(deref_term e)
  | Itof(e) ->Itof(deref_term e)
  | FAbs(e) ->FAbs(deref_term e)
  | FSqrt(e) ->FSqrt(deref_term e)
  | Read_int(e) ->Read_int(deref_term e)
  | Read_float(e) ->Read_float(deref_term e)
  | Print_char(e) ->Print_char(deref_term e)
  | e -> e

let rec occur r1 = function (* occur check (caml2html: typing_occur) *)
  | Type.Fun(t2s, t2) -> List.exists (occur r1) t2s || occur r1 t2
  | Type.Tuple(t2s) -> List.exists (occur r1) t2s
  | Type.Array(t2) -> occur r1 t2
  | Type.Var(r2) when r1 == r2 -> true
  | Type.Var({ contents = None }) -> false
  | Type.Var({ contents = Some(t2) }) -> occur r1 t2
  | _ -> false

let rec unify t1 t2 = (* 型が合うように、型変数への代入をする (caml2html: typing_unify) *)
  match t1, t2 with
  | Type.Unit, Type.Unit | Type.Bool, Type.Bool | Type.Int, Type.Int | Type.Float, Type.Float -> ()
  | Type.Fun(t1s, t1'), Type.Fun(t2s, t2') ->
      (try List.iter2 unify t1s t2s
      with Invalid_argument("List.iter2") -> raise (Unify(t1, t2)));
      unify t1' t2'
  | Type.Tuple(t1s), Type.Tuple(t2s) ->
      (try List.iter2 unify t1s t2s
      with Invalid_argument("List.iter2") -> raise (Unify(t1, t2)))
  | Type.Array(t1), Type.Array(t2) -> unify t1 t2
  | Type.Var(r1), Type.Var(r2) when r1 == r2 -> ()
  | Type.Var({ contents = Some(t1') }), _ -> unify t1' t2
  | _, Type.Var({ contents = Some(t2') }) -> unify t1 t2'
  | Type.Var({ contents = None } as r1), _ -> (* 一方が未定義の型変数の場合 (caml2html: typing_undef) *)
      if occur r1 t2 then raise (Unify(t1, t2));
      r1 := Some(t2)
  | _, Type.Var({ contents = None } as r2) ->
      if occur r2 t1 then raise (Unify(t1, t2));
      r2 := Some(t1)
  | _, _ -> raise (Unify(t1, t2))

let rec g env e = (* 型推論ルーチン (caml2html: typing_g) *)
    match e with
    | Unit (_) -> Type.Unit
    | Bool(_,_) -> Type.Bool
    | Int(_,_) -> Type.Int
    | Float(_,_) -> Type.Float
    | Not(e) ->
       let t1 = g env e in
       (try unify Type.Bool t1 with
         Unify _ ->raise (Error (Type.Bool,deref_typ t1,startpos e)) );
	Type.Bool
    | Neg(e) ->
       let t1 = g env e in
       (try unify Type.Int t1 with
         Unify _ ->raise (Error (Type.Int,deref_typ t1,startpos e)));
         Type.Int
    | Add(e1, e2) | Sub(e1, e2)| Mul(e1,e2)|Div(e1,e2) -> (* 足し算（と引き算）の型推論 (caml2html: typing_add) *)
       let t1 = g env e1 in
       let t2 = g env e2 in
       (try unify Type.Int t1 with
          Unify _ -> raise (Error (Type.Int,deref_typ t1,startpos e1)));
       (try unify Type.Int t2 with
          Unify _ -> raise (Error (Type.Int,deref_typ t2,startpos e2)));
	Type.Int
    | FNeg(e) ->
       let t1 = g env e in
       (try unify Type.Float t1 with
         Unify _ ->raise (Error (Type.Float,deref_typ t1,startpos e)));
       Type.Float
    | Ftoi(e) ->
       let t1 = g env e in
       (try unify Type.Float t1 with
         Unify _ ->raise (Error (Type.Float,deref_typ t1,startpos e)));
       Type.Int
    | Itof(e) ->
       let t1 = g env e in
       (try unify Type.Int t1 with
         Unify _ ->raise (Error (Type.Int,deref_typ t1,startpos e)));
       Type.Float
    | FAbs(e) ->
       let t1 = g env e in
       (try unify Type.Float t1 with
         Unify _ ->raise (Error (Type.Float,deref_typ t1,startpos e)));
       Type.Float
    | FSqrt(e) ->
       let t1 = g env e in
       (try unify Type.Float t1 with
         Unify _ ->raise (Error (Type.Float,deref_typ t1,startpos e)));
       Type.Float
    | Read_int(e) ->
       let t1 = g env e in
       (try unify Type.Unit t1 with
         Unify _ ->raise (Error (Type.Unit,deref_typ t1,startpos e)));
       Type.Int
    | Read_float(e) ->
       let t1 = g env e in
       (try unify Type.Unit t1 with
         Unify _ ->raise (Error (Type.Unit,deref_typ t1,startpos e)));
       Type.Float
    | Print_char(e) ->
       let t1 = g env e in
       (try unify Type.Int t1 with
         Unify _ ->raise (Error (Type.Int,deref_typ t1,startpos e)));
       Type.Unit
    | FAdd(e1, e2) | FSub(e1, e2) | FMul(e1, e2) | FDiv(e1, e2) ->
       let t1 = g env e1 in
       let t2 = g env e2 in
       (try unify Type.Float t1 with
          Unify _ -> raise (Error (Type.Float,deref_typ t1,startpos e1)));
       (try unify Type.Float t2 with
          Unify _ -> raise (Error (Type.Float,deref_typ t2,startpos e2)));
       Type.Float
    | Eq(e1, e2) | LE(e1, e2) ->
       let t1 = g env e1 in
       let t2 = g env e2 in
       (try unify t1 t2 with
          Unify _ -> raise (Error (deref_typ t1,deref_typ t2,startpos e2)));
       Type.Bool
    | If(e1, e2, e3) ->
       let t1 = g env e1 in
       (try unify Type.Bool t1 with
          Unify _ -> raise (Error (Type.Bool,deref_typ t1,startpos e1)));
	let t2 = g env e2 in
	let t3 = g env e3 in
	(try unify t2 t3 with
           Unify _ -> raise (Error(deref_typ t2,deref_typ t3,startpos e3)));
	t2
    | Let((x, t), e1, e2) -> (* letの型推論 (caml2html: typing_let) *)
       let t1=g env e1 in
       (try unify t t1 with(*ここで単一化エラーは起こらない*)
          Unify _ -> raise (Error(t,t1,startpos e1)));
	g (M.add x t env) e2
    | Var(x,_) when M.mem x env -> M.find x env (* 変数の型推論 (caml2html: typing_var) *)
    | Var(x,_) when M.mem x !extenv -> M.find x !extenv
    | Var(x,_) -> (* 外部変数の型推論 (caml2html: typing_extvar) *)
	Format.eprintf "free variable %s assumed as external@." x;
	let t = Type.gentyp () in
	extenv := M.add x t !extenv;
	t
    | LetRec({ name = (x, t),pos; args = yts; body = e1 }, e2) -> (* let recの型推論 (caml2html: typing_letrec) *)
       let env = M.add x t env in
       let tbody = g (M.add_list yts env) e1 in
       let targs = List.map snd yts in
       (try unify t (Type.Fun(targs,tbody)) with
          Unify _ ->(*tが未定義のまま単一化失敗->tのoccurcheckでエラー*)
          (match t with
          |Type.Var ({contents=None}) ->raise (Occur(t,Type.Fun(targs,tbody),pos))
          |_ -> raise (Error(t,Type.Fun(targs,tbody),pos))));
	g env e2
    | App(e, es) -> (* 関数適用の型推論 (caml2html: typing_app) *)
       let t = Type.gentyp () in
       let t1 = g env e in
       let ts1 = (Type.Fun(List.map (g env) es, t)) in
	(try unify t1 ts1 with
           Unify _ ->raise (Error(ts1,t1,startpos e)));
	t
    | Tuple(es) -> Type.Tuple(List.map (g env) es)
    | LetTuple(xts, e1, e2) ->
       let txs=Type.Tuple(List.map snd xts) in
       let t1=g env e1 in
       (try unify txs t1 with
          Unify _ -> raise (Error(txs,t1,startpos e1)));
	g (M.add_list xts env) e2
    | Array(e1, e2) -> (* must be a primitive for "polymorphic" typing *)
       let t1=g env e1 in
       (try unify t1 Type.Int with
          Unify _ ->raise (Error(Type.Int,t1,startpos e1)));
	Type.Array(g env e2)
    | Get(e1, e2) ->
       let t = Type.gentyp () in
       let t1 = g env e1 in
       (try unify (Type.Array(t)) t1 with
          Unify _ ->raise (Error(Type.Array(t),t1,startpos e1)));
       let t2 = g env e2 in
       (try unify Type.Int t2 with
          Unify _ ->raise (Error(Type.Int, t2,startpos e2)));
	t
    | Put(e1, e2, e3) ->
       let t3 = g env e3 in
       let t1 = g env e1 in
       (try unify (Type.Array(t3)) t1 with
          Unify _ ->raise (Error(Type.Array(t3),t1,startpos e1)));
       let t2 = g env e2 in
       (try unify Type.Int t2 with
         Unify _ ->raise (Error(Type.Int, t2,startpos e2)));
	Type.Unit

       
let f e =
  extenv := M.empty;
(*
  (match deref_typ (g M.empty e) with
  | Type.Unit -> ()
  | _ -> Format.eprintf "warning: final result does not have type unit@.");
 *)
  let t = g M.empty e in
  (try unify Type.Unit t with
     Unify _ ->(try unify Type.Int t with
                  Unify _ ->failwith "toplevel type is not unit or int"));
  extenv := M.map deref_typ !extenv;
  deref_term e
