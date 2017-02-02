let dummy = Id.genid "dummy"
let index_ref=ref dummy
let fun_name = ref dummy(*mk_rw_graphが解析中の関数名*)
let (fundef_env:(KNormal.fundef M.t) ref) = ref M.empty


type t =(*loop内の変数を分類*)
  |Unit
  |Int of int
  |Index of int(*index変数+(整数定数)*)
  |Float of float
  |Elm of Id.t * elm_pos
  |Parent of (elm_pos*Id.t) list(*array_treeでparentに当たるもの*)
  |Arraytree_var of Id.t
  |Trace_add of Id.t * Id.t
  |Unknown
 and elm_pos =
   |Array of t(*tはint(i),index(i),unknown,のどれか*)
   |Tuple of int(*tupleの要素位置はコンパイル時整数*)
   |Ref


let find a env = try M.find a env with Not_found ->a

let print_path_from_root (a,poslist) =
  let path=
    List.fold_left
      (fun path pos ->
        match pos with  
        |Array(Int(i))->path^(Printf.sprintf ".(%d)" i)
        |Array(Index(i))->path^(Printf.sprintf ".(i+%d)" i)
        |Array(_) ->path^(Printf.sprintf ".(unknown)" )
        |Tuple(i) ->path^(Printf.sprintf ".<%d>" i)
        |Ref ->path^".<refelm>" )
      ""
      poslist
  in
  Format.eprintf "%s%s@." a path

  
let print_apos (a,pos)=
  match pos with
  |Array(Int(i))->Format.eprintf "%s.(%d)@." a i
  |Array(Index(i))->Format.eprintf "%s.(i+%d)@." a i
  |Array(_) ->Format.eprintf "%s.(unknown)@." a
  |Tuple(i) ->Format.eprintf "tuple:%s,elm:%d@." a i
  |Ref ->Format.eprintf "ref:%sd,elm@." a
                                                     
let rec subst env =function
  |Elm(a,pos)->Elm(find a env,pos)
  |Parent(pas)->Parent(List.map (fun (pos,a) ->(pos,find a env)) pas)
  |Arraytree_var(a) ->Arraytree_var(find a env)
  |Trace_add(x,y) ->Trace_add(find x env,find y env)
  |e ->e

(*変数が*)
let cmple e1 e2 =
  match (e1,e2) with
  |Int(i1),Int(i2) ->Some (i1<=i2)
  |Float(d1),Float(d2) ->Some (d1<=d2)
  |_ ->None

let cmpeq e1 e2 =
  match (e1,e2) with
  |Int(i1),Int(i2) ->Some (i1=i2)
  |Float(d1),Float(d2) ->Some (d1=d2)
  |_ ->None


let is_intpos = function
  |Array(Int _)|Tuple _ ->true
  |_ ->false

let is_indexpos = function
  |Array(Index _) ->true
  |_ ->false
