open Asm
exception Closure
exception Call_parallel
let rec free_lavel env = function
  (* 参照されるラベルを集める env: 関数->関数内で参照されるラベル*)
  |Ans(exp) ->free_lavel' env exp
  |Let(xt,exp,e) -> (free_lavel' env exp)@(free_lavel env e)
and free_lavel' env = function
  |CallDir(Id.L(name),_,_) ->
    (try
       Id.L(name)::(M.find name env)
    with
      Not_found ->
      Format.eprintf "%s@." name;
      raise Not_found)
  |Lwi(_,l)|FLwi(_,l)|Swi(_,_,l)|FSwi(_,_,l)|La(l) ->[l]
  |CallCls _ ->raise Closure    (*取り敢えず手抜き  *)
  |Run_parallel _ ->[]
  |IfEq(_,_,e1,e2)|IfLE(_,_,e1,e2)|IfFZ(_,e1,e2)|IfFLE(_,_,e1,e2) ->
    (free_lavel env e1)@(free_lavel env e2)
  |ForLE(_,e) ->free_lavel env e
  |_ ->[]

let rec list_uniq = function
  |x::xs ->let xs' = list_uniq xs in
           if List.mem x xs' then
             xs'
           else
             x::xs'
  |[] ->[]

    
let make_env fundefs =          (* 関数内で参照されるラベルをボトムアップに調べる *)
  List.fold_left
    (fun env {name=Id.L(x) ; args=_ ; fargs=_ ; body=e ; ret = _} ->
      try
        let env' = M.add x [] env in (* 再帰に対応する為 *)
        let lavels = list_uniq  (free_lavel env' e) in
        M.add x lavels env
      with
        Not_found -> Format.eprintf "%s@." x;
                     env)
        
    (M.add "min_caml_create_array" []
           (M.add "min_caml_create_float_array" [] M.empty))
    fundefs

let f parallel (data,fundefs) =
  match parallel with
  |Some {pargs=_;
         pfargs=_;
         index=(i,(j',k'));
         pbody=e} ->
    let env = make_env fundefs in
    
    let lavels = free_lavel env e in
    (* lavelsにあるデータだけ残す *)
    let data'= List.filter (fun (l,_) ->List.mem l lavels) data in
    let fundefs' = List.filter (fun fundef ->List.mem fundef.name lavels) fundefs in
    let arraydefs' =
      List.filter (fun {HpAlloc.name=(l,_);HpAlloc.size =_;HpAlloc.initv=_} ->
          List.mem l lavels)
                  !HpAlloc.arrays
    in
    let tupledefs' =
            List.filter (fun {HpAlloc.name=(l,_);HpAlloc.body = _} ->
                List.mem l lavels)
                        !HpAlloc.tuples
    in
    (data',tupledefs',arraydefs',fundefs')
  |None ->(data,!HpAlloc.tuples,!HpAlloc.arrays,fundefs)
      
    

      
  
    
