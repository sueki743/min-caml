open KNormal
let rec loop_exit = function
    | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2)
      | Let(_, e1, e2) | LetRec({ body = e1 }, e2)|Let_Ref(_,e1,e2) ->
       (loop_exit e1)||(loop_exit e2)
    |LetTuple(_,_,e)->loop_exit e
    |ForLE _ ->true
    |_ ->false

type category =
  |Create_array of Id.t *Id.t
  |Create_tuple of Id.t list
  |Const of KNormal.t
  |Ref_elm of Id.t
  |Other 

let rec  category_of =function
  |Int _|Float _|Unit as const ->Const(const)
  |ExtFunApp(l, [arg1;arg2]) when (l="create_array"||l="create_float_array")->
    Create_array(arg1,arg2)
  |Tuple(xs) ->Create_tuple(xs)
  |Ref_Get(a) ->Ref_elm(a)
  |Let(_,_,e2)|LetRec(_,e2)|LetTuple(_,_,e2) ->category_of e2
  |_ ->Other


exception Cant_parallelize
(*forloopを含むfundefを受け取り、Mk_rw_graph.f で読み書きのフローグラフを作成し、Rw_g.analyzeで依存関係を解析する *)
let rec can_parallelize global_regions  constenv fundef_env {name=(fun_name,t);args=yts ; body=e} =
  VarCatego.fun_name:=fun_name;
  let array_arg = List.fold_left
                    (fun array_arg (y,t) ->if(Type.include_array_ref t)then
                                             y::array_arg
                                           else
                                             array_arg)
                    []
                    yts in
  let global_regions' = array_arg@global_regions in(*配列を含む型の引数もglobal_regionsに登録*)
  let para_accum = ref [] in                   
  let rec inner global_regions constenv fundef_env ref_element = function(*ref_elementいらなかった*)
    |LetRec({name=(x,t);args=_;body=e}as fundef,e2) ->(*局所関数*)
      if (S.mem fun_name (fv e)) then(*局所関数を介して再帰*)
        raise Cant_parallelize
      else
        let e2'=
          inner global_regions constenv (M.add x fundef fundef_env) ref_element e2
        in
        LetRec(fundef,e2')
    |Let((x,t),e1,e2) ->
      (try
         let e1' =
           inner global_regions constenv fundef_env ref_element e1 in
         Let((x,t),e1',e2)
       with
         Cant_parallelize ->
         let e2'=
           (match category_of e1 with
            |Create_array(size,y) ->
              (*yが配列だった場合gloval,regionから外す*)
              let global_regions'=x::(List.filter (fun x' ->x'<>y) global_regions) in
              inner global_regions' constenv fundef_env ref_element e2
            |Create_tuple(ys) ->
              let global_regions'=
                x::(List.filter (fun x' ->(not (List.mem x' ys))) global_regions) in
              inner global_regions' constenv fundef_env ref_element e2
            |Const(i) ->
              let constenv' = M.add x i constenv in
              inner global_regions constenv' fundef_env ref_element e2
            |Ref_elm(a) ->
              let ref_element' = M.add x a ref_element in
              inner global_regions constenv fundef_env ref_element' e2
            |_ ->inner global_regions constenv fundef_env ref_element e2
           ) in
         Let((x,t),e1,e2'))
    |Let_Ref((x,Type.Ref t'),e1,e2) ->
      let e2' = 
        if Type.include_array_ref t' then
          inner global_regions constenv fundef_env ref_element e2
                (*xはglobalregionに登録しない,*)
        else
          inner (x::global_regions) constenv fundef_env ref_element e2
      in
      Let_Ref((x,Type.Ref t'),e1,e2')
    |LetTuple(xts,y,e2) ->
      let e2'=
        inner global_regions constenv fundef_env ref_element e2
      in
      LetTuple(xts,y,e2')
    |IfLE(i,j,e1,e2) ->
      raise Cant_parallelize
    |IfEq(i,j,e1,e2) ->
      raise Cant_parallelize
    |ForLE(((i,a),(j,k),step),e) ->
      VarCatego.index_ref:=i;
      VarCatego.fundef_env:=fundef_env;
      Format.eprintf "\n\n%s :judging -----> @." fun_name;
      (try
        let (rw_graph,array_tree)=
          Mk_rw_graph.f global_regions constenv e in
        let may_same_env=Array_tree.mk_may_same_env array_tree in
        let accum_path_list=Rw_g.analyze may_same_env array_tree rw_graph in
        let accum_path_list' =
          List.map VarCatego.pospath2intlist accum_path_list in        
        let e',accum= Accum.f constenv fundef_env accum_path_list' e in
        para_accum:=accum;
        ForLE(((i,a),(j,k),step),e')

      with
      |Array_tree.Not_preserve(y,x) ->
        Format.eprintf "cannot parallelize this function:Not_preserve %s<-%s@." y x;
        raise Cant_parallelize
      |Mk_rw_graph.Side_effect ->
        Format.eprintf "cannot parallelize this function:side effect@.";
        raise Cant_parallelize
      |Rw_g.WAR(a,pos) ->
        Format.eprintf "cannot parallelize this function:WAR over loop@.";
        VarCatego.print_apos (a,pos);
        raise Cant_parallelize
      |Rw_g.RAW(a,pos) ->
        Format.eprintf "cannot parallelize this function:RAW over loop@.";
        VarCatego.print_apos (a,pos);
        raise Cant_parallelize
      |Accum.Not_simple ->
        Format.eprintf "cannot parallelize this function:(may accum)RAW over loop@.";
        raise Cant_parallelize
      )
    
    |_ -> raise Cant_parallelize
  in
  let e' =
    inner global_regions' constenv fundef_env M.empty e
  in
   {name=(fun_name,t);args=yts ; body=e'},!para_accum
        
      
let rec g global_regions  constenv fundef_env parallel_fun= function
  |LetRec({name=(x,t);args=_;body=e}as fundef,e2) ->
    if(loop_exit e)then
       try
         let fundef',accum =
           can_parallelize global_regions constenv fundef_env fundef in
         let parallel_fun'=(fundef',accum)::parallel_fun in
         g global_regions constenv (M.add x fundef fundef_env) parallel_fun' e2
       with
         Cant_parallelize ->
         g global_regions constenv (M.add x fundef fundef_env) parallel_fun e2
     else
       g global_regions constenv (M.add x fundef fundef_env)  parallel_fun e2
  |Let((x,t),e1,e2) ->
    (match category_of e1 with
     |Create_array(size,y) ->
       (*yが配列だった場合gloval,regionから外す*)
       let global_regions'=x::(List.filter (fun x' ->x'<>y) global_regions) in
       g global_regions' constenv fundef_env  parallel_fun e2
     |Create_tuple(ys) ->
       let global_regions'=
         x::(List.filter (fun x' ->(not (List.mem x' ys))) global_regions) in
       g global_regions' constenv fundef_env parallel_fun e2
     |Const(i) ->
       let constenv' = M.add x i constenv in
       g global_regions constenv' fundef_env parallel_fun e2
     |_ ->g global_regions constenv fundef_env parallel_fun e2)
  |Let_Ref((x,Type.Ref t'),e1,e2) ->
    if Type.include_array_ref t' then
      g global_regions constenv fundef_env parallel_fun e2
        (*xはglobalregionに登録しない*)
    else
      g (x::global_regions) constenv fundef_env parallel_fun e2
  |LetTuple(xts,y,e2) ->
    g global_regions constenv fundef_env parallel_fun e2
  |IfLE(i,j,e1,e2)|IfEq(i,j,e1,e2) ->
    let parallel_fun1 =
      g global_regions constenv fundef_env parallel_fun e1 in
    let parallel_fun2 = 
      g global_regions constenv fundef_env parallel_fun e2 in
    parallel_fun1@parallel_fun2
  |ForLE _ ->parallel_fun
  |_ -> parallel_fun
  
let choose_one parallel_funs =
  let numbered_list,_ =
    List.fold_left
      (fun (numbered_list,nth) x ->(numbered_list@[(nth,x)],nth+1))
      ([],0)
      parallel_funs
  in
  Format.eprintf "\n\nplease choose one function for parallelize...@.";
  (List.iter
    (fun (n,(fundef,accum)) ->
      let name = fst (fundef.name) in
      Format.eprintf "%d : %s@."  n name)
    numbered_list);
  let rec receive_ans () =
    try
      let ans = read_int () in
      List.assoc ans numbered_list
    with
     _ ->
      Format.eprintf "please choose number above@.";
      receive_ans ()
  in
  receive_ans ()
        
let subst_parallel newfundef parallel e =
  let rec inner =function
  |LetRec(fundef,e2) ->
    if(fundef.name=newfundef.name) then
      LetPara(parallel,
              LetRec(newfundef,e2))
    else
      LetRec(fundef,inner e2)
  |Let(xt,e1,e2) ->Let(xt,inner e1,inner e2)
  |LetTuple(xts,y,e2) ->LetTuple(xts,y,inner e2)
  |Let_Ref(xt,e1,e2) ->Let_Ref(xt,inner e1,inner e2)
  |IfLE(i,j,e1,e2) ->IfLE(i,j,inner e1,inner e2)
  |IfEq(i,j,e1,e2) ->IfEq(i,j,inner e1,inner e2)
  |ForLE(cs,e) ->ForLE(cs,inner e)
  |e ->e
  in
  inner e
        
  
let dummy = Id.genid "dummy"
let parallelize_fun = ref dummy

let f e=
  let parallel_funs=
    g [] M.empty M.empty [] e in
  if(parallel_funs<>[])then
    let parallel_fundef,accum=choose_one parallel_funs in
    (* accumの位置はVarCatego.elm_posを使って書かれている
   accumの位置は定数のパスになるのintを使った表現にする*)
    parallelize_fun:=fst (parallel_fundef.name);
  
    let (new_fundef',parallel)=Mk_parallel.f parallel_fundef accum in

    let e'=subst_parallel new_fundef' parallel e in(*fundef置き換え*)
    e'
  else
    e
  


