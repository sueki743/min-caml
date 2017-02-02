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

(*forloopを含むfundefを受け取り、Mk_rw_graph.f で読み書きのフローグラフを作成し、Analyze_rw_graph.fで依存関係を解析する *)
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
                                             
  let rec inner global_regions constenv fundef_env ref_element = function(*ref_elementいらなかった*)
    |LetRec({name=(x,t);args=_;body=e}as fundef,e2) ->(*局所関数*)
      if (S.mem fun_name (fv e)) then(*局所関数を介して再帰*)
        ()
      else
        inner global_regions constenv (M.add x fundef fundef_env) ref_element e2
    |Let((x,t),e1,e2) ->
      inner global_regions constenv fundef_env ref_element e1;
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
      )
    |Let_Ref((x,Type.Ref t'),e1,e2) ->
      if Type.include_array_ref t' then
        inner global_regions constenv fundef_env ref_element e2
              (*xはglobalregionに登録しない,*)
      else
        inner (x::global_regions) constenv fundef_env ref_element e2
    |LetTuple(xts,y,e2) ->
      inner global_regions constenv fundef_env ref_element e2
    |IfLE(i,j,e1,e2) ->
      ()
    |IfEq(i,j,e1,e2) ->
      ()
    |ForLE(((i,a),(j,k),step),e) ->
      VarCatego.index_ref:=i;
      VarCatego.fundef_env:=fundef_env;
      Format.eprintf "\n\n%s :judging -----> @." fun_name;
      (try
        let (rw_graph,array_tree)=
          Mk_rw_graph.f global_regions constenv e in
        let may_same_env=Array_tree.mk_may_same_env array_tree in
        let _=Rw_g.analyze may_same_env array_tree rw_graph in
        ()
      with
      |Array_tree.Not_preserve(y,x) ->
        Format.eprintf "cannot parallelize this function:Not_preserve %s<-%s@." y x
      |Mk_rw_graph.Side_effect ->
        Format.eprintf "cannot parallelize this function:side effect@."
      |Rw_g.WAR(a,pos) ->
        Format.eprintf "cannot parallelize this function:WAR over loop@.";
        VarCatego.print_apos (a,pos)
      |Rw_g.RAW(a,pos) ->
        Format.eprintf "cannot parallelize this function:RAW over loop@.";
        VarCatego.print_apos (a,pos)
      )
    
    |_ -> ()
  in
  inner global_regions' constenv fundef_env M.empty e
        
      
let rec g global_regions  constenv fundef_env = function
  |LetRec({name=(x,t);args=_;body=e}as fundef,e2) ->
    (if(loop_exit e)then
      can_parallelize global_regions constenv fundef_env fundef
    else
      () );
    g global_regions constenv (M.add x fundef fundef_env)  e2
  |Let((x,t),e1,e2) ->
    (match category_of e1 with
     |Create_array(size,y) ->
       (*yが配列だった場合gloval,regionから外す*)
       let global_regions'=x::(List.filter (fun x' ->x'<>y) global_regions) in
       g global_regions' constenv fundef_env  e2
     |Create_tuple(ys) ->
       let global_regions'=
         x::(List.filter (fun x' ->(not (List.mem x' ys))) global_regions) in
       g global_regions' constenv fundef_env e2
     |Const(i) ->
       let constenv' = M.add x i constenv in
       g global_regions constenv' fundef_env e2
     |_ ->g global_regions constenv fundef_env e2)
  |Let_Ref((x,Type.Ref t'),e1,e2) ->
    if Type.include_array_ref t' then
      g global_regions constenv fundef_env e2
        (*xはglobalregionに登録しない*)
    else
      g (x::global_regions) constenv fundef_env e2
  |LetTuple(xts,y,e2) ->
    g global_regions constenv fundef_env e2
  |IfLE(i,j,e1,e2) ->
    g global_regions constenv fundef_env e1;
    g global_regions constenv fundef_env e2
  |IfEq(i,j,e1,e2) ->
    g global_regions constenv fundef_env e1;
    g global_regions constenv fundef_env e2
  |ForLE _ ->()
  |_ -> ()

let f e=(g [] M.empty M.empty e);e
