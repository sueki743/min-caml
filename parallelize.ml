let rec loop_exit = function
    | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2)
      | Let(_, e1, e2) | LetRec({ body = e1 }, e2)|Let_Ref(_,e1,e2) ->
       (loop_exit e1)||(loop_exit e2)
    |LetTuple(_,_,e)->loop_exit e
    |ForLE _ ->true
    |_ ->false

      let array_tree=Array_tree.set_root gloval_arrays (Array_tree.empty) in
      let (rw_graph,array_tree,_,_)=
        g Rw_g.empty array_tree NotW_hypo.empty [] M.empty S.empty in

           
let g global_regions contenv =Array_tree.set_root gloval_arrays
  |LetRec({name=(x,t);args=_;body=e}as fundef,e2) ->
    (if(loop_exit e)then
      judge_paralleliable gloval_regions constenv fundef;
    else
      ());
    VarCatego.fundef_env:=M.add x fundef !VarCatego.fundef_env;
    g global_regions e2
  |Let((x,t),e1,e2) ->
    (match category_of e1 with
     |Create_array(size,y) ->
       (*yが配列だった場合gloval,regionから外す*)
       let global_regions'=x::(List.filter (fun x' ->x'<>y) global_regions) in
       g global_regions' constenv e2
     |Create_Tuple(ys) ->
       let gloval_regions'=
         x::(List.filter (fun x' ->(not (List.mem x' ys))) global_regions) in
       g global_regions' constenv e2
     |Const(i) ->
       let constenv' = M.add x i in
       g global_regions constenv' e2
     |_ ->g global_regions constenv e2)
  |Let_Ref((x,Type.Ref t'),e1,e2) ->
    if Type.include_array_ref t' then
      g gloval_regions constenv' e2(*xはglobalregionに登録しない*)
    else
      g (x::gloval_regions) constenv' e2
  |
      
