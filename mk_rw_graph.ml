open KNormal

exception Not_preserv
exception Side_effect

let find x var_category =
  try M.find x var_category with Not_found ->VarCatego.Unknown
            
let rec g rw_graph array_tree notW_hypothesis pre_written var_category trace
  =function
  (*var_category:id.t ->VarCatego.t
   arrayを含む型の変数はElm(a,n) or Tuple(xs)で登録
   それ以外は
   Int(i),Index(i),Float(d),Unknownのどれか*)
  |Get(a,n) ->
    let a=Array_tree.find a array_tree in
    let lavel=Rw_g.genlavel () in
    let category_of_n=find n var_category in
    let n_position=VarCatego.Array(category_of_n) in
    let rw_graph=Rw_g.add_read lavel (a,n_position) pre_written rw_graph in
    let hypo=NotW_hypo.set_elm_ans (a,n_position) notW_hypothesis in
    (rw_graph , array_tree , hypo , VarCatego.elm(a,n_position))
  |Ref_Get(a) when a=VarCatego.index_ref ->
    (rw_graph, array_tree, notw_hypothesis, VarCatego.Index(0))
  |Ref_Get(a) ->
    let a=Array_tree.find a array_tree in
    let lavel=Rw_g.genlavel () in
    let position=VarCatego.Ref in
    let rw_graph=Rw_g.add_read lavel (a,position) pre_written rw_graph in
    let hypo=NotW_hypo.set_elm_ans (a,position) notW_hypothesis in
    (rw_graph, region_tree, hypo, VarCatego.elm(a,postion))
  |Put(a,n, x) ->
    let a=Array_tree.find a array_tree in
    let cate_x=find x var_category in
    let cate_n=find n var_category in
    let n_pos=VarCatego.Array(cate_n) in
    let x=Array_tree.find x array_tree in
    let array_t'=Array_tree.put (a,n_pos,x) array_tree in
    let lavel=Rw_g.genlavel () in
    let rw_graph=Rw_g.add_write lavel (a,n_pos,x) pre_written rw_graph in
    let hypo=
      NotW_hypo.new_hypo (a,n_pos) cate_x lavel var_category notW_hypothesis
    in
    let hypo=NotW_hypo.set_all_ans VarCatego.Unit hypo in
    (rw_graph,array_t',hypo, VarCatego.Unit)

  |Ref_Put(a,x) ->
    let a=Array_tree.find a array_tree in
    let cate_x=find x var_category in
    let pos=VarCatego.Ref in
    let x=Array_tree.find x array_tree in
    let array_t'=Array_tree.put (a,n_pos,x) array_tree in    
    let lavel=Rw_g.genlavel () in
    let rw_graph=Rw_g.add_write lavel (a,pos,x) pre_written rw_graph in
    let hypo=
      NotW_hypo.new_hypo (a,n_pos) cate_x lavel var_category notW_hypothesis
    in
    let hypo=NotW_hypo.set_all_ans VarCatego.Unit hypo in
    (rw_graph,array_t',hypo, VarCatego.Unit)
  |Let((x,t),e1,e2) ->
    let (rw_g1,array_t1,hypo1,ans1)=
      g rw_graph array_tree notW_hypothesis pre_written var_category trace e1
    in
    let hypo=NotW_hypo.set_env_after_return var_category notW_hypothesis hypo1 in
    let hypo'=NotW_hypo.set_var2env x hypo in

    (match ans1 with
     |VarCatego.Elm(a,pos) ->(*xがarrayincludeならarray_treeに追加*)
       if Type.include_array_ref t then
         let array_t' = Array_tree.add_childe x (a,pos) array_t1 in
         g rw_g1 array_t' hypo' pre_written var_category trace e2
       else if (t=Type.Int||t=Type.Float)&&(a<>!(VarCatego.index_ref)) then(*xをtrace*)
         let trace' =S.add x trace in
         let rw_g'=Rw_g.add_trace_get (x,(a,pos)) rw_g1 in
         g rw_g' array_t1 hypo' pre_written var_category trace' e2
       else
         g rw_g1 array_t1 hypo' pre_written var_category trace e2
     |VarCatego.Parent(aps) ->
       let array_t'=Array_tree.add_parent x aps array_t1 in
       g rw_g1 array_t' hypo' pre_written var_category trace e2
     |VarCatego.Arraytree_var y ->
       let array_t'=Array_tree.add_env x y array_t1 in
       g rw_g1 array_t' hypo' pre_written var_category trace e2       
     |VarCatego.Trace_add(y,z)->
       let rw_g'=Rw_g.add_trace_add (x,(y,z)) rw_g1 in
       g rw_g' array_t1 hypo' pre_written var_category trace e2
     |_->
       let var_category'=M.add x ans1 var_category in
       g rw_g1 array_t1 hypo' pre_written var_category' trace e2)

  |Let_Ref((x,(Type.Ref t)),e1,e2) ->
    let (rw_g1,array_t1,hypo1,ans1)=
      g rw_graph array_tree notW_hypothesis pre_written var_category trace e1
    in
    let hypo=NotW_hypo.set_env_after_return var_category notW_hypothesis hypo1 in
    (match ans1 with
     |VarCatego.Elm(a,pos) ->
       if Type.include_array_ref t then
         let dummy=Id.genid "dummy" in(*a,posに位置する値を表すダミー*)
         let array_t'=Array_tree.add_childe dummy (a,pos) array_t1 in
         let array_t'=Array_tree.add_parent x [(dummy,VarCatego.Ref)] array_t' in
         g rw_g1 array_t' hypo  pre_written var_category trace e2
       else
         let array_t'=Array_tree.set_root [x] array_t1 in
         g rw_g1 array_t' hypo  pre_written var_category trace e2
     |VarCatego.Parent(aps) ->
       let dummy=Id.genid "dummy" in
       let array_t'=Array_tree.add_parent dummy aps array_t1 in
       let array_t'=Array_tree.add_parent x [(dummy,VarCatego.Ref)] array_t' in
       g rw_g1 array_t' hypo pre_written var_category trace e2
     |VarCatego.Arraytree_var y ->
       let array_t'=Array_tree.add_parent x [(y,VarCatego.Ref)] in
       g rw_g1 array_t' hypo pre_written var_category trace e2       
     |_ ->
       let array_t'=Array_tree.set_root [x] array_t1 in
       g rw_g1 array_t' hypo  pre_written var_category trace e2)

  |LetTuple(xts,y,e2) ->
    let y=Array_tree.find y array_tree in
    let (var_category',_)=
      List.fold_left
        (fun (var_category',nth) (x,t) ->
          if(Type.include_array_ref t) then
            (M.add x (VarCatego.Elm(y,VarCatego.Tuple(nth))) var_category',nth+1)
          else
            (var_category',nth+1)) 
        (var_category,0)
        xts
    in
    g rw_graph array_tree notW_hypothesis pre_written var_category' trace e2

  |LetRec({name=(x,t);args=yts ; body=e} as fundef,e2) ->
    VarCatego.fundef_env:=M.add x fundef !VarCatego.fundef_env;
    g rw_graph array_tree notW_hypothesis pre_written var_category trace e2 
          
  |IfLE(i,j,e1,e2) ->
    let hypo_goto =
      NotW_hypo.judge_witch_togo (i,j) (VarCatego.cmple) notW_hypothesis in
    let (pre_written1,pre_written2)=
      List.fold_left
        (fun (pre_written1,pre_written2) ((a,pos),(l,goto)) ->
          if(goto=0)then
            (pre_written1,pre_written2)
          else if(goto=1) then
            (*l以降(a,pos)がwrittenされていないという仮定の元でe1に分岐
             ->e2に分岐するなら、(a,pos)がl以降にwritten*)
            (pre_written1,((a,pos),l)::pre_written2)
          else if(goto=2) then
            (((a,pos),l)::pre_written1,pre_written2)
          else
            assert false)
        (pre_written,pre_written)
        hypo_goto
    in
    let (rw_g1,array_t1,hypo1,ans1)=
      g Rw_g.empty array_tree notW_hypothesis pre_written1 var_category trace e1
    in
    let (rw_g2,array_t2,hypo2,ans2)=
      g Rw_g.empty array_tree notW_hypothesis pre_written2 var_category trace e2
    in
    
    let (array_t',same_arrays)=Array_tree.union array_t1 array_t2 in
    let rw_g2'=Rw_g.subst_array same_arrays rw_g2 in
    let hypo2'=NotW_hypo.subst_array same_arrays hypo2 in
    let ans2'=VarCatego.subst same_arrays ans2 in

    let joint_l=Rw_g.genlavel ()in
    let rw_g'=Rw_g.add_branch rw_graph (rw_g1,rw_g2') joint_l in
    let hypo =
      NotW_hypo.change_hypo_after_if
        notW_hypothesis var_category joint_l hypo_goto hypo1 hypo2'
    in
    let hypo' =
      NotW_hypo.add_newhypo_after_if
        hypo var_category ans1 ans2' joint_l hypo1 hypo2'
    in
    let ans=if(ans1=ans2)then ans1 else VarCatego.Unknown in
    (rw_g',array_t',hypo',ans)
  |IfEq(i,j, e1, e2) ->(*ifLEに同じ*)
    let hypo_goto =
      NotW_hypo.judge_witch_togo (i,j) (VarCatego.cmpeq) notW_hypothesis in
    let (pre_written1,pre_written2)=
      List.fold_left
        (fun (pre_written1,pre_written2) ((a,pos),(l,goto)) ->
          if(goto=0)then
            (pre_written1,pre_written2)
          else if(goto=1) then
            (*l以降(a,pos)がwrittenされていないという仮定の元でe1に分岐
             ->e2に分岐するなら、(a,pos)がl以降にwritten*)
            (pre_written1,((a,pos),l)::pre_written2)
          else if(goto=2) then
            (((a,pos),l)::pre_written1,pre_written2)
          else
            assert false)
        (pre_written,pre_written)
        hypo_goto
    in
    let (rw_g1,array_t1,hypo1,ans1)=
      g Rw_g.empty array_tree notW_hypothesis pre_written1 var_category trace e1
    in
    let (rw_g2,array_t2,hypo2,ans2)=
      g Rw_g.empty array_tree notW_hypothesis pre_written2 var_category trace e2
    in
    
    let (array_t',same_arrays)=Array_tree.union array_t1 array_t2 in
    let rw_g2'=Rw_g.subst_array same_arrays rw_g2 in
    let hypo2'=NotW_hypo.subst_array same_arrays hypo2 in
    let ans2'=VarCatego.subst same_arrays ans2 in
    let joint_l=Rw_g.genlavel ()in
    let rw_g'=Rw_g.add_branch rw_graph (rw_g1,rw_g2') joint_l in
    let hypo =
      NotW_hypo.change_hypo_after_if
        notW_hypothesis var_category joint_l hypo_goto hypo1 hypo2'
    in
    let hypo' =
      NotW_hypo.add_newhypo_after_if
        hypo var_category ans1 ans2' joint_l hypo1 hypo2'
    in
    let ans=if(ans1=ans2)then ans1 else VarCatego.Unknown in
    (rw_g',array_t',hypo',ans)
      
  |App(f,xs) ->(*関数は追う*)
    if(f<>!VarCatego.fun_name) then
      let {name=_;args=yts;body=e} as fundef = M.find f !VarCatego.fundef_env in
      let env' =
	List.fold_left2
	  (fun env' (z, t) y -> M.add z y env')
	  M.empty
	  yts
	  xs in
      let e'= Alpha.g env' e in(*変数の重複を解消*)
      let unchanged_args_ys = For_check.search_unchanged_arg fundef in
      let unchanged_args_xs = List.map
                                (fun y ->M.find y env')
                                unchanged_args_ys in
      let index_ref_backup = !VarCatego.index_ref in
      (if(not (List.mem !VarCatego.index_ref unchanged_args_xs)) then
         VarCatego.index_ref:=VarCatego.dummy);

      let var_catego_in_f=(*不動引数に当たるものだけを残す*)
        List.fold_left
          (fun var_catego' x ->
            if(List.mem x unchanged_args_xs) then
              M.add x (M.find x var_category) var_catego'
            else
              M.add x VarCatego.Unknown var_catego')
          M.empty
          xs in
      let hypo_in_f =
        NotW_hypo.app_each_env
          (fun local_varcatego ->
            List.fold_left
              (fun var_catego' x ->
                if(List.mem x unchanged_args_xs) then
                  M.add x (M.find x local_varcatego) var_catego'
                else
                  M.add x VarCatego.Unknown var_catego')
              M.empty
              xs)　
          notW_hypothesis
      in
      let fun_name_backup=!VarCatego.fun_name in
      VarCatego.fun_name :=f;
      let (rw_g,array_t,hypo,ans)=
        g rw_graph array_tree hypo_in_f pre_written var_catego_in_f trace e'
      in
      VarCatego.fun_name := fun_name_backup;
      VarCatego.index_ref :=index_ref_backup;
      let hypo'=NotW_hypo.set_env_after_return var_category NotW_hypothesis hypo in
      (rw_g,array_t,hypo',ans)
    else(*自分自身の再帰だった場合*)
      (rw_graph,array_tree,notW_hypothesis,VarCatego.Unknown)
  |ForLE(((i,a),(j,k),step),e) ->
    let j'=if(j=i)then M.find a var_category else M.find j var_category in
    let k'=if(k=i)then M.find a var_category else M.find k var_category in
    (match VarCatego.cmple j' k' with
     |Some true ->(*少なくとも一回はループする*)
       g rw_graph array_tree notW_hypothesis pre_written var_category trace e
     |Some false ->
       (rw_graph,array_tree,notW_hypothesis,VarCatego.Unit)
     |None ->
       let (rw_g,array_t,hypo,ans) =
         g Rw_g.empty array_tree notW_hypothesis pre_written var_category trace e
       in
       let rw_g'=Rw_g.add_branch rw_graph (rw_g,Rw_g.empty) in
       (rw_g',array_t,hypo,ans))

  |ExtFunApp _|Read_int _|Read_float _|Print_char _ ->raise Side_effect

  |e ->let ans=Categorize.f array_tree var_category trace e in
       let hypo=NotW_hypo.categorize_set_ans array_tree trace e notW_hypothesis in
       (rw_graph,array_tree,hypo,ans)
                                                  
     
