open KNormal

exception Not_preserve
exception Side_effect

let find x var_category =
  try M.find x var_category with Not_found ->VarCatego.Unknown

(*knormal.tの受け取って,自由変数を適切にrw_graphに加える*)
let add_read trace e pre_written rw_graph=
  let next_fv =(*直後に評価される自由変数*)
    match e with 
    |Let _|Let_Ref _|LetRec _ ->S.empty
    |LetTuple(_,y,_) ->S.singleton y
    |IfEq(x,y,_,_)|IfLE(x,y,_,_)->S.of_list [x;y]
    |ForLE(((i,a),(j,k),step),_) ->
      S.of_list (List.filter (fun x->x<>i) [j;k])
    |e' ->(KNormal.fv e')
  in
  S.fold
    (fun x (rw_g',trace') ->
      try
        let ((a,pos),was_read) = M.find x trace' in
        if(not was_read)then
          let l=Rw_g.genlavel ()in
          let rw_g'=Rw_g.add_read l (a,pos) pre_written rw_g'
          in
          let trace'=M.add x ((a,pos),true) trace' in
            (rw_g',trace')
        else
          (rw_g',trace')
        with
          Not_found ->(rw_g',trace'))
    next_fv
    (rw_graph,trace)           
                                               
let rec g rw_graph array_tree notW_hypothesis pre_written var_category trace e =
  (*配列から読み込んだ値が初めて直後に評価される場合は,read情報をrw_graphに登録*)
  let (rw_graph,trace)=add_read trace e pre_written rw_graph in
  
  match e with
    
  |Get(a,n) ->
    (* Format.eprintf "get(%s)@." a; *)
    let a=Array_tree.find a array_tree in
    let category_of_n=find n var_category in
    let n_position=VarCatego.Array(category_of_n) in
    let hypo=NotW_hypo.set_elm_ans (a,n_position) notW_hypothesis in
    (rw_graph , array_tree , hypo , VarCatego.Elm(a,n_position))
  |Ref_Get(a) when a= (!VarCatego.index_ref) ->(*index変数からget*)
    let pos = VarCatego.Ref in
    let hypo=NotW_hypo.set_elm_ans (a,pos) notW_hypothesis in   
    (rw_graph, array_tree,hypo, VarCatego.Index(0))
  |Ref_Get(a) ->
     (* Format.eprintf "ref_get(%s)@." a;  *)
     
    let a=Array_tree.find a array_tree in
    let position=VarCatego.Ref in
    let hypo=NotW_hypo.set_elm_ans (a,position) notW_hypothesis in
    (rw_graph, array_tree, hypo, VarCatego.Elm(a,position))
  |Put(a,n, x) ->
    
    let a=Array_tree.find a array_tree in
    let cate_x=find x var_category in
    let cate_n=find n var_category in
    let n_pos=VarCatego.Array(cate_n) in
    let x=Array_tree.find x array_tree in
    let array_t'=Array_tree.put (a,n_pos,x) array_tree in
    let lavel=Rw_g.genlavel () in
    let rw_graph=Rw_g.add_write lavel (a,n_pos,x) pre_written rw_graph in
    (* (if (a,n_pos)=("solver_dist.256",VarCatego.Array(VarCatego.Int(0))) then *)
    (*    Format.eprintf "solver_dist put!!!!!!!!!!!!!!!!!@."); *)
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
    let array_t'=Array_tree.put (a,pos,x) array_tree in    
    let lavel=Rw_g.genlavel () in
    let rw_graph=Rw_g.add_write lavel (a,pos,x) pre_written rw_graph in
    let hypo=
      NotW_hypo.new_hypo (a,pos) cate_x lavel var_category notW_hypothesis
    in
    let hypo=NotW_hypo.set_all_ans VarCatego.Unit hypo in
    (rw_graph,array_t',hypo, VarCatego.Unit)
  |Let((x,t),e1,e2) ->
    (* Format.eprintf "let@."; *)
    let (rw_g1,array_t1,hypo1,ans1)=
      g rw_graph array_tree notW_hypothesis pre_written var_category trace e1
    in
    let hypo=NotW_hypo.set_env_after_return var_category notW_hypothesis hypo1 in
    let hypo'=NotW_hypo.set_var2env x hypo in

    (match ans1 with
     |VarCatego.Elm(a,pos) ->(*xがarrayincludeならarray_treeに追加*)
       let trace'=M.add x ((a,pos),false) trace in
       if Type.include_array_ref t then
         (let array_t' = Array_tree.add_childe x (a,pos) array_t1 in
          (* Format.eprintf "add_array_tree:%s,num=%d,env_num=%d@." x (Array_tree.num array_t') (Array_tree.env_num array_t'); *)
         g rw_g1 array_t' hypo' pre_written var_category trace' e2)
       else if (t=Type.Int||t=Type.Float)&&(a<> !(VarCatego.index_ref)) then(*xをtrace*)
         let rw_g'=Rw_g.add_trace_get (x,(a,pos)) rw_g1 in
         g rw_g' array_t1 hypo' pre_written var_category trace' e2
       else
         g rw_g1 array_t1 hypo' pre_written var_category trace' e2
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
       let l=Rw_g.genlavel () in
       let rw_g1'=Rw_g.add_read  l (a,pos) pre_written rw_g1 in
       if Type.include_array_ref t then
         let dummy=Id.genid "dummy" in(*a,posに位置する値を表すダミー*)
         let array_t'=Array_tree.add_childe dummy (a,pos) array_t1 in
         let array_t'=Array_tree.add_parent x [(VarCatego.Ref,dummy)] array_t' in
         g rw_g1' array_t' hypo  pre_written var_category trace e2
       else
         let array_t'=Array_tree.set_root [x] array_t1 in
         g rw_g1' array_t' hypo  pre_written var_category trace e2
     |VarCatego.Parent(aps) ->
       let dummy=Id.genid "dummy" in
       let array_t'=Array_tree.add_parent dummy aps array_t1 in
       let array_t'=Array_tree.add_parent x [(VarCatego.Ref,dummy)] array_t' in
       g rw_g1 array_t' hypo pre_written var_category trace e2
     |VarCatego.Arraytree_var y ->
       let array_t'=Array_tree.add_parent x [(VarCatego.Ref,y)] array_t1 in
       g rw_g1 array_t' hypo pre_written var_category trace e2       
     |_ ->
       let array_t'=Array_tree.set_root [x] array_t1 in
       g rw_g1 array_t' hypo  pre_written var_category trace e2)

  |LetTuple(xts,y,e2) ->
    let y=Array_tree.find y array_tree in
    let (array_tree',_)=(*xtsのうちarray含む型はarray_treeに登録*)
      List.fold_left
        (fun (array_tree',nth) (x,t) ->
          if(Type.include_array_ref t) then
            let pos=VarCatego.Tuple(nth) in
            (Array_tree.add_childe x (y,pos) array_tree',nth+1)
          else
            (array_tree',nth+1)) 
        (array_tree,0)
        xts
    in
    let hypo=NotW_hypo.set_all_ans VarCatego.Unit notW_hypothesis in
    g rw_graph array_tree' hypo pre_written var_category trace e2

  |LetRec({name=(x,t);args=yts ; body=e} as fundef,e2) ->
    VarCatego.fundef_env:=M.add x fundef !VarCatego.fundef_env;
    g rw_graph array_tree notW_hypothesis pre_written var_category trace e2 
          
  |IfLE(i,j,e1,e2) ->
    (* Format.eprintf "ifle@."; *)
    (*  NotW_hypo.print ("solver_dist.256",VarCatego.Array(VarCatego.Int(0))) notW_hypothesis;  *)
    
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

    let joint_l=Id.genid "join"in
    let rw_g'=Rw_g.add_branch rw_graph (rw_g1,rw_g2') joint_l in
     (* Format.eprintf "pre_size:%d" (List.length pre_written);  *)
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
    (* Format.eprintf "ifeq@."; *)
    (*  NotW_hypo.print ("solver_dist.256",VarCatego.Array(VarCatego.Int(0))) notW_hypothesis;  *)

    let hypo_goto =
      NotW_hypo.judge_witch_togo (i,j) (VarCatego.cmpeq) notW_hypothesis in
    let (pre_written1,pre_written2)=
      List.fold_left
        (fun (pre_written1,pre_written2) ((a,pos),(l,goto)) ->
          if(goto=0)then
            (pre_written1,pre_written2)
          else if(goto=1) then
            (
              (* Format.eprintf "add_prewritten2@.";VarCatego.print_apos (a,pos); *)
            (*l以降(a,pos)がwrittenされていないという仮定の元でe1に分岐
             ->e2に分岐するなら、(a,pos)がl以降にwritten*)
            (pre_written1,((a,pos),l)::pre_written2))
          else if(goto=2) then
            (
              (* Format.eprintf "add_prewritten1@.";VarCatego.print_apos (a,pos); *)
            (((a,pos),l)::pre_written1,pre_written2))
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
    let joint_l=Id.genid "join" in
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
    if(f<> !VarCatego.fun_name) then
      (
        (* Format.eprintf "function:%s@." f; *)
      assert (M.mem f (!VarCatego.fundef_env));
    let {name=_;args=yts;body=e} as fundef = M.find f !VarCatego.fundef_env in
      let env' =
	List.fold_left2
	  (fun env' (y, t) x -> M.add y x env')
	  M.empty
	  yts
	  xs in
      let e'= Alpha.g env' e in(*変数の重複を解消*)
      let unchanged_args_ys = For_check.search_unchanged_arg fundef in
      let unchanged_args_xs = List.map
                                (fun y ->assert (M.mem y env');M.find y env')
                                unchanged_args_ys in
      let index_ref_backup = !VarCatego.index_ref in
      
      (if(not (List.mem !VarCatego.index_ref unchanged_args_xs)) then
         VarCatego.index_ref:=VarCatego.dummy);
      let var_catego_in_f=(*不動引数に当たるものだけを残す*)
        List.fold_left
          (fun var_catego' x ->
            if(List.mem x unchanged_args_xs) then
              M.add x (find x var_category) var_catego'
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
                  M.add x (find x local_varcatego) var_catego'
                else
                  M.add x VarCatego.Unknown var_catego')
              M.empty
              xs)
          notW_hypothesis
      in
      let fun_name_backup= !(VarCatego.fun_name) in
      (VarCatego.fun_name :=f);
       let (rw_g,array_t,hypo,ans)=
        g rw_graph array_tree hypo_in_f pre_written var_catego_in_f M.empty e'
      in
      ( (* NotW_hypo.print ("solver_dist.256",VarCatego.Array(VarCatego.Int(0))) hypo;  *)
        (*  Format.eprintf "function_return    : %s@." f;    *)
      (*  (match ans with *)
      (*     VarCatego.Int(i) ->Format.eprintf "%d@." i *)
      (*   |_ ->Format.eprintf "other@."); *)
      VarCatego.fun_name := fun_name_backup;
      VarCatego.index_ref :=index_ref_backup;
      let hypo'=NotW_hypo.set_env_after_return var_category notW_hypothesis hypo in
      (rw_g,array_t,hypo',ans)))
    else(*自分自身の再帰だった場合*)
      (rw_graph,array_tree,notW_hypothesis,VarCatego.Unknown)
  |ForLE(((i,a),(j,k),step),e) ->
    let j'=if(j=i)then find a var_category else find j var_category in
    let k'=if(k=i)then find a var_category else find k var_category in
    (match VarCatego.cmple j' k' with
     |Some true ->(*少なくとも一回はループする*)
       g rw_graph array_tree notW_hypothesis pre_written var_category trace e
     |Some false ->
       (rw_graph,array_tree,notW_hypothesis,VarCatego.Unit)
     |None ->
       let (rw_g,array_t,hypo,ans) =
         g Rw_g.empty array_tree notW_hypothesis pre_written var_category trace e
       in
       let joint_lavel=Rw_g.genlavel ()in
       let rw_g'=Rw_g.add_branch rw_graph (rw_g,Rw_g.empty) joint_lavel in
       (rw_g',array_t,hypo,ans))

  |ExtFunApp _|Read_int _|Read_float _|Print_char _ ->raise Side_effect

  |e ->let ans=Categorize.f array_tree var_category trace e in
       let hypo=NotW_hypo.categorize_set_ans array_tree trace e notW_hypothesis in
       (rw_graph,array_tree,hypo,ans)
                                                  
let f global_regions constenv e=
  let array_tree=Array_tree.set_root global_regions (Array_tree.empty) in
  let var_category=
    M.map (fun const ->Categorize.f array_tree M.empty M.empty const) constenv
  in
  let (rw_graph,array_tree,_,_)=
    g Rw_g.empty array_tree NotW_hypo.empty [] var_category M.empty e in
  let rw_graph = Rw_g.add_dummy rw_graph in (* 末尾に空ノードを足す *)
  (rw_graph,array_tree)

