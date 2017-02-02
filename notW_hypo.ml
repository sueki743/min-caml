
(*仮定の元の帰結を表す型*)
type conseq={value:VarCatego.t ; env:(VarCatego.t) M.t ; anser:VarCatego.t}

type t = ((Id.t*VarCatego.elm_pos)*((Rw_g.lavel)* conseq)) list
(*[(a,n),(lavel,conseq) ; (b,m),(lavel,conseq)... ]*)
let find x env = try M.find x env with Not_found ->x
let empty=[]
let size hypo = List.length hypo
let subst_array env hypothesis =
  List.map
    (fun ((a,pos),(l,{value=x; env=var_category ; anser=ans})) ->
      ((find a env,pos),
       (l,{value=VarCatego.subst env x;env=var_category;anser=VarCatego.subst env ans})))
    hypothesis

let print (a,pos) hypothesis =
  Format.eprintf "hypo...@.";
  VarCatego.print_apos (a,pos);
  try
    let (l,{value=x;env=_;anser=ans}) = List.assoc (a,pos) hypothesis in
    (match ans with
     |VarCatego.Int (i) ->Format.eprintf "%d@." i
     |VarCatego.Float(d) ->Format.eprintf "%f@." d
     |VarCatego.Unknown ->Format.eprintf "unkown@."
     |_ ->Format.eprintf "other@.")
  with
    Not_found ->Format.eprintf "not_found@."
    
let overwrite'  ((a,pos),new_state) hypothesis =
  let hypo=(* List.remove_assoc (a,pos) hypothesis  *)
    List.filter (fun ((a',pos'),_) ->(a',pos')<>(a,pos)) hypothesis
  in
  ((a,pos),new_state)::hypo


let set_ans (a,pos) ans hypothesis=
  (*ansをそのままset,(a,pos)がhypoに含まれている前提*)
  let (l,{value=x ; env=var_category ; anser=_})=List.assoc (a,pos) hypothesis in
  overwrite' ((a,pos),(l,{value=x ; env=var_category ; anser=ans})) hypothesis

(*新しい仮定の登録*)
let new_hypo (a,pos) x lavel var_category hypothesis =
  overwrite'
    ((a,pos),
     (lavel,{value=x;env=var_category;anser=VarCatego.Unknown})) hypothesis

let set_all_ans ans hypothesis=
  List.map
    (fun ((a,pos),(l,{value=x ; env=var_category ; anser=_})) ->
      ((a,pos),(l,{value=x ; env=var_category ; anser=ans})))
    hypothesis

(*aの中身を各ansにset*)
let set_elm_ans(a,pos) hypothesis =
  List.map
    (fun ((a',pos'),(l,{value=x ; env=var_category ; anser=ans})) ->
      if(a,pos)=(a',pos')then
        ((a',pos'),(l,{value=x ; env=var_category ; anser=x}))
      else
        ((a',pos'),(l,{value=x ; env=var_category ; anser=VarCatego.Elm(a,pos)})))
    hypothesis

(*各仮定の元でansを計算*)
let categorize_set_ans  array_tree trace e hypothesis=
  List.map
    (fun ((a,pos),(l,{value=x ; env=var_category ; anser=_})) ->
      let ans=Categorize.f array_tree var_category trace e in
      ((a,pos),(l,{value=x ; env=var_category;anser=ans})))
    hypothesis

    
let set_var2env x hypothesis =
  List.map
    (fun ((a,pos),(l,{value=v ; env=var_category ; anser=ans})) ->
      ((a,pos),(l,{value=v ; env=M.add x ans var_category;anser=VarCatego.Unknown})))
    hypothesis

(*let set_env (a,pos) var_category hypothesis=
  (*envをそのままset,(a,pos)がhypoに含まれている前提*)
  let (l,{value=x ; env=_ ; anser=ans})=List.assoc (a,pos) hypothesis in
  overwrite' ((a,pos),(l,{value=x ; env=var_category ; anser=ans})) hypothesis

let set_all_env var_category hypothesis =
  List.map
    (fun ((a,pos),(l,{value=x ; env=_ ; anser=ans})) ->
      ((a,pos),(l,{value=x ; env=var_category ; anser=ans})))
    hypothesis*)

let app_each_env f hypothesis =
  List.map
    (fun ((a,pos),(l,{value=x ; env=var_category ; anser=ans})) ->
      ((a,pos),(l,{value=x ; env=f var_category ; anser=ans})))
    hypothesis

(*returnされた、hypothesisに対して、内部のenvを適切に設定する
hypothesisが変更してなかったら昔のenvを
変更または新しく出来てたら,global_vcategoを*)             
let set_env_after_return global_vcatego hypo_before hypo_return  =
  List.map
    (fun ((a,pos),(l,{value=x ; env=local_v_catego ; anser=ans}))->
      if(List.mem_assoc (a,pos) hypo_before) then
        let (l_before,{value=_;env=v_catego_before;anser=_}) =
          List.assoc (a,pos) hypo_before in
        if(l=l_before) then(*変更なし*)
            ((a,pos),(l,{value=x ; env=v_catego_before ; anser=ans}))
        else
          ((a,pos),(l,{value=x ; env=global_vcatego ; anser=ans}))
      else
          ((a,pos),(l,{value=x ; env=global_vcatego ; anser=ans})))
    hypo_return


      
let find_cate a var_category = try M.find a var_category with Not_found ->VarCatego.Unknown
(*各仮定のもとで、どちらに分岐するか判定*)
let judge_witch_togo (i,j) cmp hypothesis =
  List.map
    (fun ((a,pos),(l,{value=x ; env=var_category ; anser=_})) ->
      let i_cate=find_cate i var_category in
      let j_cate=find_cate j var_category in
      (match cmp i_cate j_cate with
       |Some true ->
          (* Format.eprintf "if %s unwritten goto 1!\n\n" a;  *)
         ((a,pos),(l,1))
       |Some false->
          (* Format.eprintf "if %s unwritten goto 2!\n\n" a;  *)
         ((a,pos),(l,2))
       |None ->((a,pos),(l,0))))
    hypothesis

(*hypo_beforeにある仮定->hypo1,hypo2にもある*)
let change_hypo_after_if hypo_before v_catego joint_l hypo_goto hypo1 hypo2 =
  (List.map
    (fun ((a,pos),(l,{value=x ; env=local_v_catego ; anser=ans})) ->
      let (_,goto)=List.assoc (a,pos) hypo_goto in
      let (l1,{value=x1;env=_;anser=ans1}) =List.assoc (a,pos) hypo1 in
      let (l2,{value=x2;env=_;anser=ans2}) =List.assoc (a,pos) hypo2 in
      if(goto=0)then
        if(l1<>l&&l2<>l)then
          let x'=if(x1=x2)then x1 else VarCatego.Unknown in
          let ans'=if(ans1=ans2)then ans1 else VarCatego.Unknown in
          ((a,pos),
           (joint_l,{value=x';env=v_catego;anser=ans'}))
        else if(l1<>l&&l2=l) then
          ((a,pos),
           (l,{value=x ; env=local_v_catego ; anser=ans2}))
        else if(l1=l&&l2<>l) then
          ((a,pos),
           (l,{value=x ; env=local_v_catego ; anser=ans1}))
        else(*l1=l2=l*)
          let ans'=if(ans1=ans2)then ans1 else VarCatego.Unknown in
          ((a,pos),
           (l,{value=x ; env=local_v_catego ; anser=ans'}))
            
      else if(goto=1) then
        if(l1<>l)then
            ((a,pos),
            (joint_l,{value=x1;env=v_catego;anser=ans1}))
        else
          ((a,pos),
           (l,{value=x1;env=local_v_catego;anser=ans1}))
      else if goto=2 then
        if(l2<>l) then
          ((a,pos),
           (joint_l,{value=x2;env=v_catego;anser=ans2}))
        else
          ((a,pos),
           (l,{value=x2;env=local_v_catego;anser=ans2}))
            
      else
        assert false)
    hypo_before)

let add_newhypo_after_if hypo_before v_catego a1 a2  joint_l hypo1 hypo2 =
  let new_hypo1=List.filter
                  (fun ((a,pos),_) ->not (List.mem_assoc (a,pos) hypo_before))
                  hypo1
  in
  let new_hypo2=List.filter
                  (fun ((a,pos),_) ->not (List.mem_assoc (a,pos) hypo_before))
                  hypo2
  in
  let newhypo=new_hypo1@(List.filter (fun x ->not (List.mem x new_hypo1)) new_hypo2) in
  (* Format.eprintf "new1=%d,new2=%d" (List.length new_hypo1) (List.length new_hypo2); *)
  List.fold_left
    (fun hypo_after ((a,pos),_) ->
      if(List.mem_assoc (a,pos) new_hypo1&&List.mem_assoc (a,pos) new_hypo2) then
        let (l1,{value=x1;env=_;anser=ans1}) =List.assoc (a,pos) new_hypo1 in
        let (l2,{value=x2;env=_;anser=ans2}) =List.assoc (a,pos) new_hypo2 in
        let x'=if(x1=x2)then x1 else VarCatego.Unknown in
        let ans'=if(ans1=ans2) then ans1 else VarCatego.Unknown in
        (if(l1=Rw_g.start_l&&l2=Rw_g.start_l)then
           overwrite'
             ((a,pos),
              (Rw_g.start_l,
               {value=x';env=v_catego;anser=ans'}))
             hypo_after
         else if(l1=Rw_g.start_l&&l2<>Rw_g.start_l) then
           (*l2で(a,pos)がwritten,1の方はtopからunwrittenの経路あり*)
           overwrite'
             ((a,pos),
              (Rw_g.start_l,
               {value=x1;env=v_catego;anser=ans1}))
             hypo_after
         else if(l1<>Rw_g.start_l&&l2=Rw_g.start_l) then
           overwrite'
             ((a,pos),
              (Rw_g.start_l,
               {value=x2;env=v_catego;anser=ans2}))
             hypo_after
         else
           overwrite'
             ((a,pos),
              (joint_l,
               {value=x';env=v_catego;anser=ans'}))
             hypo_after)
          
      else if(List.mem_assoc (a,pos) new_hypo1) then(*hypo2に(a,pos)ない*)
        let (l1,{value=x1;env=_;anser=ans1}) =List.assoc (a,pos) new_hypo1 in
      
        (if(l1=Rw_g.start_l) then
           let ans'=if(ans1=a2)then ans1 else VarCatego.Unknown in
           (* Format.eprintf "l1=start l2 -non\n"; *)
           overwrite'
             ((a,pos),
              (Rw_g.start_l,
               {value=VarCatego.Unknown;env=v_catego;anser=ans'}))
             hypo_after
         else(*l1で初めて(a,pos)がwritten*)
           
           (*トップからの(a,pos)のunwrittenの仮定を登録,仮定の元のansはif文のe2のans*)
           (
             (* Format.eprintf "l1=written l2 non\n"; *)
            overwrite'
              ((a,pos),
               (Rw_g.start_l,
                {value=VarCatego.Unknown;env=v_catego;anser=a2}))
              hypo_after))
      else if(List.mem_assoc (a,pos) new_hypo2) then
        let (l2,{value=x2;env=_;anser=ans2}) =List.assoc (a,pos) new_hypo2 in
        (if(l2=Rw_g.start_l) then
           let ans'=if(ans2=a1)then ans2 else VarCatego.Unknown in
           (* Format.eprintf "l1=non l2 -start\n"; *)
           overwrite'
             ((a,pos),
              (Rw_g.start_l,
               {value=VarCatego.Unknown;env=v_catego;anser=ans'}))
             hypo_after
         else
           
           
           (
             (* Format.eprintf "l1 non l2 written@." ; *)
            overwrite'
              ((a,pos),
               (Rw_g.start_l,
                {value=VarCatego.Unknown;env=v_catego;anser=a1}))
              hypo_after))
      else
        assert false)
    hypo_before
    newhypo

        


                                                       
                                                       
                     
