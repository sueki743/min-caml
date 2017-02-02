

let counter=ref 0
                
let genlavel ()=
  incr counter;
  Printf.sprintf "l%d" !counter

type lavel=Id.t
let top_l = genlavel ()(*グラフ以前の表すラベル*)
let start_l = genlavel ()(*グラフ先頭のラベル*)
type read_write =
  |Read of Id.t * VarCatego.elm_pos
  |Write of Id.t *VarCatego.elm_pos *Id.t
  |Trace_Get of Id.t *(Id.t*VarCatego.elm_pos)
  |Trace_Add of Id.t *(Id.t*Id.t)
  |Not
                    
type pre_written_t=((Id.t*VarCatego.elm_pos)*lavel ) list

type next_lavel =
  |Seq of lavel
  |Branch of (lavel*lavel)*lavel (*各分岐のスタート,合流地点 *)
  |No_next
                             
type node ={ rw:read_write ; pre_w:pre_written_t ; next:next_lavel }


             
type t={graph:( node M.t) ; end_l:lavel }
(*ラベルからnodeへのmapでグラフを表現*)

let find x env =try M.find x env with Not_found ->x
         
let subst_array_read_write env = function
  |Read(a,pos) ->Read(find a env,pos)
  |Write(a,pos,x) ->Write(find a env,pos ,find x env)
  |Trace_Get(x,(a,pos)) ->Trace_Get(x,(find a env,pos))
  |e ->e

(*array型の変数の代入*)
let subst_array env {graph=g;end_l=el} =
  let g'=
  M.map
    (fun  {rw=read_write;pre_w=pre;next=next_l} ->
      let read_write'=subst_array_read_write env read_write in
      let pre'=List.map (fun ((a,pos),l) ->((find a env,pos),l)) pre in
      {rw=read_write';pre_w=pre';next=next_l})
    g in
  {graph=g' ; end_l=el}
         
let empty=
  let start_node = {rw=Not ; pre_w=[] ; next=No_next} in
  {graph=(M.add start_l start_node (M.empty)) ; end_l=start_l}

let is_empty {graph=_;end_l=el} = (el=start_l)

let set_rw l read_write g=
  if(not (M.mem l g)) then (Format.eprintf "%s@." l;assert false)
  else
  let {rw=_;pre_w=pre;next=next_l}=M.find l g in
  (M.add l {rw=read_write;pre_w=pre;next=next_l} g)
                                    
let set_children l children  g=
  let {rw=read_write;pre_w=pre;next=_}=M.find l g in
  (M.add l {rw=read_write;pre_w=pre;next=children} g)

let change_lavel_name before_l after_l g =
  let node = M.find before_l g in
  M.add after_l node (M.remove before_l g)
                                    
                                    
let add_read new_lavel (a,pos) pre_written {graph=g;end_l=el} =
  
  let g'=set_children el (Seq(new_lavel)) g in
  let g''
    =M.add new_lavel  {rw=Read(a,pos);pre_w=pre_written;next=No_next} g'
  in
  { graph=g'' ; end_l=new_lavel }

let add_write new_lavel (a,pos,x) pre_written {graph=g;end_l=el} =
  let g'=set_children el (Seq(new_lavel)) g in
  let g''
    =M.add new_lavel {rw=Write(a,pos,x);pre_w=pre_written;next=No_next} g'
  in
  { graph=g'' ; end_l=new_lavel}

let add_trace_add (x,(y,z)) {graph=g;end_l=el} =
  (* Format.eprintf "addtarce_add!!!!!!!!!!!!!!!!!!!!!!!!%s+%s@." x y; *)
  let new_lavel=genlavel () in
  let g'=set_children el (Seq(new_lavel)) g in
  let g''
    =M.add new_lavel {rw=Trace_Add(x,(y,z));pre_w=[];next=No_next} g'
  in
  { graph=g'' ; end_l=new_lavel}

let add_trace_get (x,(a,pos)) {graph=g;end_l=el} =
  (* Format.eprintf "addtarce_get!!!!!!!!!!!!!!!!!!!!!!!!%s@." x; *)
  (* VarCatego.print_apos (a,pos); *)
  let new_lavel=genlavel () in
  let g'=set_children el (Seq(new_lavel)) g in
  let g''
    =M.add new_lavel {rw=Trace_Get(x,(a,pos));pre_w=[];next=No_next} g'
  in
  { graph=g'' ; end_l=new_lavel}
    

    
let add_branch rw_g (rw_g1,rw_g2) joint_l =
  let {graph=g;end_l=e_l} = rw_g in
  let {graph=g1;end_l=e_l1} = rw_g1 in
  let {graph=g2;end_l=e_l2} = rw_g2 in
  if (not ((is_empty rw_g1)||(is_empty rw_g2))) then
    let start1 = genlavel () in
    let start2 = genlavel () in
    let g1'=change_lavel_name start_l start1 g1 in
    let g1'=set_children e_l1 (Seq(joint_l)) g1' in
    let g2'=change_lavel_name start_l start2 g2 in
    let g2'=set_children e_l2 (Seq(joint_l)) g2' in
    let g' = set_children e_l (Branch((start1,start2),joint_l)) g in

    let g1_g2 =M.union
                 (fun lavel n1 n2 ->assert (false))
                 g1'
                 g2' in
    let new_g=M.union
                (fun lavel n1 n2 ->assert false)
                g'
                g1_g2 in
    let new_g=M.add joint_l {rw=Not;pre_w=[];next=No_next} new_g in
    {graph=new_g;end_l=joint_l}
  else if (is_empty rw_g1&&(not (is_empty rw_g2))) then
    let start2=genlavel () in
    let g2'=change_lavel_name start_l start2 g2 in
    let g2'=set_children e_l2 (Seq(joint_l)) g2' in
    let g' = set_children e_l (Branch((joint_l,start2),joint_l)) g in    

    let new_g=M.union
                (fun lavel n n2 ->assert false)
                g'
                g2' in
    let new_g=M.add joint_l {rw=Not;pre_w=[];next=No_next} new_g in
    {graph=new_g;end_l=joint_l}
  else if ((not (is_empty rw_g1))&&is_empty rw_g2) then
    let start1=genlavel () in
    let g1'=change_lavel_name start_l start1 g1 in
    let g1'=set_children e_l1 (Seq(joint_l)) g1' in
    let g' = set_children e_l (Branch((start1,joint_l),joint_l)) g in    

    let new_g=M.union
                (fun lavel n n2 ->assert false)
                g'
                g1' in
    let new_g=M.add joint_l {rw=Not;pre_w=[];next=No_next} new_g in
    {graph=new_g;end_l=joint_l}

  else(*is_empty rw_g1&&is_empty rw_g2*)
    rw_g(*変更なし*)

let may_same env (a,pos) (a',pos') =
  assert (M.mem a env);
  let may_same_a = M.find a env in
  let unknown=VarCatego.Array(VarCatego.Unknown) in
  if(List.mem a' (a::may_same_a)) then
    ((pos=pos')
     ||(pos=unknown||pos'=unknown)
     ||((VarCatego.is_intpos pos)&&(VarCatego.is_indexpos pos'))
     ||((VarCatego.is_intpos pos')&&(VarCatego.is_indexpos pos))
    )
  else
    false

let may_mem env (a,pos) l =
  List.exists (fun (a',pos') ->may_same env (a,pos) (a',pos')) l

      
(* lavelからrtn_lまでの経路で『a[posa]にwriteならばb[posb]にwrite 』が成立するか調べる*)
let aW_then_bW lavel ((a,posa),env) (b,posb) graph rtn_l =
  if (posa=VarCatego.Array(VarCatego.Unknown)||
        posb=VarCatego.Array(VarCatego.Unknown))then false
  else if(a,posa)=(b,posb) then true
  else
  let rec inner (l,end_l) aW_exist bW_above aW_then_bW rtn_l =
    if (l=rtn_l) then(aW_exist,bW_above,aW_then_bW,true) else
      if(l=end_l)then (aW_exist,bW_above,aW_then_bW,false) else
        (assert (M.mem l graph) ;
         let {rw=read_write;pre_w=_;next=next_l}=M.find l graph in
         
        let (aW_exist',bW_above',aW_then_bW') =
          match(read_write)with
          |Write(a',pos',_) when may_same env (a',pos') (a,posa)->
            let aW_exist'=true in
            let aW_then_bW'=bW_above in(**)
            (aW_exist',bW_above,aW_then_bW')
          |Write(b',pos',_) when (b',pos')=(b,posb) ->
            let bW_above'=true in
            let aW_then_bW'=true in
            (aW_exist,bW_above',aW_then_bW')
          |_ ->(aW_exist,bW_above,aW_then_bW)
        in
        match next_l with
        |Seq(l') ->inner (l',end_l) aW_exist' bW_above' aW_then_bW' rtn_l
        |Branch((l1,l2),join_l) ->
          let (aW_exist1,bW_above1,aW_then_bW1,is_return1)=
            inner (l1,join_l) aW_exist' bW_above' aW_then_bW' rtn_l in
          let (aW_exist2,bW_above2,aW_then_bW2,is_return2)=
            inner (l2,join_l) aW_exist' bW_above' aW_then_bW' rtn_l in
          if(is_return1)then (aW_exist1,bW_above1,aW_then_bW1,true)
          else if(is_return2)then(aW_exist2,bW_above2,aW_then_bW2,true)
          else
            let aW_exist''=aW_exist1||aW_exist2 in
            let bW_above''=bW_above1&&bW_above2 in
            let aW_then_bW''=aW_then_bW1&&aW_then_bW2 in
            inner (join_l,end_l) aW_exist'' bW_above'' aW_then_bW'' rtn_l
        |No_next ->assert false)
  in
  let (_,_,aW_then_bW,_) =
    inner (lavel,rtn_l) false false true rtn_l in
  aW_then_bW

let is_written pre_written env (b,posb) graph end_l=
  if(pre_written=[])then
    (Format.eprintf "empty_pre_written@.";
     VarCatego.print_apos (b,posb);false)
  else
    let tf=List.map
             (fun ((a,posa),l) ->
               VarCatego.print_apos (a,posa);
               let graph'= set_rw l Not graph in
               aW_then_bW  l ((a,posa),env) (b,posb) graph' end_l)
             pre_written
    in
    List.exists (fun x->x=true) tf

(* let is_trace_of (a,pos) x graph = *)
let add_list x list =
  if List.mem x list then list
  else
    x::list
let rec unique_list = function
  |x::xs->if List.mem x xs then unique_list xs
          else x::(unique_list xs)
  |[] ->[]
          
      
exception WAR of Id.t*VarCatego.elm_pos
exception RAW of Id.t*VarCatego.elm_pos
let analyze' (l,end_l) graph env=
  
  let rec inner (l,end_l) (read,write,may_write,localWAR,acum) trace_env  =
    if(l=end_l)then (read,write,may_write,localWAR,acum,trace_env)
    else
      let {rw=read_write;pre_w=pre_written;next=next_l}=M.find l graph in
      let unknown=VarCatego.Array(VarCatego.Unknown) in
      let (read',write',may_write',localWAR',acum',trace_env')=

        match read_write with
        |Read(a,pos) ->
          (* Format.eprintf "read@."; *)
          (* VarCatego.print_apos (a,pos); *)
          if(List.mem (a,pos) write&&pos<>unknown) then
            let localWAR'=add_list (a,pos) localWAR in
            (read,write,may_write ,localWAR',acum,trace_env)
          else if(may_mem env (a,pos) may_write) then
            if(Format.eprintf "goto_is_written@.";
              is_written pre_written env (a,pos) graph l)then
              (Format.eprintf "is_written_return@.";
              let localWAR'=add_list (a,pos) localWAR in
              (read,write,may_write, localWAR',acum,trace_env))
            else
              raise (WAR (a,pos))
          else
            (add_list (a,pos) read,write,may_write,localWAR,acum,trace_env)
        |Write(a,pos,x) ->
          (* Format.eprintf "write@."; *)
          (* VarCatego.print_apos (a,pos); *)
          let raws=
            List.filter (fun (a',pos') ->may_same env (a,pos) (a',pos')) read in

          if(raws=[])then
            let write' =add_list (a,pos) write in
            let may_write' = add_list (a,pos) may_write in
            (read,write',may_write',localWAR,acum,trace_env)
          else if(raws=[(a,pos)]&&pos<>unknown&&M.mem x trace_env) then
            if((M.find x trace_env)=(a,pos)) then
              let write' =add_list (a,pos) write in
              let may_write' = add_list (a,pos) may_write in
              let acum'=add_list (a,pos) acum in
              (read,write',may_write',localWAR,acum',trace_env)
            else
              raise (RAW(a,pos))
          else
            raise (RAW(a,pos))
        |Trace_Get(x,(a,pos)) ->
          (* Format.eprintf "trace_get:%s=.@" x; *)
          (* VarCatego.print_apos (a,pos); *)
          (read,write,may_write,localWAR,acum,M.add x (a,pos) trace_env)
        |Trace_Add(x,(y,z)) ->
          (* Format.eprintf "trace_add:%s=%s+%s.@" x y z; *)
          let (a,pos)=try M.find y trace_env with Not_found ->M.find z trace_env in
          (read,write,may_write,localWAR,acum,M.add x (a,pos) trace_env)
        |Not ->(read,write,may_write,localWAR,acum,trace_env)
      in
      
      match next_l with
      |Seq(l') ->
        inner (l',end_l) (read',write',may_write',localWAR',acum') trace_env'
      |Branch((l1,l2),join_l) ->
        let (read1,write1,may_write1,localWAR1,acum1,trace_env1) =
          inner (l1,join_l) (read',write',may_write',localWAR',acum') trace_env' 
        in
        let (read2,write2,may_write2,localWAR2,acum2,trace_env2) =
          inner (l2,join_l) (read',write',may_write',localWAR',acum') trace_env'
        in
        
        let read''=read1@(List.filter (fun x ->not (List.mem x read1)) read2) in
        let write''=List.filter (fun x->List.mem x write1) write2 in
        let may_write''=
          may_write1@(List.filter (fun x ->not (List.mem x may_write1)) may_write2)
        in
        let localWAR''=
          localWAR1@(List.filter (fun x ->not (List.mem x localWAR1)) localWAR2)
        in
        let acum''=acum1@(List.filter (fun x ->not (List.mem x acum1)) acum2) in
        let trace_env''=M.union (fun x ap1 ap2->assert (ap1=ap2);Some ap1)
                                trace_env1
                                trace_env2 in
        inner (join_l,end_l) (read'',write'',may_write'',localWAR'',acum'') trace_env''
      |No_next ->assert false
  in

  inner (l,end_l) ([],[],[],[],[]) M.empty
        
let analyze env {graph=g;end_l=el} =
  analyze' (start_l,el) g env
