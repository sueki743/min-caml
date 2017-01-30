
let index_vars=ref []

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

type node ={ rw:read_write ; pre_w:pre_written_t ; next:lavel list }
                 
type t={graph:( node M.t) ; end_l:lavel }
(*ラベルからnodeへのmapでグラフを表現*)

let find x env =try M.find x env with Not_found ->x
         
let subst_array_read_write env = function
  |Read(a,pos) ->Read(find a env,pos)
  |Write(a,pos,x) ->Write(find a env,pos ,find x pos)
  |Trace_Get(x,(a,pos)) ->Trace_Get(x,(find a env,pos))
  |e ->e
         
let subst_array env {graph=g;end_l=el} =
  let g'=
  M.map
    (fun  {rw=read_write;pre_w=pre;next=next_l} ->
      let read_write'=subst_array_read_write env rw in
      let pre'=List.map (fun ((a,pos),l) ->((find a env,pos),l)) pre in
      {rw=read_write';pre_w=pre';next=next_l})
    g in
  {graph=g' ; end_l=el}
         
let empty=
  let start_node = {rw=Not ; pre_w=[] ; next=[]} in
  {graph=(M.add start_l start_node (M.empty)) ; end_l=start_l}

let is_empty {graph=_;end_l=el} = (el=start_l)
  
let add_read new_lavel (a,pos) pre_written {graph=g;end_l=el} =
  
  let {rw=read_write;pre_w=pre;next=_}=M.find el g in
  (*gの末尾にlavelのnodeを足す*)
  let g'=M.add el {rw=read_write;pre_w=pre;next=[new_lavel]} g in
  let g''
    =M.add new_lavel  {rw=Read(a,pos);pre_w=pre_written;next=[]} g'
  in
  { graph=g'' ; end_l=new_lavel }

let add_write new_lavel (a,pos,x) pre_written {graph=g;end_l=el} =
  let {rw=read_write;pre_w=pre;next=_}=M.find el g in
  (*gの末尾にlavelのnodeを足す*)
  let g'=M.add el {rw=read_write;pre_w=pre;next=[new_lavel]} g in
  let g''
    =M.add new_lavel {rw=Write(a,pos,x);pre_w=pre_written;next=[]} g'
  in
  { graph=g'' ; end_l=new_lavel}

let add_trace_add (x,(y,z)) {graph=g;end_l=el} =
  let new_lavel =genlavel () in
  let {rw=read_write;pre_w=pre;next=_}=M.find el g in
  (*gの末尾にlavelのnodeを足す*)
  let g'=M.add el {rw=read_write;pre_w=pre;next=[new_lavel]} g in
  let g''
    =M.add new_lavel {rw=Trace_add(x,(y,z));pre_w=pre_written;next=[]} g'
  in
  { graph=g'' ; end_l=new_lavel}

let add_trace_get (x,(a,pos)) {graph=g;end_l=el} =
  let new_lavel =genlavel () in
  let {rw=read_write;pre_w=pre;next=_}=M.find el g in
  (*gの末尾にlavelのnodeを足す*)
  let g'=M.add el {rw=read_write;pre_w=pre;next=[new_lavel]} g in
  let g''
    =M.add new_lavel {rw=Trace_get(x,(a,pos));pre_w=pre_written;next=[]} g'
  in
  { graph=g'' ; end_l=new_lavel}
    

let set_children l children  g=
  let {rw=read_write;pre_w=pre;next=_}=M.find l g in
  (M.add l {rw=read_write;pre_w=pre;next=children} g)
    
let add_branch rw_g (rw_g1,rw_g2) joint_l =
  let {graph=g;end_l=e_l} = rw_g in
  let {graph=g1;end_l=e_l1} = rw_g1 in
  let {graph=g2;end_l=e_l2} = rw_g2 in
  if (not ((is_empty rw_g1)||(is_empty rw_g2))) then
    let {rw=_;pre_w=_;next=next_l1}=M.find start_l g1 in
    let {rw=_;pre_w=_;next=next_l2}=M.find start_l g2 in
    let new_g =M.union
                 (fun lavel n1 n2 ->assert lavel=start_l;None)
                 g1
                 g2 in
    let new_g=M.union
                (fun lavel n1 n2 ->assert false;None)
                (set_children e_l (next_l1@next_l2) g)
                new_g in
    let new_g=M.add joint_l {rw=Non;pre_w=[];next=[]} new_g in
    let new_g=set_children e_l1 [joint_l]
                           (set_children e_l2 [joint_l] new_g) in
    {graph=new_g;end_l=joint_l}
  else if (is_empty rw_g1&&(not is_empty rw_g2)) then
    let {rw=_;pre_w=_;next=next_l2}=M.find start_l g2 in
    let new_g=M.union
                (fun lavel n n2 ->assert lavel=start_l;Some n)
                (set_children e_l (joint_l::nextl2) g)
                (set_children e_l2 [joint_l] g2) in
    let new_g=M.add joint_l {rw=Non;pre_w=[];next=[]} new_g in
    {graph=new_g;end_l=joint_l}
  else if ((not is_empty rw_g1)&&is_empty rw_g2) then
    let {rw=_;pre_w=_;next=next_l1}=M.find start_l g1 in
    let new_g=M.union
                (fun lavel n n2 ->assert lavel=start_l;Some n)
                (set_children e_l (joint_l::nextl1) g)
                (set_children e_l1 [joint_l] g1) in
    let new_g=M.add joint_l {rw=Non;pre_w=[];next=[]} new_g in
    {graph=new_g;end_l=joint_l}
  else(*is_empty rw_g1&&is_empty rw_g2*)
    rw_g(*変更なし*)
      
                                    

  
  
  
  
  
  
  
