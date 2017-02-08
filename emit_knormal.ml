open Printf
open KNormal

let print_id oc id depth=
  fprintf oc "%*s" depth "";
  fprintf oc "(";
  Id.print_id oc id;
  fprintf oc ")\n"

let rec g oc tree depth =
  fprintf oc "%*s" depth "";
  match tree with
  |Unit ->fprintf oc "UNI\n"
  |Int i ->fprintf oc "Int %d\n" i
  |Float f->fprintf oc "Float %f\n" f
  |Neg t ->fprintf oc "Neg\n";
           print_id oc t (depth+1)
  |Add (t1,t2) ->fprintf oc "Add\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |Sub (t1,t2) ->fprintf oc "Sub\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |Mul (t1,t2) ->fprintf oc "Mul\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |Div (t1,t2) ->fprintf oc "Div\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |FNeg t ->fprintf oc "FNeg\n";
            print_id oc t  (depth+1)
  |FAdd (t1,t2) ->fprintf oc "FAdd\n";
                  print_id oc t1 (depth+1);
                  print_id oc t2 (depth+1)
  |FSub (t1,t2) ->fprintf oc "FSub\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |FMul (t1,t2) ->fprintf oc "FMul\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |FDiv (t1,t2) ->fprintf oc "FDiv\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
  |IfEq (t1,t2,tree1,tree2) ->fprintf oc "IfEq\n";
                              print_id oc t1 (depth+1);
                              print_id oc t2 (depth+1);
                              g oc tree1 (depth +1);
                              g oc tree2 (depth +1)
  |IfLE (t1,t2,tree1,tree2) ->fprintf oc "IfLE\n";
                              print_id oc t1 (depth+1);
                              print_id oc t2 (depth+1);
                              g oc tree1 (depth +1);
                              g oc tree2 (depth +1)
  |Let ((id1,ty1),t2,t3) ->fprintf oc "Let\n";
                           print_id oc id1 (depth+1);
                           g oc t2 (depth+1);
                           g oc t3 depth;
  |Let_Ref((x,t),e1,e2) ->fprintf oc "Let_Ref\n";
                          print_id oc x (depth+1);
                          g oc e1 (depth +1);
                          g oc e2 depth
  |Var v ->fprintf oc "((";Id.print_id oc v;fprintf oc "))\n"
  |LetRec (fundef,t1)->fprintf oc "LetRec\n";
                       fprintf oc "%*s" (depth+1) "";
                       let {name=(n1,ty1);args=arglist;body=funbody}=fundef in
                       fprintf oc "<< ";
                       Id.print_id oc n1;
                       fprintf oc " | ";
                       List.iter (fun (id,ty)->Id.print_id oc id;fprintf oc " ") arglist;
                       fprintf oc "|\n\n";
                       g oc funbody (depth+2);
                       fprintf oc "\n%*s>>\n" (depth+1) "";
                       g oc t1 depth
  | LetPara({pargs = xts;
             index =cs
            ;accum=acc
            ;pbody=e1},e2) ->
     fprintf oc "LetPara\n";
     fprintf oc "%*s" (depth+1) "";
     fprintf oc "<< ";
     fprintf oc "parallel_part";
     
     fprintf oc " | ";
     List.iter (fun x ->print_id oc x  0) (List.map fst xts);
     List.iter (fun (a,n) ->fprintf oc "%s(%d) "a n) (List.concat acc);
     fprintf oc "|\n\n";
     g oc  e1 (depth+2);
     fprintf oc "\n%*s>>\n" (depth+1) "";
     g oc e2 depth
  |Run_parallel (a,d,xs,ys) ->fprintf oc "Run_parallel(%s,%s)\n" a d;
                              List.iter (fun x ->print_id oc x (depth +1)) xs;
                              let ys' = List.map fst ys in
                              List.iter (fun x ->print_id oc x (depth+1)) ys'
  |App (t1,ts) -> fprintf oc "App\n";
                  List.iter (fun x ->print_id oc x (depth +1)) (t1::ts)
                  
  |Tuple ts ->fprintf oc "Tuple\n";
              (match ts with
               |[] -> fprintf oc "\n";
               |_ ->List.iter (fun x ->print_id oc x (depth +1)) ts;
                    ())
  |LetTuple (ids1,t2,tree3)->fprintf oc "LetTuple\n";
                          fprintf oc "%*s" (depth+1) "";
                          List.iter (fun (id,ty)->Id.print_id oc id;fprintf oc " ") ids1;
                          fprintf oc "\n";
                          print_id oc t2 (depth+1);
                          g oc tree3 (depth+1)
  |Get (t1,t2) ->fprintf oc "Get\n";
                 print_id oc t1 (depth+1);
                 print_id oc t2 (depth+1);
  |Put (t1,t2,t3)->fprintf oc "Put\n";
               print_id oc t1 (depth+1);
               print_id oc t2 (depth+1);
               print_id oc t3 (depth+1)
  |ExtArray t ->fprintf oc "ExtArray\n";
                print_id oc t (depth+1)
  |ExtFunApp (t1,t2s)->fprintf oc "ExtFunApp\n";
                       print_id oc t1 (depth+1);
                       List.iter (fun x->(print_id oc x (depth+1))) t2s
  |Ftoi(t1) ->fprintf oc "Ftoi(%s)\n" t1
  |Itof(t1) ->fprintf oc "Itof(%s)\n" t1
  |FAbs(t1) ->fprintf oc "FAbs(%s)\n" t1
  |FSqrt(t1) ->fprintf oc "FSqrt(%s)\n" t1
  |Read_int(t1) ->fprintf oc "Read_int(%s)\n" t1
  |Read_float(t1) ->fprintf oc "Read_float(%s)\n" t1
  |Print_char(t1) ->fprintf oc "Print_char(%s)\n" t1
  |ForLE(((i,a),(j,k),step),e)->
    fprintf oc "ForLE{%s=%s|%s<=%s|\n" i a j k;
    g oc step (depth+7);
    fprintf oc "|\n";
    g oc e (depth + 1);
    fprintf oc "%*s" depth "";fprintf oc "endforLE\n"
  |Ref_Get(t) ->fprintf oc "Ref_Get(%s)\n" t
  |Ref_Put(t1,t2) ->fprintf oc "Ref_Put(%s<-%s)\n" t1 t2
  |Accum(a,n,x) ->fprintf oc "Accum(%s.(%s), %s" a n x

let f oc tree=g oc tree 0;fprintf oc "\n\n\n\n\n" ;tree
