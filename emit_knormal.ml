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
                           g oc t3 (depth+1);
  |Var v ->fprintf oc "((";Id.print_id oc v;fprintf oc "))\n"
  |LetRec (fundef,t1)->fprintf oc "LetRec\n";
                       fprintf oc "%*s" (depth+1) "";
                       let {name=(n1,ty1);args=arglist;body=funbody}=fundef in
                       fprintf oc "<< ";
                       Id.print_id oc n1;
                       fprintf oc " | ";
                       List.map (fun (id,ty)->Id.print_id oc id;fprintf oc " ") arglist;
                       fprintf oc "|\n\n";
                       g oc funbody (depth+2);
                       fprintf oc "\n%*s>>\n" (depth+1) "";
                       g oc t1 (depth+1)
  |App (t1,ts) -> fprintf oc "App\n";
                  List.map (fun x ->print_id oc x (depth +1)) (t1::ts);
                  ()
  |Tuple ts ->fprintf oc "Tuple\n";
              (match ts with
               |[] -> fprintf oc "\n";
               |_ ->List.map (fun x ->print_id oc x (depth +1)) ts;
                    ())
  |LetTuple (ids1,t2,tree3)->fprintf oc "LetTuple\n";
                          fprintf oc "%*s" (depth+1) "";
                          List.map (fun (id,ty)->Id.print_id oc id;fprintf oc " ") ids1;
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
                       List.map (fun x->(print_id oc x (depth+1))) t2s;()
  |Ftoi(t1) ->fprintf oc "Ftoi(%s)\n" t1
  |Itof(t1) ->fprintf oc "Itof(%s)\n" t1
  |FAbs(t1) ->fprintf oc "FAbs(%s)\n" t1
  |FSqrt(t1) ->fprintf oc "FSqrt(%s)\n" t1
  |Read_int(t1) ->fprintf oc "Read_int(%s)\n" t1
  |Read_float(t1) ->fprintf oc "Read_float(%s)\n" t1
  |Print_char(t1) ->fprintf oc "Print_char(%s)\n" t1

let f oc tree=g oc tree 0;fprintf oc "\n\n\n\n\n" ;tree
