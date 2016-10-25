open Printf
open Asm
let p_id_im oc =function
  |V i ->fprintf oc "V(";Id.print_id oc i;fprintf oc ")"
  |C i ->fprintf oc "C(%d)" i
                 
let rec g oc = function
  |Ans exp1 ->fprintf oc "Ans\n\t";
              g_exp oc exp1
  |Let ((x,_),exp,tree) ->fprintf oc "Let\n\t";
                          g_exp oc exp;
                          g oc tree
and g_exp oc= function
  |Nop ->fprintf oc "Nop"
  |Set i ->fprintf oc "Set %d" i
  |SetL l ->fprintf oc "SetL ";Id.printf_l oc l;
  |Mov n ->fprintf oc "Mov ";Id.print_id oc n;
  |Neg n ->fprintf oc "Neg ";Id.print_id oc n;
  |Add (n,im)->fprintf oc "Add ";
               Id.print_id oc n;fprintf oc " ";
               p_id_im oc im
  |Sub (n,im)->fprintf oc "Sub ";
               Id.print_id oc n;fprintf oc " ";
               p_id_im oc im
  |SLL (n,im)->fprintf oc "SLL ";
               Id.print_id oc n;fprintf oc " ";
               p_id_im oc im
  |LD (n,im)->fprintf oc "LD ";
               Id.print_id oc n;fprintf oc " ";
               p_id_im oc im
