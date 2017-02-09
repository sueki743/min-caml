open Asm
       open Printf

let emit_exp oc  = function
  |Nop->fprintf oc "nop\n"
  |Add _ ->fprintf oc "add\n"
  |Sub _->fprintf oc "sub\n"
  |Mul _ ->fprintf oc "mul\n"
  |Div _ ->fprintf oc "div\n"
  |SLL _ ->fprintf oc "sll\n"
  |SRL _ ->fprintf oc "srl\n"
  |SRA _ ->fprintf oc "sra\n"
  |Lw _ ->fprintf oc "lw\n"
  |Sw _ ->fprintf oc "sw\n"
  |In ->fprintf oc "in\n"
  |Out _ ->fprintf oc "out\n"
  |Save(r,x) ->fprintf oc "save(%s, %s)\n" r x
  |Restore x ->fprintf oc "restore(%s)\n" x
  |Ref_Get x ->fprintf oc "ref_get(%s)\n" x
  |Ref_Put(x,y) ->fprintf oc "ref_put(%s, %s)\n" x y
  | _ ->fprintf oc "tenuki\n"
                 
