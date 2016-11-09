exception Error of Type.t * Type.t * Syntax.pos
exception Occur of Type.t * Type.t * Syntax.pos
val extenv : Type.t M.t ref
val f : Syntax.t -> Syntax.t
