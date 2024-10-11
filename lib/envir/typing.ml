type t =
  { local : Local.t
  ; ty_refine : Ty_refine.t
  ; ty_param : Ty_param.t
  ; ty_param_refine : Ty_param_refine.t
  ; subtyping : Subtyping.t
  }
[@@deriving compare, create, eq, sexp, show]

let empty =
  { local = Local.empty
  ; ty_refine = Ty_refine.empty
  ; ty_param = Ty_param.empty
  ; ty_param_refine = Ty_param_refine.empty
  ; subtyping = Subtyping.empty
  }
;;

(* ~~ Locals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let bind_local ({ local; _ } as t) key ty =
  let local = Local.bind_local local key ty in
  { t with local }
;;

let find_local { local; _ } key = Local.find local key
let find_local_refinement { ty_refine; _ } local = Ty_refine.find_local ty_refine local

(* ~~ Type parameters ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
