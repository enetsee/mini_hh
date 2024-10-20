type _ Effect.t +=
  | Tell_is_subtype :
      { ty_sub : Ty.t
      ; ty_super : Ty.t
      }
      -> unit Effect.t
  | Find_local : Name.Tm_var.t -> Ty.t option Effect.t
  | Locally_refine :
      { is_opt : Ctxt.Cont.Refinement.t option
      ; as_opt : Ctxt.Cont.Refinement.t option
      }
      -> unit Effect.t
  | Refine_by :
      { ty_scrut : Ty.t
      ; ty_test : Ty.t
      }
      -> (Ty.Refinement.t * Ctxt.Ty_param.Refinement.t option) Effect.t

let tell_is_subtype ~ty_sub ~ty_super = Effect.perform (Tell_is_subtype { ty_sub; ty_super })
let find_local tm_var = Effect.perform (Find_local tm_var)
let locally_refine ~is_opt ~as_opt = Effect.perform (Locally_refine { is_opt; as_opt })
let refine_by ~ty_scrut ~ty_test = Effect.perform (Refine_by { ty_scrut; ty_test })
