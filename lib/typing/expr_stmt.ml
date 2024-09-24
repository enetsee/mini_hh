open Core
open Reporting

module rec Expr : sig
  include Sigs.Synthesizes with type t := Lang.Expr.t and type out := Ty.t and type env_out := Envir.Typing.t
  include Sigs.Checks with type t := Lang.Expr.t and type env_out := Envir.Typing.t
end = struct
  let synth t ~ctxt ~env ~errs =
    match t with
    | Lang.Expr.Is is_ -> Is.synth is_ ~ctxt ~env ~errs
    | _ -> failwith "Nope"
  ;;

  (* Just subsumption case for now *)
  let check t ~against ~ctxt ~env ~errs =
    let ty_sub, env, errs = synth t ~ctxt ~env ~errs in
    (* TODO(mjt) move to algebraic effects and hide all this *)
    let subtyping_res =
      let Envir.Typing.{ ty_param; ty_param_refine; subtyping = env; _ } = env
      and Ctxt.{ oracle; _ } = ctxt in
      let ctxt = Subtyping.Ctxt.create ~oracle ~ty_param ~ty_param_refine ()
      and ty_super = against in
      Subtyping.Tell.is_subtype ~ty_sub ~ty_super ~ctxt ~env
    in
    match subtyping_res with
    | Error err -> env, Err.Subtyping err :: errs
    | Ok subtyping_env -> Envir.Typing.{ env with subtyping = subtyping_env }, errs
  ;;
end

(* ~~ Is refinement expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Is : sig
  include Sigs.Synthesizes with type t := Lang.Is.t and type out := Ty.t and type env_out := Envir.Typing.t
end = struct
  (** Typing `is` can give us:
      - a type refinement if the scrutinee is a local
      - type parameter refinements if the test / scrutinee involve generics

      TODO(mjt) support properties *)
  let synth Lang.Is.{ scrut; ty_test } ~ctxt ~env ~errs =
    (* Get the type of the scrutinee expression *)
    let ty_scrut, env, errs = Expr.synth scrut ~ctxt ~env ~errs in
    (* Refine the scrutinee under the test type, bind any type params from the opened existential *)
    let _refinement_res =
      let Envir.Typing.{ ty_param; ty_param_refine; _ } = env
      and Ctxt.{ oracle; _ } = ctxt in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      Refinement.refine ~ty_scrut ~ty_test ~ctxt
    in
    (* match refinement_res with
    | Error err ->
      (* The refinemnt gave us a subtyping error but we will assume we can just  *)
    let ty_refine =
      Option.value_map ~default:Envir.Ty_refine.empty ~f:(fun id -> Envir.Ty_refine.of_local id ty_test)
      @@ Lang.Expr.local_opt scrut
    in *)
    let delta =
      Envir.Typing.create
        ~local:Envir.Local.empty
        ~ty_refine:Envir.Ty_refine.empty
        ~ty_param:Envir.Ty_param.empty
        ~ty_param_refine:Envir.Ty_param_refine.empty
        ~subtyping:()
        ()
    in
    Ty.bool Prov.empty, delta, errs
  ;;
end

(* ~~ As refinement expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and As : sig end = struct end

(* ~~ Binary expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Binary : sig
  include Sigs.Synthesizes with type t := Lang.Binary.t and type out := Ty.t and type env_out := Envir.Typing.t
end = struct
  (** Typing logical binary expression carries through the refinements from each operand *)
  let synth_logical (binop, lhs, rhs) ~ctxt ~env ~errs =
    let delta_lhs, errs = Expr.check lhs ~against:(Ty.bool Prov.empty) ~ctxt ~env ~errs in
    (* Type the rhs operand under the refinements from the first *)
    let delta_rhs, errs =
      (* TODO(mtj) hide all this *)
      let Envir.Typing.
            { local = local_delta
            ; ty_refine = ty_refine_delta
            ; ty_param = ty_param_delta
            ; ty_param_refine = ty_param_refine_delta
            ; subtyping
            }
        =
        delta_lhs
      and Envir.Typing.{ local; ty_refine; ty_param; ty_param_refine; _ } = env in
      (* New local bindings supercede the old *)
      let local = Envir.Local.merge_right local local_delta
      (* New type refinements intersect with existing refinements *)
      and ty_refine = Envir.Ty_refine.meet ty_refine ty_refine_delta
      (* New type parameters must be fresh with respect the existing env *)
      and ty_param = Envir.Ty_param.merge_disjoint_exn ty_param ty_param_delta
      (* New type parameter refinements intersect with existing refinements *)
      and ty_param_refine = Envir.Ty_param_refine.meet ty_param_refine ty_param_refine_delta ~prov:Prov.empty in
      let env = Envir.Typing.create ~local ~ty_refine ~ty_param ~ty_param_refine ~subtyping () in
      Expr.check rhs ~against:(Ty.bool Prov.empty) ~ctxt ~env ~errs
    in
    (* Now combine the two deltas *)
    let delta =
      (* TODO(mtj) hide all this *)
      let Envir.Typing.
            { local = local_lhs
            ; ty_refine = ty_refine_lhs
            ; ty_param = ty_param_lhs
            ; ty_param_refine = ty_param_refine_lhs
            ; _
            }
        =
        delta_lhs
      and Envir.Typing.
            { local = local_rhs
            ; ty_refine = ty_refine_rhs
            ; ty_param = ty_param_rhs
            ; ty_param_refine = ty_param_refine_rhs
            ; subtyping
            }
        =
        delta_rhs
      in
      (* New local bindings supercede the old *)
      let local = Envir.Local.merge_right local_lhs local_rhs
      (* New type parameters must be fresh with respect the existing env *)
      and ty_param = Envir.Ty_param.merge_disjoint_exn ty_param_lhs ty_param_rhs
      and ty_refine, ty_param_refine =
        match binop with
        | Lang.Binop.Logical.And ->
          ( Envir.Ty_refine.meet ty_refine_lhs ty_refine_rhs
          , Envir.Ty_param_refine.meet ty_param_refine_lhs ty_param_refine_rhs ~prov:Prov.empty )
        | Lang.Binop.Logical.Or ->
          ( Envir.Ty_refine.join ty_refine_lhs ty_refine_rhs
          , Envir.Ty_param_refine.join ty_param_refine_lhs ty_param_refine_rhs ~prov:Prov.empty )
      in
      Envir.Typing.create ~local ~ty_refine ~ty_param ~ty_param_refine ~subtyping ()
    in
    Ty.bool Prov.empty, delta, errs
  ;;

  let synth Lang.Binary.{ binop; lhs; rhs } ~ctxt ~env ~errs =
    match binop with
    | Logical binop -> synth_logical (binop, lhs, rhs) ~ctxt ~env ~errs
  ;;
end

(* ~~ Unary expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Unary : sig end = struct end

(* ~~ Statements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Stmt : sig
  include Sigs.Synthesizes with type t := Lang.Stmt.t and type out := unit and type env_out := Envir.Local.t
end = struct
  let synth t ~ctxt ~env ~errs =
    match t with
    | Lang.Stmt.Assign assign -> Assign.synth assign ~ctxt ~env ~errs
    | Lang.Stmt.Seq seq -> Seq.synth seq ~ctxt ~env ~errs
    | _ -> failwith "Nope"
  ;;
end

(* ~~ Assigment ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Assign : sig
  include Sigs.Synthesizes with type t := Lang.Assign.t and type out := unit and type env_out := Envir.Local.t
end = struct
  let synth_local local rhs ~ctxt ~env ~errs =
    (* Synthesize a type for the right hand side under the initial environment. *)
    let ty, Envir.Typing.{ local = env_delta; _ }, errs = Expr.synth rhs ~ctxt ~env ~errs in
    (* Bind the lvalue in the local env *)
    let env_delta = Envir.Local.bind_local env_delta local ty in
    (* Refinments arising from the expression are applicable and the new binding
       are applicable to the a `next` continuation *)
    (), env_delta, errs
  ;;

  let synth Lang.Assign.{ lvalue; rhs } ~ctxt ~env ~errs =
    match lvalue with
    | Local local -> synth_local local rhs ~ctxt ~env ~errs
  ;;
end

(* ~~ If ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and If : sig
  include Sigs.Synthesizes with type t := Lang.If.t and type out := unit and type env_out := Envir.Local.t
end = struct
  let defined then_ else_ ~(outer : Envir.Local.t) ~errs =
    (* Find the symmetric difference of the bindings in the then and else branches
       and determine which weren't already bound *)
    Sequence.fold ~init:errs ~f:(fun errs k ->
      let k =
        match k with
        | Either.First k -> k
        | Either.Second k -> k
      in
      if Envir.Local.is_bound outer k then errs else Err.(Unbound_at_join k) :: errs)
    @@ Envir.Local.symm_diff then_ else_
  ;;

  let synth Lang.If.{ cond; then_; else_ } ~ctxt ~env ~errs =
    (* Check the type of the conditional exprssion is a subtype of bool *)
    let env_delta, errs = Expr.check cond ~against:(Ty.bool Prov.empty) ~ctxt ~env ~errs in
    (* Check the `then` branch under the delta. This means: 
       - appending the local environments, prefering bindings resulting from typing the conditional expresssion
       
       function foo(MyA $x): void {
         if (($x as MyB) is MyB) {
           ...
         }
       }

      - appending the type parameter environments; any new type parameters _must_ have resulted from implicitly opening
        and existential with an `is` refinement in the conditional expression so they cannot already be bound

      - take the conjunction of the type refinement environments since it's possible we refined already refined to a 
         smaller subtype

       class MyA {}
       class MyB extends MyA {}
       class MyC extends MyB {}

       function blah(MyA $a): void {
         if($a is MyC) {
           if ($a is MyB) {
            ...
           }
         }
       }

      - take the conjunction of the type parameter refinement environments since it's posible a type parameter appearing
        in the type of an `is` expression scrutinee was already refined to some smaller subtype:

        interface MyInferface<+T> {}
        class MyA {}
        class MyB extends MyA implements MyInferface<arraykey> {}
        class MyC extends MyB implements MyInferface<int> {}

        function blah<T>(MyInferface<T> $i): void {
          if ($i is MyC) {
            expect<T>(1); // Ok, T == int
            if ($i is MyB) {
              expect<T>('a'); // error, T == int /\ arraykey 
            }
          }
        }
    *)
    let then_env =
      let Envir.Typing.{ local; ty_refine; ty_param; ty_param_refine; _ } = env
      and Envir.Typing.
            { local = local_delta
            ; ty_refine = ty_refine_delta
            ; ty_param = ty_param_delta
            ; ty_param_refine = ty_param_refine_delta
            ; subtyping
            }
        =
        env_delta
      in
      Envir.Typing.create
        ~local:(Envir.Local.merge_right local local_delta)
        ~ty_param:(Envir.Local.merge_disjoint_exn ty_param ty_param_delta)
        ~ty_refine:(Envir.Ty_refine.meet ty_refine ty_refine_delta)
        ~ty_param_refine:(Envir.Ty_param_refine.meet ty_param_refine ty_param_refine_delta ~prov:Prov.empty)
        ~subtyping
        ()
    (* Check the `else` branch under:
       - The conjunction of the complement of the type refinements resulting from typing the conditional expression.
       - The oringal local env since any locals from the delta since they could only occur using `$x as Foo is Foo`.
       - The original type parameter environment since refinement wasn't true no existentials are opened in the else branch
       - The original type parameter refinement environment for the same reason as above
    *)
    and else_env =
      let Envir.Typing.{ ty_refine; _ } = env
      and Envir.Typing.{ ty_refine = ty_refine_delta; _ } = env_delta in
      let ty_refine = Envir.Ty_refine.(meet ty_refine (cmp ty_refine_delta)) in
      Envir.Typing.{ env with ty_refine }
    in
    (* Type the `then` branch then ensure locals bound in the branch don't contain references to type parameters scoped
       to the branch by promoting any such types to the least supertype not containing a type parameter which will
       be discarded *)
    let local_env_then, errs =
      let _, local_env_then, errs = Stmt.synth then_ ~ctxt ~env:then_env ~errs in
      let Envir.Typing.{ ty_param; _ } = env_delta in
      let Ctxt.{ oracle; _ } = ctxt in
      Envir.Local.map local_env_then ~f:(fun ty -> Exposure.promote_exn ty ty_param ~oracle), errs
    in
    let _, local_env_else, errs = Stmt.synth else_ ~ctxt ~env:else_env ~errs in
    (* Ensure newly bound locals are defined both branches if not already bound *)
    let errs =
      let Envir.Typing.{ local; _ } = env in
      defined ~outer:local local_env_then local_env_else ~errs
    in
    (), Envir.Local.join local_env_then local_env_else ~prov:Prov.empty, errs
  ;;
end

(* ~~ Sequence ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Seq : sig
  include Sigs.Synthesizes with type t := Lang.Seq.t and type out := unit and type env_out := Envir.Local.t
end = struct
  let rec synth_help stmts ~ctxt ~env ~delta ~errs =
    match stmts with
    | [] -> delta, errs
    | stmt :: stmts ->
      (* Type the remaining statements with any locals bound in the current statement; we don't propagate any type
         refinements, newly bound type parameters or type paramter refinements resulting from `is` expressions.
         N.B. we _do_ propogate `as` refinements which cause the type of existing locals to be modified *)
      let env =
        let Envir.Typing.{ local; _ } = env in
        let local = Envir.Local.merge_right local delta in
        Envir.Typing.{ env with local }
      in
      let _, delta, errs = Stmt.synth stmt ~ctxt ~env ~errs in
      let delta2, errs = synth_help stmts ~ctxt ~env ~delta ~errs in
      (* TODO(mjt) remember to only drop next when moving to continuations *)
      delta2, errs
  ;;

  let synth Lang.Seq.(Seq stmts) ~ctxt ~env ~errs =
    let delta, errs = synth_help stmts ~ctxt ~env ~delta:Envir.Local.empty ~errs in
    (), delta, errs
  ;;
end
