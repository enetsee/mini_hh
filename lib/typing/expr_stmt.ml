open Core
open Reporting

module rec Expr : sig
  val synth : Lang.Expr.t -> def_ctxt:Ctxt.Def.t -> cont_ctxt:Ctxt.Cont.t -> Ty.t * Ctxt.Cont.Expr_delta.t

  val check
    :  Lang.Expr.t
    -> against:Ty.t
    -> def_ctxt:Ctxt.Def.t
    -> cont_ctxt:Ctxt.Cont.t
    -> Ty.t * Ctxt.Cont.Expr_delta.t
end = struct
  let synth expr ~def_ctxt ~cont_ctxt =
    let Located.{ elem; span }, def_ctxt, cont_ctxt = Eff.log_enter_synth_expr expr def_ctxt cont_ctxt in
    let open Lang.Expr_node in
    Eff.log_exit_expr span
    @@
    match elem with
    | Lit lit ->
      let ty = Lit.synth (lit, span) in
      ty, Ctxt.Cont.Expr_delta.empty
    | Local tm_var ->
      let ty =
        match Ctxt.Cont.find_local cont_ctxt tm_var with
        | Some ty ->
          let prov_tm_var = Prov.lvalue_tm_var span in
          Ty.map_prov ty ~f:(fun prov_def -> Prov.use ~prov_def ~prov_tm_var)
        | _ ->
          let _ : unit =
            let tm_var = Located.create ~elem:tm_var ~span () in
            let err = Err.unbound_local tm_var in
            Eff.log_error err
          in
          Ty.nothing (Prov.lvalue_tm_var span)
      in
      ty, Ctxt.Cont.Expr_delta.empty
    | This ->
      (* TODO(mjt) add this literal witness *)
      let ty = Ty.this @@ Prov.witness span in
      ty, Ctxt.Cont.Expr_delta.empty
    | Is is_expr -> Is.synth (is_expr, span) ~def_ctxt ~cont_ctxt
    | As as_expr -> As.synth (as_expr, span) ~def_ctxt ~cont_ctxt
    | Binary binary -> Binary.synth (binary, span) ~def_ctxt ~cont_ctxt
    | _ -> failwith "TODO"
  ;;

  let check expr ~against ~def_ctxt ~cont_ctxt =
    let expr, against, def_ctxt, cont_ctxt = Eff.log_enter_check_expr expr against def_ctxt cont_ctxt in
    let ty, refn = synth expr ~def_ctxt ~cont_ctxt in
    let subty_err_opt = Subtyping.Tell.is_subtype ~ty_sub:ty ~ty_super:against ~ctxt:cont_ctxt in
    let _ : unit = Option.iter subty_err_opt ~f:(fun err -> Eff.log_error (Err.subtyping err)) in
    Eff.log_exit_expr expr.span (ty, refn)
  ;;
end

and Is : sig
  val synth : Lang.Is.t * Span.t -> def_ctxt:Ctxt.Def.t -> cont_ctxt:Ctxt.Cont.t -> Ty.t * Ctxt.Cont.Expr_delta.t
end = struct
  let refine_by expr_scrut ~ty_scrut ~ty_test cont_ctxt =
    let ty_refinement, ty_param_refinement_opt = Refinement.refine ~ty_scrut ~ty_test ~ctxt:cont_ctxt in
    match Located.elem expr_scrut with
    | Lang.Expr_node.Local tm_var ->
      let local = Ctxt.Local.Refinement.singleton tm_var ty_refinement
      and ty_param =
        let default = Ctxt.Ty_param.Refinement.empty in
        Option.value_map ~default ~f:snd ty_param_refinement_opt
      in
      Some (Ctxt.Cont.Refinements.create ~local ~ty_param ())
    | Lang.Expr_node.This ->
      let local = Ctxt.Local.Refinement.empty in
      let ty_param =
        let default = Ctxt.Ty_param.Refinement.empty in
        Option.value_map ~default ~f:snd ty_param_refinement_opt
      in
      Some (Ctxt.Cont.Refinements.create ~local ~ty_param ())
    | _ -> None
  ;;

  let synth (Lang.Is.{ scrut; ty_test }, span) ~def_ctxt ~cont_ctxt =
    (* [Is] expressions have type bool *)
    let prov = Prov.expr_is span in
    let ty = Ty.bool prov in
    (* First we type the expression in scrutinee posisition; this may have some global side-effects, captured in [ctxt]
       and have conditional and unconditional refinements captured in [is_] and [as_]. Note that in the case that we do
       have an is refinement then the outer expression can't produce one since the subexpression can't be a local or
       [$this] *)
    let ty_scrut, expr_delta_scrut = Expr.synth scrut ~def_ctxt ~cont_ctxt in
    (* The refinements from typing from the scrutinee subexpression apply when typing the [is] expression to in the
       expression *)
    let cont_ctxt = Ctxt.Cont.update_expr cont_ctxt ~expr_delta:expr_delta_scrut in
    (* Build the result is refinement and put it into a delta *)
    let expr_delta_is =
      let rfmts = refine_by scrut ~ty_scrut ~ty_test cont_ctxt in
      Ctxt.Cont.Expr_delta.create ?rfmts ()
    in
    (* We need to combine the expression delta from the scrutinee with the delta resulting from the containing [is]
       expression. When doing this we need:
       - local and type parameter bindings resulting from any [as] sub-expressions in the scrutinee should be combined
         so that those from the second delta are chosen (note: clearly the outer [is] expression has no [as]
         subexpressions so we could actually just chose the [local] and [ty_param] fields here but we want to use the
         same operation for the [as] case)
       - local and type parameter _refinements_ resulting from the scrutinee expression should be combined with the
         [is] refinement for the outer expression such that:
         -- if only one of the delta has a refinement we keep it
         -- if both the inner and outer expression have refinements we take the [meet]
    *)
    let delta =
      let bindings =
        Option.merge
          ~f:(fun t with_ -> Ctxt.Cont.Bindings.extend t ~with_)
          expr_delta_scrut.bindings
          expr_delta_is.bindings
      and rfmts = Option.merge ~f:(Ctxt.Cont.Refinements.meet ~prov) expr_delta_scrut.rfmts expr_delta_is.rfmts in
      Ctxt.Cont.Expr_delta.create ?bindings ?rfmts ()
    in
    ty, delta
  ;;
end

and As : sig
  val synth : Lang.As.t * Span.t -> def_ctxt:Ctxt.Def.t -> cont_ctxt:Ctxt.Cont.t -> Ty.t * Ctxt.Cont.Expr_delta.t
end = struct
  let refine_by expr_scrut prov ~ty_scrut ~ty_assert cont_ctxt =
    let ty_refinement, ty_param_refinement_opt = Refinement.refine ~ty_scrut ~ty_test:ty_assert ~ctxt:cont_ctxt in
    let ty = Ty.refine ty_scrut ~rfmt:ty_refinement in
    match Located.elem expr_scrut with
    | Lang.Expr_node.Local tm_var ->
      let local =
        let tm_var = Located.create ~elem:tm_var ~span:(Located.span_of expr_scrut) () in
        Ctxt.Local.singleton tm_var ty
      and ty_param =
        Option.value_map ty_param_refinement_opt ~default:Ctxt.Ty_param.empty ~f:(fun (_, ty_param_rfmt) ->
          match Ctxt.Ty_param.Refinement.bindings ty_param_rfmt with
          | `Bounds bounds ->
            let ty_params =
              List.map bounds ~f:(fun (name, delta) ->
                let bounds = Option.value_exn @@ Ctxt.Cont.ty_param_bounds cont_ctxt name in
                name, Ty.Param_bounds.meet bounds delta ~prov)
            in
            Ctxt.Ty_param.of_alist ty_params
          | `Top -> Ctxt.Ty_param.empty
          | `Bottom -> failwith "[Typing.As] Encoutered bottom in type parameter refinement")
      in
      ty, Some (Ctxt.Cont.Bindings.create ~local ~ty_param ())
    | Lang.Expr_node.This ->
      let local = Ctxt.Local.empty
      and ty_param =
        Option.value_map ty_param_refinement_opt ~default:Ctxt.Ty_param.empty ~f:(fun (_, ty_param_rfmt) ->
          match Ctxt.Ty_param.Refinement.bindings ty_param_rfmt with
          | `Bounds bounds ->
            let ty_params =
              List.map bounds ~f:(fun (name, delta) ->
                let bounds = Option.value_exn @@ Ctxt.Cont.ty_param_bounds cont_ctxt name in
                name, Ty.Param_bounds.meet bounds delta ~prov)
            in
            Ctxt.Ty_param.of_alist ty_params
          | `Top -> Ctxt.Ty_param.empty
          | `Bottom -> failwith "[Typing.As] Encoutered bottom in type parameter refinement")
      in
      ty, Some (Ctxt.Cont.Bindings.create ~local ~ty_param ())
    | _ -> ty, None
  ;;

  let synth (Lang.As.{ scrut; ty_assert }, span) ~def_ctxt ~cont_ctxt =
    let prov = Prov.expr_as span in
    let ty_scrut, expr_delta_scrut = Expr.synth scrut ~def_ctxt ~cont_ctxt in
    (* The refinements from typing from the scrutinee subexpression apply when typing the [as] expression to in the
       expression *)
    let cont_ctxt = Ctxt.Cont.update_expr cont_ctxt ~expr_delta:expr_delta_scrut in
    let ty, expr_delta_as =
      let ty, bindings = refine_by scrut prov ~ty_scrut ~ty_assert cont_ctxt in
      ty, Ctxt.Cont.Expr_delta.create ?bindings ()
    in
    (* We need to combine the expression delta from the scrutinee with the delta resulting from the containing [as]
       expression. When doing this we need:
       - local and type parameter bindings resulting from any [as] sub-expressions in the scrutinee should be combined
         so that those from the second delta are chosen.
       - local and type parameter _refinements_ resulting from the scrutinee expression should be combined with the
         [as] refinement for the outer expression such that:
         -- if only one of the delta has a refinement we keep it
         -- if both the inner and outer expression have refinements we take the meet
         (note: similar to the [is] case, we know the outer expression doesn't give us any refinements but we want to
         use the same operation)
    *)
    let delta =
      let bindings =
        Option.merge
          ~f:(fun t with_ -> Ctxt.Cont.Bindings.extend t ~with_)
          expr_delta_scrut.bindings
          expr_delta_as.bindings
      and rfmts = Option.merge ~f:(Ctxt.Cont.Refinements.meet ~prov) expr_delta_scrut.rfmts expr_delta_as.rfmts in
      Ctxt.Cont.Expr_delta.create ?bindings ?rfmts ()
    in
    ty, delta
  ;;
end

and Binary : sig
  val synth : Lang.Binary.t * Span.t -> def_ctxt:Ctxt.Def.t -> cont_ctxt:Ctxt.Cont.t -> Ty.t * Ctxt.Cont.Expr_delta.t
end = struct
  let synth_logical_or (lhs, rhs, span) ~def_ctxt ~cont_ctxt =
    let prov = Prov.witness span in
    let ty_bool = Ty.bool prov in
    let _, expr_delta_lhs = Expr.check lhs ~against:ty_bool ~def_ctxt ~cont_ctxt in
    let _, expr_delta_rhs = Expr.check rhs ~against:ty_bool ~def_ctxt ~cont_ctxt in
    let expr_delta =
      let bindings =
        Option.merge
          ~f:(fun t with_ -> Ctxt.Cont.Bindings.extend t ~with_)
          expr_delta_lhs.bindings
          expr_delta_rhs.bindings
      in
      let rfmts = Option.merge ~f:(Ctxt.Cont.Refinements.join ~prov) expr_delta_lhs.rfmts expr_delta_rhs.rfmts in
      Ctxt.Cont.Expr_delta.create ?bindings ?rfmts ()
    in
    ty_bool, expr_delta
  ;;

  let synth_logical_and (lhs, rhs, span) ~def_ctxt ~cont_ctxt =
    (* TODO(mjt): logical op witness *)
    let prov = Prov.witness span in
    let ty_bool = Ty.bool prov in
    let _, expr_delta_lhs = Expr.check lhs ~against:ty_bool ~def_ctxt ~cont_ctxt in
    let _, expr_delta_rhs =
      (* Refinements and bindings from the lhs should be applied in the rhs *)
      let cont_ctxt = Ctxt.Cont.update_expr cont_ctxt ~expr_delta:expr_delta_lhs in
      Expr.check rhs ~against:ty_bool ~def_ctxt ~cont_ctxt
    in
    let expr_delta =
      let bindings =
        Option.merge
          ~f:(fun t with_ -> Ctxt.Cont.Bindings.extend t ~with_)
          expr_delta_lhs.bindings
          expr_delta_rhs.bindings
      in
      let rfmts = Option.merge ~f:(Ctxt.Cont.Refinements.meet ~prov) expr_delta_lhs.rfmts expr_delta_rhs.rfmts in
      Ctxt.Cont.Expr_delta.create ?bindings ?rfmts ()
    in
    ty_bool, expr_delta
  ;;

  let synth (Lang.Binary.{ lhs; rhs; binop }, span) ~def_ctxt ~cont_ctxt =
    match binop with
    | Lang.Binop.Logical And -> synth_logical_and (lhs, rhs, span) ~def_ctxt ~cont_ctxt
    | Lang.Binop.Logical Or -> synth_logical_or (lhs, rhs, span) ~def_ctxt ~cont_ctxt
  ;;
end

(* ~~ Statements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Stmt : sig
  val synth : Lang.Stmt.t -> def_ctxt:Ctxt.Def.t -> cont_ctxt:Ctxt.Cont.t -> Ctxt.Delta.t
end = struct
  let synth stmt ~def_ctxt ~cont_ctxt =
    let Located.{ elem; span }, def_ctxt, cont_ctxt = Eff.log_enter_stmt stmt def_ctxt cont_ctxt in
    Eff.log_exit_stmt span
    @@
    let open Lang.Stmt_node in
    match elem with
    | Expr expr ->
      let _ty, expr_delta = Expr.synth expr ~def_ctxt ~cont_ctxt in
      let next = Ctxt.Cont.Delta.of_expr_delta expr_delta in
      Ctxt.Delta.create ~next ()
    | Return expr_opt ->
      let expr_delta_opt =
        Option.bind expr_opt ~f:(fun expr ->
          match Ctxt.Def.ask_return_ty def_ctxt with
          | Some ty_return -> Some (snd @@ Expr.check expr ~against:ty_return ~def_ctxt ~cont_ctxt)
          | _ ->
            (* Not in function context - raise an error *)
            None)
      in
      let exit = Option.value_map ~default:Ctxt.Cont.Delta.empty ~f:Ctxt.Cont.Delta.of_expr_delta expr_delta_opt in
      Ctxt.Delta.create ~exit ()
    | Assign assign_stmt -> Assign.synth (assign_stmt, span) ~def_ctxt ~cont_ctxt
    | If if_stmt -> If.synth (if_stmt, span) ~def_ctxt ~cont_ctxt
    | Seq seq_stmt -> Seq.synth (seq_stmt, span) ~def_ctxt ~cont_ctxt
    | Unpack unpack_stmt -> Unpack.synth (unpack_stmt, span) ~def_ctxt ~cont_ctxt
  ;;
end

and Assign : sig
  val synth : Lang.Assign.t * Span.t -> def_ctxt:Ctxt.Def.t -> cont_ctxt:Ctxt.Cont.t -> Ctxt.Delta.t
end = struct
  let synth_tm_var tm_var rhs ~def_ctxt ~cont_ctxt =
    let ty_rhs, expr_delta = Expr.synth rhs ~def_ctxt ~cont_ctxt in
    (* Now bind the new new local and any [as] refinement resulting from typing the rhs expression
       in the [next] continuation *)
    let assign_delta =
      let local =
        let prov_lvalue = Prov.lvalue_tm_var @@ Located.span_of tm_var in
        let ty = Ty.map_prov ~f:(fun prov_rhs -> Prov.assign ~prov_rhs ~prov_lvalue) ty_rhs in
        Ctxt.Local.singleton tm_var ty
      in
      let ty_param = Ctxt.Ty_param.empty in
      let bindings = Ctxt.Cont.Bindings.create ~local ~ty_param () in
      Ctxt.Cont.Delta.create ~bindings ()
    in
    let delta = Ctxt.Cont.Delta.extend (Ctxt.Cont.Delta.of_expr_delta expr_delta) ~with_:assign_delta in
    Ctxt.Delta.create ~next:delta ()
  ;;

  let synth (Lang.Assign.{ lvalue; rhs }, _span) ~def_ctxt ~cont_ctxt =
    match lvalue.elem with
    | Lang.Lvalue.Local tm_var ->
      let tm_var = Located.create ~elem:tm_var ~span:lvalue.span () in
      synth_tm_var tm_var rhs ~def_ctxt ~cont_ctxt
  ;;
end

and Unpack : sig
  val synth : Lang.Unpack.t * Span.t -> def_ctxt:Ctxt.Def.t -> cont_ctxt:Ctxt.Cont.t -> Ctxt.Delta.t
end = struct
  let get_bounds span quants names =
    let rec aux n_names quants names ~k =
      match quants, names with
      (* ~~ Continue ~~ *)
      | quant :: quants, new_name :: names ->
        aux (n_names + 1) quants names ~k:(fun (ty_params, subst) ->
          let Ty.Param.{ name; param_bounds } = quant in
          let ty_param = Ty.Param.create ~name:new_name ~param_bounds () in
          let ty =
            let Located.{ span; elem } = new_name in
            let prov = Prov.witness span in
            Ty.generic prov elem
          in
          let subst = Map.add_exn subst ~key:(Located.elem name) ~data:ty in
          k (ty_param :: ty_params, subst))
      (* ~~ Success ~~ *)
      | [], [] -> k ([], Name.Ty_param.Map.empty)
      (* ~~ Failure ~~ *)
      | [], rest ->
        (* We have more names than quantifiers so just use bottom for any remaining name and raise an error *)
        let _ : unit =
          let n_quants = n_names in
          let n_names = n_names + List.length rest in
          let err = Err.unpack_arity ~span ~n_quants ~n_names in
          Eff.log_error err
        in
        let ty_params =
          List.map rest ~f:(fun new_name ->
            let param_bounds = Ty.Param_bounds.bottom (Prov.witness @@ Located.span_of new_name) in
            Ty.Param.create ~name:new_name ~param_bounds ())
        in
        k (ty_params, Name.Ty_param.Map.empty)
      | _, [] ->
        (* We have more quantifiers than names so leave the remaining quantifiers unbound and raise an error *)
        let _ : unit =
          let n_quants = n_names + List.length quants in
          let err = Err.unpack_arity ~span ~n_quants ~n_names in
          Eff.log_error err
        in
        k ([], Name.Ty_param.Map.empty)
    in
    aux 0 quants names ~k:Fn.id
  ;;

  let synth (Lang.Unpack.{ ty_params; tm_var; rhs }, span) ~def_ctxt ~cont_ctxt =
    (* First type the rhs *)
    let ty_rhs, expr_delta = Expr.synth rhs ~def_ctxt ~cont_ctxt in
    (* TODO(mjt) Nooooooooo don't inspect the type - this needs to go when we introduce inference...
       Not sure how to do this but probably some variation on hh's [destructures_to] constraint.
       The interesting thing is that we'll need to introduce fresh type parameters and
       fresh type variables to use in the parameter bounds. Not sure if that will work out... *)
    let ty_params, body_ty =
      let prov_packed, ty_node = Ty.prj ty_rhs in
      match Ty.Node.exists_val ty_node with
      | Some Ty.Exists.{ quants; body } ->
        (* Extract the bounds from the quantifiers and make the subsitution in the body *)
        let bounds, subst = get_bounds span quants ty_params in
        ( bounds
        , Ty.(
            map_prov ~f:(fun prov_unpacked -> Prov.unpack ~prov_packed ~prov_unpacked)
            @@ apply_subst body ~subst ~combine_prov:(fun _ p -> p)) )
      | _ ->
        ( List.map ty_params ~f:(fun (Located.{ span; _ } as name) ->
            let param_bounds = Ty.Param_bounds.bottom @@ Prov.witness span in
            Ty.Param.create ~name ~param_bounds ())
        , ty_rhs )
    in
    let unpack_delta =
      let ty_param = Ctxt.Ty_param.(bind_all empty ty_params) in
      (* TODO(mjt) should we be storing term var locations in [local] too? *)
      let local =
        let span = Located.span_of tm_var in
        let prov_lvalue = Prov.lvalue_tm_var span in
        let ty = Ty.map_prov ~f:(fun prov_rhs -> Prov.assign ~prov_rhs ~prov_lvalue) body_ty in
        Ctxt.Local.singleton tm_var ty
      in
      let bindings = Ctxt.Cont.Bindings.create ~local ~ty_param () in
      Ctxt.Cont.Delta.create ~bindings ()
    in
    (* Now bind the new type parameters , the new local in addition to any bound when typing the rhs expression *)
    let delta = Ctxt.Cont.Delta.extend (Ctxt.Cont.Delta.of_expr_delta expr_delta) ~with_:unpack_delta in
    Ctxt.Delta.create ~next:delta ()
  ;;
end

and If : sig
  val synth : Lang.If.t * Span.t -> def_ctxt:Ctxt.Def.t -> cont_ctxt:Ctxt.Cont.t -> Ctxt.Delta.t
end = struct
  let synth (Lang.If.{ cond; then_; else_ }, span) ~def_ctxt ~cont_ctxt =
    (* Check the condition expression against [bool] *)
    let _ty_cond, expr_delta =
      let against = Ty.bool (Prov.expr_if_cond span) in
      Expr.check cond ~against ~def_ctxt ~cont_ctxt
    in
    (* In the [then_] branch both the [is] and [as] refinements resulting from typing the condition expression apply *)
    let delta_then_ =
      let cont_ctxt = Ctxt.Cont.update_expr cont_ctxt ~expr_delta in
      let delta = Stmt.synth then_ ~def_ctxt ~cont_ctxt in
      (* Any type parameters in the delta came about because we unpacked an existential. To prevent these escaping the
         continuation we have to promote any occurrences of these type parameters inside types in the local environment
         to the upper or lower bound of the type parametes or, if any type parameter occurs invariantly, promote / demote
         the constructor to the first sub- or supertype which doesn't mention the type parameter *)
      Exposure.promote_delta delta
    (* In the [else_] branch on the [as] refinement resulting from typing the condition expression applies; in hh
       we also have negated types for classes and some primitives but this adds a lot of complexity so we just drop
       the refinements for now *)
    and delta_else_ =
      let expr_delta = Ctxt.Cont.Expr_delta.drop_rfmts expr_delta in
      let cont_ctxt = Ctxt.Cont.update_expr cont_ctxt ~expr_delta in
      let delta = Stmt.synth else_ ~def_ctxt ~cont_ctxt in
      Exposure.promote_delta delta
    in
    let prov = Prov.stmt_if_join span in
    Ctxt.Delta.join cont_ctxt ~tl:delta_then_ ~tr:delta_else_ ~prov
  ;;
end

and Seq : sig
  val synth : Lang.Seq.t * Span.t -> def_ctxt:Ctxt.Def.t -> cont_ctxt:Ctxt.Cont.t -> Ctxt.Delta.t
end = struct
  let rec synth_help span_return span_all stmts ~def_ctxt ~acc_ctxt ~acc_delta =
    match stmts with
    | [] -> acc_delta
    | stmt :: stmts ->
      (* Type the statement under the [next] continuation of the accumulated context, if it exists. *)
      (match Ctxt.next acc_ctxt with
       | Some cont_ctxt ->
         let delta = Stmt.synth stmt ~def_ctxt ~cont_ctxt in
         (* Appending the delta to the context means that we will see any local or type parameter bound in the current
            statement and any refinement made to a local or $this and any corresponding refinement to type parameters *)
         let acc_ctxt = Ctxt.update acc_ctxt ~delta
         and acc_delta = Ctxt.Delta.extend acc_delta ~with_:delta in
         synth_help (Some (Located.span_of stmt)) span_all stmts ~def_ctxt ~acc_ctxt ~acc_delta
       | None ->
         (* We don't have a next continuation which means the previous statment cause an [exit]. All subsequent
            statements are unreachable so we finish typing and raise a warning *)
         let _ : unit =
           let span_current = Located.span_of stmt in
           let span_dead = Span.meet span_current span_all in
           let warn = Warn.unreachable ~span_return ~span_dead in
           Eff.log_warning warn
         in
         acc_delta)
  ;;

  let synth (Lang.Seq.Seq stmts, span) ~def_ctxt ~cont_ctxt =
    match stmts with
    (* Using [Seq] to encode both non-empty sequences and no-ops so we have to
       handle the no-op case specially *)
    | [] -> Ctxt.Delta.create ~next:Ctxt.Cont.Delta.empty ()
    | _ ->
      let acc_ctxt = Ctxt.create ~next:cont_ctxt ()
      and acc_delta = Ctxt.Delta.empty in
      synth_help None span stmts ~def_ctxt ~acc_ctxt ~acc_delta
  ;;
end
