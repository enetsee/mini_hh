open Core
open Reporting
open Common

let rec step_tuple_elem
  prov_sub
  params_sub
  prov_super
  params_super
  ~idx_sub
  ~idx_super
  ~cstrs
  =
  (* TODO(mjt) PROV!!!! *)
  match params_sub, params_super with
  (* ~~ Success conditions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* -- No (remaining) params -- *)
  | ([], [], None), ([], [], None) -> Ok cstrs
  (* -- Fewer optional and/or variadic params in the subtype than the supertype -- *)
  | ([], [], None), ([], _ :: _, _) -> Ok cstrs
  (* -- No variadic param in the supertype with variadic param in subtype -- *)
  | ([], [], None), ([], [], Some _) -> Ok cstrs
  (* -- Variadic params in both subtype and supertyep -- *)
  | ([], [], Some ty_sub), ([], [], Some ty_super) ->
    let cstr = Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super in
    Ok (cstr :: cstrs)
  (* ~~ Continuation conditions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* ~~ Match up required-required, optional-optional and variadic-variadic params ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* -- Match up required args -- *)
  | ( (ty_sub :: reqs_sub, opts_sub, var_sub)
    , (ty_super :: reqs_sup, opts_sup, var_sup) ) ->
    let cstr = Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super in
    let cstrs = cstr :: cstrs in
    let idx_sub = idx_sub + 1
    and idx_super = idx_super + 1 in
    step_tuple_elem
      prov_sub
      (reqs_sub, opts_sub, var_sub)
      prov_super
      (reqs_sup, opts_sup, var_sup)
      ~idx_sub
      ~idx_super
      ~cstrs
  (* -- Match up optional arguments -- *)
  | ([], ty_sub :: opts_sub, var_sub), ([], ty_super :: opts_sup, var_sup) ->
    let cstr = Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super in
    let cstrs = cstr :: cstrs in
    step_tuple_elem
      prov_sub
      ([], opts_sub, var_sub)
      prov_super
      ([], opts_sup, var_sup)
      ~idx_sub
      ~idx_super
      ~cstrs
  (* ~~ Match up optional-required and variadic-required params ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* -- Match a required param in the subtype with optional param in the supertype -- *)
  | ( (ty_sub :: reqs_sub, opts_sub, var_sub)
    , ([], ty_super :: opts_super, var_super) ) ->
    let cstr = Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super in
    let cstrs = cstr :: cstrs in
    step_tuple_elem
      prov_sub
      (reqs_sub, opts_sub, var_sub)
      prov_super
      ([], opts_super, var_super)
      ~idx_sub
      ~idx_super
      ~cstrs
  (* -- Match a required param in the subtype with a variadic param in the supertype -- *)
  | (ty_sub :: reqs_sub, opts_sub, var_sub), ([], [], Some ty_super) ->
    let cstr = Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super in
    let cstrs = cstr :: cstrs in
    step_tuple_elem
      prov_sub
      (reqs_sub, opts_sub, var_sub)
      prov_super
      ([], [], Some ty_super)
      ~idx_sub
      ~idx_super
      ~cstrs
  (* ~~ Match up variadic-optional and optional-variadic params ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* -- Match an optional param in the subtype with a variadic param in the supertype -- *)
  | ([], ty_sub :: opts_sub, var_sub), ([], [], Some ty_super) ->
    let cstr = Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super in
    let cstrs = cstr :: cstrs in
    step_tuple_elem
      prov_sub
      ([], opts_sub, var_sub)
      prov_super
      ([], [], Some ty_super)
      ~idx_sub
      ~idx_super
      ~cstrs
  (* -- Match a variadic param in the subtype with an optional param in the supertype -- *)
  | ([], [], Some ty_sub), ([], ty_super :: opts_super, var_super) ->
    let cstr = Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super in
    let cstrs = cstr :: cstrs in
    step_tuple_elem
      prov_sub
      ([], [], Some ty_sub)
      prov_super
      ([], opts_super, var_super)
      ~idx_sub
      ~idx_super
      ~cstrs
  (* ~~ Error conditions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* -- Fewer required params in subtype than in supertype -- *)
  | ([], _, _), ((_ :: _ as reqs), _, _) ->
    let n_sub = idx_sub + List.length reqs in
    Error
      (Err.tuple_arity_required ~prov_sub ~prov_super ~n_sub ~n_super:idx_super)
  (* -- Required params in subtype but no params in subtype -- *)
  | ((_ :: _ as reqs), _, _), ([], [], None) ->
    let n_super = idx_super + List.length reqs in
    Error
      (Err.tuple_arity_required ~prov_sub ~prov_super ~n_sub:idx_sub ~n_super)
  (* -- More optional params in the supertype with no params in the subtype -- *)
  | ([], (_ :: _ as opts), _), ([], [], None) ->
    let n_super = idx_super + List.length opts in
    Error
      (Err.tuple_arity_optional ~prov_sub ~prov_super ~n_sub:idx_sub ~n_super)
  (* -- Variadic param in the supertype with no params in the subtype -- *)
  | ([], [], Some _), ([], [], None) ->
    Error (Err.tuple_arity_variadic ~prov_sub ~prov_super)
;;

let step_tuple
  ~prov_sub
  ~tuple_sub:
    Ty.Tuple.{ required = reqs_sub; optional = opts_sub; variadic = var_sub }
  ~prov_super
  ~tuple_super:
    Ty.Tuple.
      { required = reqs_super; optional = opts_super; variadic = var_super }
  =
  let params_sub = reqs_sub, opts_sub, var_sub
  and params_super = reqs_super, opts_super, var_super in
  Result.map ~f:(fun props -> Prop.conj @@ List.rev props)
  @@ step_tuple_elem
       prov_sub
       params_sub
       prov_super
       params_super
       ~idx_sub:0
       ~idx_super:0
       ~cstrs:[]
;;

let step_fn ~prov_sub ~fn_sub ~prov_super ~fn_super =
  (* TODO(mjt) PROV!!!! In general, this is cute but we'd have to post-process the provenance and remember we were
     inside function params *)
  let Ty.Fn.{ params = params_sub; return = return_sub } = fn_sub
  and Ty.Fn.{ params = params_super; return = return_super } = fn_super in
  let tuple_sub =
    let node = Ty.Node.Tuple params_sub in
    Ty.create ~node ~prov:prov_sub ()
  and tuple_super =
    let node = Ty.Node.Tuple params_super in
    Ty.create ~node ~prov:prov_super ()
  in
  Ok
    Prop.(
      conj
        [ atom @@ Cstr.is_subtype ~ty_sub:tuple_super ~ty_super:tuple_sub
        ; atom @@ Cstr.is_subtype ~ty_sub:return_sub ~ty_super:return_super
        ])
;;

let step_ctor_args ~prov_sub:_ ~args_sub ~prov_super:_ ~args_super vs =
  let rec aux ~idx ~args_sub ~args_super ~vs ~props =
    match args_sub, args_super, vs with
    | [], [], [] -> Ok (Prop.conj @@ List.rev props)
    | arg_sub :: args_sub, arg_super :: args_super, variance :: vs ->
      (* TODO(mjt) PROV!!!! *)
      let props =
        match Located.elem variance with
        | Variance.Cov ->
          let prop =
            Prop.atom @@ Cstr.is_subtype ~ty_sub:arg_sub ~ty_super:arg_super
          in
          prop :: props
        | Variance.Contrav ->
          let prop =
            Prop.atom @@ Cstr.is_subtype ~ty_sub:arg_super ~ty_super:arg_sub
          in
          prop :: props
        | Variance.Inv ->
          let prop_cov =
            Prop.atom @@ Cstr.is_subtype ~ty_sub:arg_sub ~ty_super:arg_super
          and prop_cotrav =
            Prop.atom @@ Cstr.is_subtype ~ty_sub:arg_super ~ty_super:arg_sub
          in
          prop_cov :: prop_cotrav :: props
      in
      aux ~idx:(idx + 1) ~args_sub ~args_super ~vs ~props
    | _ -> failwith "arity"
  in
  aux ~idx:0 ~args_sub ~args_super ~vs ~props:[]
;;

let step_ctor ~prov_sub ~ctor_sub ~prov_super ~ctor_super =
  let Ty.Ctor.{ name = name_sub; args = args_sub } = ctor_sub
  and Ty.Ctor.{ name = name_super; args = args_super } = ctor_super in
  let vs = Option.value_exn @@ Eff.ask_ty_param_variances ctor_sub.name in
  if Name.Ctor.equal name_sub name_super
  then step_ctor_args ~prov_sub ~args_sub ~prov_super ~args_super vs
  else (
    match Eff.ask_up ~of_:ctor_sub ~at:ctor_super.name with
    | Not_a_subclass ->
      let ty_sub =
        let node = Ty.Node.Ctor ctor_sub in
        Ty.create ~prov:prov_sub ~node ()
      and ty_super =
        let node = Ty.Node.Ctor ctor_super in
        Ty.create ~prov:prov_super ~node ()
      in
      Error (Err.not_a_subtype ~ty_sub ~ty_super)
    | Direct args_up | Transitive args_up ->
      (* TODO(mjt) we need the declaration position to produce the exends prov *)
      step_ctor_args ~prov_sub ~args_sub:args_up ~prov_super ~args_super vs)
;;

let step ~ty_sub ~ty_super ~ctxt_cont =
  let open Ty.Node in
  match Ty.(prj ty_sub, prj ty_super) with
  (* ~~ C-Top ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | ( ( _prov_sub
      , ( Union _
        | Inter _
        | Exists _
        | Fn _
        | Generic _
        | Tuple _
        | Ctor _
        | Nonnull
        | Base _ ) )
    , (_prov_super, Inter []) ) -> Ok Prop.true_
  | ( (_prov_sub, Inter [])
    , ( _prov_super
      , ( Union _
        | Inter (_ :: _)
        | Exists _ | Fn _ | Generic _ | Tuple _ | Ctor _ | Nonnull | Base _ ) )
    ) -> Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Bot ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | ( (_, Union [])
    , ( _
      , ( Union _
        | Inter _
        | Exists _
        | Fn _
        | Generic _
        | Tuple _
        | Ctor _
        | Nonnull
        | Base _ ) ) ) -> Ok Prop.true_
  | ( ( _
      , ( Union (_ :: _)
        | Inter _
        | Exists _
        | Fn _
        | Generic _
        | Tuple _
        | Ctor _
        | Nonnull
        | Base _ ) )
    , (_, Union []) ) -> Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Union-L ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | ( (prov_sub, Union tys_sub)
    , ( _
      , ( Union (_ :: _)
        | Inter (_ :: _)
        | Exists _ | Fn _ | Generic _ | Tuple _ | Ctor _ | Nonnull | Base _ ) )
    ) ->
    let props =
      List.map tys_sub ~f:(fun ty ->
        let ty_sub =
          Ty.map_prov ty ~f:(fun sub_prj ->
            Prov.prj_union_sub ~sub_prj ~sub:prov_sub)
        in
        Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
    in
    Ok (Prop.conj props)
  (* ~~ C-Inter-R ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | ( ( _
      , ( Inter (_ :: _)
        | Exists _ | Fn _ | Generic _ | Tuple _ | Ctor _ | Nonnull | Base _ ) )
    , (prov_super, Inter tys_super) ) ->
    let props =
      List.map tys_super ~f:(fun ty ->
        let ty_super =
          Ty.map_prov ty ~f:(fun super_prj ->
            Prov.prj_inter_super ~super_prj ~super:prov_super)
        in
        Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
    in
    Ok (Prop.conj props)
  (* ~~ C-Union-R ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | ( ( _
      , ( Inter (_ :: _)
        | Exists _ | Fn _ | Generic _ | Tuple _ | Ctor _ | Nonnull | Base _ ) )
    , (prov_super, Union tys_super) ) ->
    let props =
      List.map tys_super ~f:(fun ty ->
        let ty_super =
          Ty.map_prov ty ~f:(fun super_prj ->
            Prov.prj_union_super ~super_prj ~super:prov_super)
        in
        Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
    in
    Ok (Prop.disj props)
  (* ~~ C-Inter-L ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | ( (prov_sub, Inter tys_sub)
    , (_, (Exists _ | Fn _ | Generic _ | Tuple _ | Ctor _ | Nonnull | Base _)) )
    ->
    let props =
      List.map tys_sub ~f:(fun ty ->
        let ty_sub =
          Ty.map_prov ty ~f:(fun sub_prj ->
            Prov.prj_inter_sub ~sub_prj ~sub:prov_sub)
        in
        Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
    in
    Ok (Prop.disj props)
  (* ~~ C-Var ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* ~~ C-Generic ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (_prov_sub, Generic name_sub), (_prov_super, Generic name_super)
    when Name.Ty_param.equal name_sub name_super -> Ok Prop.true_
  | ( (_, (Exists _ | Fn _ | Generic _ | Tuple _ | Ctor _ | Nonnull | Base _))
    , (prov_super, Generic name_super) ) ->
    let ty_super =
      let Ty.Param_bounds.{ lower; _ } =
        Option.value_exn @@ Ctxt.Cont.ty_param_bounds ctxt_cont name_super
      in
      Ty.map_prov lower ~f:(fun bound ->
        Prov.axiom_lower_bound ~bound ~of_:prov_super)
    in
    Ok (Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
  | ( (prov_sub, Generic name_sub)
    , (_prov_super, (Exists _ | Fn _ | Tuple _ | Ctor _ | Nonnull | Base _)) )
    ->
    let ty_sub =
      let Ty.Param_bounds.{ upper; _ } =
        Option.value_exn @@ Ctxt.Cont.ty_param_bounds ctxt_cont name_sub
      in
      Ty.map_prov upper ~f:(fun bound ->
        Prov.axiom_upper_bound ~bound ~of_:prov_sub)
    in
    Ok (Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
  (* ~~ C-Exists (TODO) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (_prov_sub, Exists _exists_sub), (_prov_super, Exists _exists_super) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | ( (_prov_sub, (Fn _ | Tuple _ | Ctor _ | Nonnull | Base _))
    , (_prov_super, Exists _exist_super) ) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | ( (_prov_sub, Exists _exists_sub)
    , (_prov_super, (Fn _ | Tuple _ | Ctor _ | Nonnull | Base _)) ) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Nonnull ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (_, Nonnull), (_, (Fn _ | Tuple _ | Ctor _ | Base _)) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | (_, (Fn _ | Tuple _ | Ctor _ | Nonnull | Base _)), (_, Nonnull) ->
    Ok Prop.true_
  (* ~~ C-Fn ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_sub, Fn fn_sub), (prov_super, Fn fn_super) ->
    step_fn ~prov_sub ~fn_sub ~prov_super ~fn_super
  | (_prov_sub, (Tuple _ | Ctor _ | Base _)), (_prov_super, Fn _fn_super) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | (_prov_sub, Fn _fn_sub), (_prov_super, (Tuple _ | Ctor _ | Base _)) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Ctor ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_sub, Ctor ctor_sub), (prov_super, Ctor ctor_super) ->
    step_ctor ~prov_sub ~ctor_sub ~prov_super ~ctor_super
  | (_prov_sub, Ctor _ctor_sub), (_prov_super, (Tuple _ | Base _)) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | (_prov_sub, (Tuple _ | Base _)), (_prov_super, Ctor _ctor_super) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Tuple ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_sub, Tuple tuple_sub), (prov_super, Tuple tuple_super) ->
    step_tuple ~prov_sub ~tuple_sub ~prov_super ~tuple_super
  | (_prov_sub, Base _), (_prov_super, Tuple _tuple_super) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | (_prov_sub, Tuple _tuple_sub), (_prov_super, Base _) ->
    Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Base ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (_prov_sub, Base base_sub), (_prov_super, Base base_super) ->
    if Common.Base.equal base_sub base_super
    then Ok Prop.true_
    else Error (Err.not_a_subtype ~ty_sub ~ty_super)
;;

(* ~~ Ask / tell API ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* let tell Cstr.Is_subtype.{ ty_sub; ty_super } ~ctxt_cont =
  match simplify ~ty_sub ~ty_super ~cont_ctxt with
  | _ -> failwith ""
;;

let ask Cstr.Is_subtype.{ ty_sub; ty_super } ~ctxt_cont =
  match simplify ~ty_sub ~ty_super ~cont_ctxt with
  | Ok (Prop.Conj []) -> Answer.Yes
  | Ok _ -> Answer.Maybe
  | Error err -> Answer.No err
;; *)
