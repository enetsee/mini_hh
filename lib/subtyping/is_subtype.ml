open Core
open Reporting

(* let step_tuple
  ~prov_sub
  ~tuple_sub:Ty.Tuple.{ required = req_sub; optional = opt_sub; variadic = var_sub }
  ~prov_super
  ~tuple_super:Ty.Tuple.{ required = req_super; optional = opt_super; variadic = var_super }
  =
  let rec aux params_sub params_sup ~idx ~cstrs =
    match params_sub, params_sup with
    (* == Success conditions ====================================================================================== *)
    (* -- No (remaining) params -- *)
    | ([], [], None), ([], [], None) -> Ok cstrs
    (* -- Fewer optional and/or variadic params in the supertype than the subtype -- *)
    | ([], _ :: _, _), ([], [], None) -> Ok cstrs
    (* -- No variadic param in the supertype with variadic param in subtype -- *)
    | ([], [], Some _), ([], [], None) -> Ok cstrs
    (* == Match up required-required, optional-optional and variadic-variadic params ============================== *)
    (* -- Match up required args  - TODO inout checks etc -- *)
    | (ty_sub :: reqs_sub, opts_sub, var_sub), (ty_sup :: reqs_sup, opts_sup, var_sup) ->
      let into = Prov.(proj_fn_arg idx Contravariant @@ append pr_sup (rev pr_sub)) in
      let ty_sup = Ty.update_prov ty_sup ~f:(fun from -> Prov.flow ~from ~into) in
      (* Contravariance *)
      let cstr = Cstr.is_subtype ty_sup ~of_:ty_sub in
      let cstrs = cstr :: cstrs in
      aux (reqs_sub, opts_sub, var_sub) (reqs_sup, opts_sup, var_sup) ~idx:(idx + 1) ~cstrs
    (* -- Match up optional arguments -- *)
    | ([], ty_sub :: opts_sub, var_sub), ([], ty_sup :: opts_sup, var_sup) ->
      let into = Prov.(proj_fn_arg idx Contravariant @@ flow ~from:pr_sup ~into:(rev pr_sub)) in
      let ty_sup = Ty.update_prov ty_sup ~f:(fun from -> Prov.flow ~from ~into) in
      (* Contravariance *)
      let cstr = Cstr.is_subtype ty_sup ~of_:ty_sub in
      let cstrs = cstr :: cstrs in
      aux ([], opts_sub, var_sub) ([], opts_sup, var_sup) ~idx:(idx + 1) ~cstrs
    (* -- Match up variadic args -- *)
    | ([], [], Some ty_sub), ([], [], Some ty_sup) ->
      let into = Prov.(proj_fn_arg idx Contravariant @@ flow ~from:pr_sup ~into:(rev pr_sub)) in
      let ty_sup = Ty.update_prov ty_sup ~f:(fun from -> Prov.flow ~from ~into) in
      (* Contravariance *)
      let cstr = Cstr.is_subtype ty_sup ~of_:ty_sub in
      Ok (cstr :: cstrs)
    (* == Match up optional-required and variadic-required params ================================================= *)
    (* -- Match a required param in the supertype with optional param in the subtype -- *)
    | ([], ty_sub :: opts_sub, var_sub), (ty_sup :: reqs_sup, opts_sup, var_sup) ->
      let into = Prov.(proj_fn_arg idx Contravariant @@ flow ~from:pr_sup ~into:(rev pr_sub)) in
      let ty_sup = Ty.update_prov ty_sup ~f:(fun from -> Prov.flow ~from ~into) in
      (* Contravariance *)
      let cstr = Cstr.is_subtype ty_sup ~of_:ty_sub in
      let cstrs = cstr :: cstrs in
      aux ([], opts_sub, var_sub) (reqs_sup, opts_sup, var_sup) ~idx:(idx + 1) ~cstrs
    (* -- Match a required param in the supertype with a variadic param in the subtype -- *)
    | ([], [], Some ty_sub), (ty_sup :: reqs_sup, opts_sup, var_sup) ->
      let into = Prov.(proj_fn_arg idx Contravariant @@ flow ~from:pr_sup ~into:(rev pr_sub)) in
      let ty_sup = Ty.update_prov ty_sup ~f:(fun from -> Prov.flow ~from ~into) in
      (* Contravariance *)
      let cstr = Cstr.is_subtype ty_sup ~of_:ty_sub in
      let cstrs = cstr :: cstrs in
      aux ([], [], Some ty_sub) (reqs_sup, opts_sup, var_sup) ~idx:(idx + 1) ~cstrs
    (* == Match up variadic-optional and optional-variadic params ================================================= *)
    (* -- Match an optional param in the supertype with a variadic param in the subtype -- *)
    | ([], [], Some ty_sub), ([], ty_sup :: opts_sup, var_sup) ->
      let into = Prov.(proj_fn_arg idx Contravariant @@ flow ~from:pr_sup ~into:(rev pr_sub)) in
      let ty_sup = Ty.update_prov ty_sup ~f:(fun from -> Prov.flow ~from ~into) in
      (* Contravariance *)
      let cstr = Cstr.is_subtype ty_sup ~of_:ty_sub in
      let cstrs = cstr :: cstrs in
      aux ([], [], Some ty_sub) ([], opts_sup, var_sup) ~idx:(idx + 1) ~cstrs
    (* -- Match a variadic param in the supertype with an optional param in the subtype -- *)
    | ([], ty_sub :: opts_sub, var_sub), ([], [], Some ty_sup) ->
      let into = Prov.(proj_fn_arg idx Contravariant @@ flow ~from:pr_sup ~into:(rev pr_sub)) in
      let ty_sup' = Ty.update_prov ty_sup ~f:(fun from -> Prov.flow ~from ~into) in
      (* Contravariance *)
      let cstr = Cstr.is_subtype ty_sup' ~of_:ty_sub in
      let cstrs = cstr :: cstrs in
      aux ([], opts_sub, var_sub) ([], [], Some ty_sup) ~idx:(idx + 1) ~cstrs
    (* == Error conditions ======================================================================================== *)
    (* -- Fewer required params in supertype than in subtype -- *)
    | (ty_sub :: _, _, _), ([], _, _) ->
      let from = Ty.prov_of ty_sub in
      Error (Err.Not_a_subtype (Prov.flow ~from ~into:Prov.empty))
    (* -- Required params in supertype but no params in subtype -- *)
    | ([], [], None), (ty_sup :: _, _, _) ->
      let into = Ty.prov_of ty_sup in
      Error (Err.Not_a_subtype (Prov.flow ~from:Prov.empty ~into))
    (* -- More optional params in the supertype with no params in the subtype -- *)
    | ([], [], None), ([], ty_sup :: _, _) ->
      let into = Ty.prov_of ty_sup in
      Error (Err.Not_a_subtype (Prov.flow ~from:Prov.empty ~into))
    (* -- Variadic param in the supertype with no params in the subtype -- *)
    | ([], [], None), ([], [], Some ty_sup) ->
      let into = Ty.prov_of ty_sup in
      Error (Err.Not_a_subtype (Prov.flow ~from:Prov.empty ~into))
  in
  aux (reqs_sub, opts_sub, var_sub) (reqs_sup, opts_sup, var_sup) ~idx:0 ~cstrs:[]
;; *)

let step ~ty_sub ~ty_super ~ctxt_cont:_ =
  let open Ty.Node in
  match Ty.(prj ty_sub, prj ty_super) with
  (* ~~ C-Top ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | _, (_, Inter []) -> Ok Prop.true_
  | (_prov_sub, Inter []), (_prov_super, _) -> Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Bot ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (_, Union []), _ -> Ok Prop.true_
  | _, (_, Union []) -> Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Union-L ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_sub, Union tys_sub), _ ->
    let props =
      List.map tys_sub ~f:(fun ty ->
        let ty_sub = Ty.map_prov ty ~f:(fun sub_prj -> Prov.prj_union_sub ~sub_prj ~sub:prov_sub) in
        Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
    in
    Ok (Prop.conj props)
  (* ~~ C-Inter-R ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | _, (prov_super, Inter tys_super) ->
    let props =
      List.map tys_super ~f:(fun ty ->
        let ty_super = Ty.map_prov ty ~f:(fun super_prj -> Prov.prj_inter_super ~super_prj ~super:prov_super) in
        Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
    in
    Ok (Prop.conj props)
  (* ~~ C-Union-R ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | _, (prov_super, Union tys_super) ->
    let props =
      List.map tys_super ~f:(fun ty ->
        let ty_super = Ty.map_prov ty ~f:(fun super_prj -> Prov.prj_union_super ~super_prj ~super:prov_super) in
        Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
    in
    Ok (Prop.disj props)
  (* ~~ C-Inter-L ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_sub, Inter tys_sub), _ ->
    let props =
      List.map tys_sub ~f:(fun ty ->
        let ty_sub = Ty.map_prov ty ~f:(fun sub_prj -> Prov.prj_inter_sub ~sub_prj ~sub:prov_sub) in
        Prop.atom @@ Cstr.is_subtype ~ty_sub ~ty_super)
    in
    Ok (Prop.disj props)
    (* ~~ C-Var ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
    (* ~~ C-Tuple ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
    (* | (prov_sub, Tuple tuple_sub), (prov_super, Tuple tuple_super) ->
       step_tuple ~prov_sub ~tuple_sub ~prov_super ~tuple_super ~ctxt_cont *)
    (* ~~ C-Base ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (_prov_sub, Base base_sub), (_prov_super, Base base_super) ->
    if Common.Base.equal base_sub base_super then Ok Prop.true_ else Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | _, _ -> Ok Prop.true_
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
