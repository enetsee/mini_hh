open Core
open Reporting
(*
   let step Cstr.Is_subtype.{ ty_sub; ty_super } ~ctxt:_ =
  let open Ty.Node in
  match Ty.(prj ty_sub, prj ty_super) with
  (* ~~ C-Top ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | _, (_, Inter []) -> Ok Prop.true_
  | (_prov_sub, Inter []), (_prov_super, _) -> Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Bot ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* -- C-Bot ------------------------------------------------------------------------------------------------------- *)
  (* | (_,Union []), _ ->  Ok Prop.true_
    | _, Ty.Union (ts, pr_sup) when Set.is_empty ts ->
      let pr_sub = Ty.prov_of ty_sub in
      return @@ Error (Err.Not_a_subtype (Prov.flow ~from:pr_sub ~into:pr_sup)) *)
  (* ~~ C-Base ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (_prov_sub, Base b1), (_prov_super, Base b2) ->
    if Common.Base.equal b1 b2 then Ok Prop.true_ else Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | _, _ -> Ok Prop.true_
;; *)

(* -- C-Top -------------------------------------------------------------------------------------------------------
      | _, Ty.Inter (ts, _) when Set.is_empty ts -> return @@ Ok Prop.true_
      | Ty.Inter (ts, pr_sub), _ when Set.is_empty ts ->
        return @@ Error (Err.Not_a_subtype (Prov.flow ~from:pr_sub ~into:(Ty.prov_of ty_sup)))
      (* -- C-Bot ------------------------------------------------------------------------------------------------------- *)
      | Ty.Union (ts, _), _ when Set.is_empty ts -> return @@ Ok Prop.true_
      | _, Ty.Union (ts, pr_sup) when Set.is_empty ts ->
        let pr_sub = Ty.prov_of ty_sub in
        return @@ Error (Err.Not_a_subtype (Prov.flow ~from:pr_sub ~into:pr_sup)) *)

(* module rec Is_subtype : sig
   (* val ask : Cstr.Is_subtype.t -> ctxt_cont:Ctxt.Cont.t -> Answer.t *)
   (* val tell : Cstr.Is_subtype.t -> ctxt_cont:Ctxt.Cont.t -> Err.t option *)
   val simplify: ty_sub:Ty.t -> ty_super: Ty.t -> ctxt_cont:Ctxt.Cont.t -> (Prop.t , Err.t) result
   end = struct *)
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
    (* ~~ C-Var ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
    (* ~~ C-Base ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (_prov_sub, Base b1), (_prov_super, Base b2) ->
    if Common.Base.equal b1 b2 then Ok Prop.true_ else Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | _, _ -> Ok Prop.true_
;;

(* ~~ C-Base ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~ C-Tuple ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

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
