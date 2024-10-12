open Core

module Fn = struct
  type t = { ret_ty : Ty.t } [@@deriving create, show]
end

module Local = struct
  (** A local environment is a map from term variables names to *)
  type t = Ty.t Name.Tm_var.Map.t [@@deriving compare, eq, sexp, show]

  let empty = Name.Tm_var.Map.empty
  let bottom = empty
  let find t local = Map.find t local
  let is_bound t local = Option.is_some @@ find t local

  let join t1 t2 ~prov =
    let f ~key:_ = function
      | `Left ty | `Right ty -> Some ty
      | `Both (ty1, ty2) -> Some (Ty.union ~prov [ ty1; ty2 ])
    in
    Map.merge t1 t2 ~f
  ;;

  let meet t1 t2 ~prov =
    let f ~key:_ = function
      | `Left _ | `Right _ -> None
      | `Both (ty1, ty2) -> Some (Ty.inter ~prov [ ty1; ty2 ])
    in
    Map.merge t1 t2 ~f
  ;;

  let merge_right t1 t2 : t =
    let f ~key:_ = function
      | `Left v | `Right v | `Both (_, v) -> Some v
    in
    Map.merge t1 t2 ~f
  ;;

  let merge_disjoint_exn t1 t2 = Map.merge_disjoint_exn t1 t2
  let bind_local t local ty = Map.update t local ~f:(fun _ -> ty)
  let map t ~f = Name.Tm_var.Map.map t ~f

  let symm_diff (t1 : t) (t2 : t) =
    let k1 = Map.key_set t1
    and k2 = Map.key_set t2 in
    Set.symmetric_diff k1 k2
  ;;
end

(* module Ty_refine = struct
  module Refine_key = struct
    (** A type refinement key is either a term variable or a member property
        TODO(mjt) Add members *)
    type t = Local of Name.Tm_var.t [@@deriving compare, eq, sexp, show]
  end

  module Refine_map = struct
    include Map.Make (Refine_key)

    let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Refine_key.pp pp_a) ppf @@ Map.to_alist t
  end

  type t = Ty.Refinement.t Refine_map.t [@@deriving compare, eq, sexp, show]

  let empty = Refine_map.empty
  let find_local t local = Map.find t (Refine_key.Local local)

  let join t1 t2 =
    let f ~key:_ = function
      | `Left rfn | `Right rfn -> Some rfn
      | `Both (rfn1, rfn2) -> Some (Ty.Refinement.join rfn1 rfn2)
    in
    Map.merge t1 t2 ~f
  ;;

  let meet t1 t2 =
    let f ~key:_ = function
      | `Left _ | `Right _ -> None
      | `Both (rfn1, rfn2) -> Some (Ty.Refinement.meet rfn1 rfn2)
    in
    Map.merge t1 t2 ~f
  ;;

  let cmp t = Refine_map.map t ~f:Ty.Refinement.cmp
  let of_local local ty : t = Refine_map.singleton Refine_key.(Local local) @@ Ty.Refinement.pos ty
end *)

module Cont = struct
  type t =
    { local : Local.t (* ; ty_refine : Ty_refine.t *)
    ; ty_param : Ty.Param.Ctxt.t
    ; ty_param_refine : Ty.Param.Refinement.t
    ; this_refine : Refinement.t
    }
end

module Global = struct
  type t =
    { oracle : Oracle.t
    ; subtyping_state : Subtyping.State.t
    ; errs : Err.t list
    (** Subtyping state which will maintain constraints asubtyping_env nd solutions to type variables when we have them *)
    ; classish : Name.Ctor.t option (** The name of the classish construct we are within, if any *)
    ; fn : Fn.t option (** The current function context if any *)
    }
  [@@deriving create, show]
end

let find_local Cont.{ local; _ } tm_var =
  (* TODO(mjt) apply refinements *)
  Local.find local tm_var
;;

let tell_is_subtype
  Global.({ oracle; subtyping_state = state; errs; _ } as ctxt)
  Cont.{ ty_param; ty_param_refine; _ }
  ~ty_sub
  ~ty_super
  =
  let subtyping_ctxt = Subtyping.Ctxt.create ~oracle ~ty_param ~ty_param_refine () in
  match Subtyping.Tell.is_subtype ~ty_sub ~ty_super ~ctxt:subtyping_ctxt ~state with
  | Error err -> { ctxt with errs = Err.subtyping err :: errs }
  | Ok subtyping_state -> { ctxt with subtyping_state }
;;
