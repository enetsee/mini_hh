open Core
open Reporting

module Refinement = struct
  module Minimal = struct
    type t =
      { local : Local.Refinement.t
      ; ty_param : Ty_param.Refinement.t
      }
    [@@deriving create]

    let pp ppf t =
      Fmt.(
        vbox
        @@ record
             ~sep:cut
             [ field "locals" (fun { local; _ } -> local) Local.Refinement.pp
             ; field "type parameters" (fun { ty_param; _ } -> ty_param) Ty_param.Refinement.pp
             ])
        ppf
        t
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let empty = { local = Local.Refinement.empty; ty_param = Ty_param.Refinement.empty }
  let param_rfmnt { ty_param; _ } nm = Ty_param.Refinement.find ty_param nm
  let tm_var_rfmt { local; _ } nm = Local.Refinement.find local nm

  let invalidate_local ({ local; _ } as t) tm_var =
    let local = Local.Refinement.invalidate local tm_var in
    { t with local }
  ;;

  let meet { local = local1; ty_param = ty_param1 } { local = local2; ty_param = ty_param2 } ~prov =
    let local = Local.Refinement.meet local1 local2 ~prov
    and ty_param = Ty_param.Refinement.meet ty_param1 ty_param2 ~prov in
    { local; ty_param }
  ;;

  let join { local = local1; ty_param = ty_param1 } { local = local2; ty_param = ty_param2 } ~prov =
    let local = Local.Refinement.join local1 local2 ~prov
    and ty_param = Ty_param.Refinement.join ty_param1 ty_param2 ~prov in
    { local; ty_param }
  ;;
end

module Minimal = struct
  (** The per-continuation context *)
  type t =
    { local : Local.t (** Local variables bound in this continuation *)
    ; ty_param : Ty_param.t (** Type parameters bound in this continuation via unpacked existentials *)
    ; rfmts : Refinement.t list (** The stack of refinements corresponding to successive type tests, if any *)
    }
  [@@deriving create, show]

  let pp ppf t =
    Fmt.(
      vbox
      @@ record
           ~sep:cut
           [ field "locals" (fun { local; _ } -> local) Local.pp
           ; field "type parameters" (fun { ty_param; _ } -> ty_param) Ty_param.pp
           ; field "refinements" (fun { rfmts; _ } -> rfmts) @@ list ~sep:cut Refinement.pp
           ])
      ppf
      t
  ;;
end

include Minimal
include Pretty.Make (Minimal)

module Expr_delta = struct
  module Minimal = struct
    (** The incremental change in the per-continuation context after typing an expression
        TODO(mjt) when we have object access this should include the set of refinements on properties that have been
        invalidated *)
    type t =
      { rfmt : Refinement.t option (** [is] expressions may refine local variables and type parameters *)
      ; local : Local.t option (** [as] expressions redefine locals and type parameters *)
      ; ty_param : Ty_param.t option
      }
    [@@deriving create]

    let pp ppf t =
      Fmt.(
        vbox
        @@ record
             ~sep:cut
             [ field "Δ refinement" (fun { rfmt; _ } -> rfmt) @@ option ~none:(any "(none)") Refinement.pp
             ; field "Δ locals" (fun { local; _ } -> local) @@ option ~none:(any "(none)") Local.pp
             ; field "Δ type parameters" (fun { ty_param; _ } -> ty_param) @@ option ~none:(any "(none)") Ty_param.pp
             ])
        ppf
        t
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let empty = { rfmt = None; local = None; ty_param = None }
  let drop_rfmt t = { t with rfmt = None }

  let extend t ~with_ ~prov =
    let local = Option.merge ~f:(fun t with_ -> Local.extend t ~with_) t.local with_.local
    and ty_param = Option.merge ~f:(fun t with_ -> Ty_param.extend t ~with_) t.ty_param with_.ty_param
    and rfmt = Option.merge ~f:(Refinement.meet ~prov) t.rfmt with_.rfmt in
    { local; ty_param; rfmt }
  ;;
end

module Delta = struct
  module Minimal = struct
    (** The incremental change in the per-continuation context after typing a statement
        TODO(mjt) this should include the set of refinements on locals that have been invalidated and the set of properties
        that have been invalidated when that is implemented for expressions *)
    type t =
      { local : Local.t option (** We get changes in the [local] context from assignement and [as] expressions *)
      ; ty_param : Ty_param.t option (** We get changes in the [ty_param] context from [unpack] expressions *)
      }
    [@@deriving create]

    let pp ppf t =
      Fmt.(
        vbox
        @@ record
             ~sep:cut
             [ field "Δ locals" (fun { local; _ } -> local) @@ option ~none:(any "(none)") Local.pp
             ; field "Δ type parameters" (fun { ty_param; _ } -> ty_param) @@ option ~none:(any "(none)") Ty_param.pp
             ])
        ppf
        t
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let empty = { local = None; ty_param = None }
  let of_expr_delta Expr_delta.{ local; ty_param; _ } = { local; ty_param }

  let extend t ~with_ =
    let local = Option.merge t.local with_.local ~f:(fun t with_ -> Local.extend t ~with_)
    and ty_param = Option.merge t.ty_param with_.ty_param ~f:(fun t with_ -> Ty_param.extend t ~with_) in
    { local; ty_param }
  ;;

  let join t1 t2 ~prov =
    let local = Option.merge ~f:(Local.join ~prov) t1.local t2.local
    and ty_param = Option.merge ~f:(Ty_param.join ~prov) t1.ty_param t2.ty_param in
    { local; ty_param }
  ;;

  let meet t1 t2 ~prov =
    let local = Option.merge ~f:(Local.meet ~prov) t1.local t2.local
    and ty_param = Option.merge ~f:(Ty_param.meet ~prov) t1.ty_param t2.ty_param in
    { local; ty_param }
  ;;
end

let invalidate_local_refinement ({ rfmts; _ } as t) tm_var =
  let rfmts = List.map rfmts ~f:(fun rfmt -> Refinement.invalidate_local rfmt tm_var) in
  { t with rfmts }
;;

let empty = { local = Local.empty; ty_param = Ty_param.empty; rfmts = [] }

let update_expr t ~expr_delta:Expr_delta.{ rfmt; local; ty_param } =
  let local = Option.value_map local ~default:t.local ~f:(fun with_ -> Local.extend t.local ~with_)
  and rfmts = Option.value_map ~default:t.rfmts ~f:(fun rfmt -> rfmt :: t.rfmts) rfmt
  and ty_param = Option.value_map ty_param ~default:t.ty_param ~f:(fun with_ -> Ty_param.extend t.ty_param ~with_) in
  { local; rfmts; ty_param }
;;

let update t ~delta:Delta.{ local; ty_param } =
  let local = Option.value_map local ~default:t.local ~f:(fun with_ -> Local.extend t.local ~with_)
  and ty_param = Option.value_map ty_param ~default:t.ty_param ~f:(fun with_ -> Ty_param.extend t.ty_param ~with_) in
  { t with local; ty_param }
;;

(* ~~ Locals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Find the type of a term variable in the current continuation *)
let find_local t tm_var =
  Option.map ~f:(fun ty ->
    List.fold_left t.rfmts ~init:ty ~f:(fun ty rfmt ->
      Option.value_map ~default:ty ~f:(fun ty_rfmt -> Ty.refine ty ~rfmt:ty_rfmt) @@ Refinement.tm_var_rfmt rfmt tm_var))
  @@ Local.find t.local tm_var
;;

(* ~~ Type parameters ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** The type parameter refinements in the current continuation are the combination of those coming from a type
    assertion (`as`) and those coming from type tests (`is`). We can have at most one `as` refinement (subsequent
    assertions refine the existing one and never go out of scope) and possibly many `is` refinements corresponding
    to nested continuation scopes. It's possible to have `is` assignments without an `as`. *)
let ty_param_refinement_opt { rfmts; _ } nm =
  let rec aux acc res =
    match res with
    | Ty_param.Refinement.Bounds_top :: rest -> aux acc rest
    | Ty_param.Refinement.Bounds_bottom :: _ -> Some (Ty.Param_bounds.bottom Prov.empty)
    | Ty_param.Refinement.Bounds bounds :: rest ->
      let acc = Option.value_map ~default:bounds ~f:(fun acc -> Ty.Param_bounds.meet acc bounds ~prov:Prov.empty) acc in
      aux (Some acc) rest
    | [] -> acc
  in
  let rmfts = List.map rfmts ~f:(fun rfmnt -> Refinement.param_rfmnt rfmnt nm) in
  aux None rmfts
;;

(** The bounds for a type parameter including all refinements *)
let ty_param_bounds ({ ty_param; _ } as t) nm =
  Option.map ~f:(fun param_bounds ->
    Option.value_map ~default:param_bounds ~f:(fun param_refinement ->
      Ty.Param_bounds.meet param_bounds param_refinement ~prov:Prov.empty)
    @@ ty_param_refinement_opt t nm)
  @@ Ty_param.find ty_param nm
;;

let bind_ty_param ty_param Ty.Param.{ name = Located.{ elem; _ }; param_bounds } =
  Ty_param.bind ty_param elem param_bounds
;;

let bind_ty_params ({ ty_param; _ } as t) ty_params =
  let ty_param = List.fold_left ty_params ~init:ty_param ~f:bind_ty_param in
  { t with ty_param }
;;
