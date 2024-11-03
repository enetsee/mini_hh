open Core
open Reporting

module Refinements = struct
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

  (** Lifts [meet] on locals and type parameters *)
  let meet { local = local1; ty_param = ty_param1 } { local = local2; ty_param = ty_param2 } ~prov =
    let local = Local.Refinement.meet local1 local2 ~prov
    and ty_param = Ty_param.Refinement.meet ty_param1 ty_param2 ~prov in
    { local; ty_param }
  ;;

  (** Lifts [join] on locals and type parameters *)
  let join { local = local1; ty_param = ty_param1 } { local = local2; ty_param = ty_param2 } ~prov =
    let local = Local.Refinement.join local1 local2 ~prov
    and ty_param = Ty_param.Refinement.join ty_param1 ty_param2 ~prov in
    { local; ty_param }
  ;;
end

module Bindings = struct
  module Minimal = struct
    type t =
      { local : Local.t
      ; ty_param : Ty_param.t
      }
    [@@deriving create]

    let pp ppf t =
      Fmt.(
        vbox
        @@ record
             ~sep:cut
             [ field "locals" (fun { local; _ } -> local) Local.pp
             ; field "type parameters" (fun { ty_param; _ } -> ty_param) Ty_param.pp
             ])
        ppf
        t
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let empty = { local = Local.empty; ty_param = Ty_param.empty }

  let extend t ~with_ =
    let local = Local.extend t.local ~with_:with_.local
    and ty_param = Ty_param.extend t.ty_param ~with_:with_.ty_param in
    { local; ty_param }
  ;;

  let bind_local ({ local; _ } as t) tm_var ty =
    let local = Local.bind local tm_var ty in
    { t with local }
  ;;

  let bind_locals ({ local; _ } as t) locals =
    let local = Local.bind_all local locals in
    { t with local }
  ;;

  let bind_ty_params ({ ty_param; _ } as t) ty_params =
    let ty_param = Ty_param.bind_all ty_param ty_params in
    { t with ty_param }
  ;;

  let bind_ty_param ({ ty_param; _ } as t) nm bounds =
    let ty_param = Ty_param.bind ty_param nm bounds in
    { t with ty_param }
  ;;
end

module Expr_delta = struct
  module Minimal = struct
    (** The incremental change in the per-continuation context after typing an expression
        TODO(mjt) when we have object access this should include the set of refinements on properties that have been
        invalidated *)
    type t =
      { rfmts : Refinements.t option (** [is] expressions may refine local variables and type parameters *)
      ; bindings : Bindings.t option (** [as] expressions redefine locals and type parameters *)
      }
    [@@deriving create]

    let pp ppf t =
      Fmt.(
        vbox
        @@ record
             ~sep:cut
             [ field "Δ refinements" (fun { rfmts; _ } -> rfmts) @@ option ~none:(any "(none)") Refinements.pp
             ; field "Δ bindings" (fun { bindings; _ } -> bindings) @@ option ~none:(any "(none)") Bindings.pp
             ])
        ppf
        t
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let empty = { rfmts = None; bindings = None }
  let drop_rfmts { bindings; _ } = { bindings; rfmts = None }

  (* let extend t ~with_ ~prov =
    let local = Option.merge ~f:(fun t with_ -> Local.extend t ~with_) t.local with_.local
    and ty_param = Option.merge ~f:(fun t with_ -> Ty_param.extend t ~with_) t.ty_param with_.ty_param
    and rfmt = Option.merge ~f:(Refinement.meet ~prov) t.rfmt with_.rfmt in
    { local; ty_param; rfmt }
  ;;

  let meet t1 t2 ~prov = extend t1 ~with_:t2 ~prov

  let join t1 t2 ~prov =
    let local = Option.merge ~f:(Local.join ~prov) t1.local t2.local
    and ty_param = Option.merge ~f:(Ty_param.join ~prov) t1.ty_param t2.ty_param
    and rfmt = Option.map2 ~f:(Refinement.join ~prov) t1.rfmt t2.rfmt in
    { local; ty_param; rfmt }
  ;; *)
end

module Delta = struct
  module Minimal = struct
    (** The incremental change in the per-continuation context after typing a statement
        TODO(mjt) this should include the set of refinements on locals that have been invalidated and the set of properties
        that have been invalidated when that is implemented for expressions *)
    type t =
      { bindings : Bindings.t option
      (** We get changes in local and type parameter bindings from [assign] and [unpack] statements and [as] expressions *)
      }
    [@@deriving create]

    let pp ppf t =
      Fmt.(
        vbox
        @@ record
             ~sep:cut
             [ field "Δ bindings" (fun { bindings; _ } -> bindings) @@ option ~none:(any "(none)") Bindings.pp ])
        ppf
        t
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let empty = { bindings = None }
  let of_expr_delta Expr_delta.{ bindings; _ } = { bindings }

  let extend t ~with_ =
    let bindings = Option.merge t.bindings with_.bindings ~f:(fun t with_ -> Bindings.extend t ~with_) in
    { bindings }
  ;;

  let join t1 t2 ~prov =
    let bindings =
      Option.merge t1.bindings t2.bindings ~f:(fun { local = l1; ty_param = tp1 } { local = l2; ty_param = tp2 } ->
        assert (Ty_param.is_empty tp1);
        assert (Ty_param.is_empty tp2);
        let local = Local.join l1 l2 ~prov in
        Bindings.create ~local ~ty_param:tp1 ())
    in
    { bindings }
  ;;

  (* let locals = Option.merge ~f:(Local.join ~prov) t1.bindings.local t2.bindings.local
    and ty_param = Option.merge ~f:(Ty_param.join ~prov) t1.ty_param t2.ty_param in
    { locals; ty_param } *)

  (*  let meet t1 t2 ~prov =
    let local = Option.merge ~f:(Local.meet ~prov) t1.local t2.local
    and ty_param = Option.merge ~f:(Ty_param.meet ~prov) t1.ty_param t2.ty_param in
    { local; ty_param }
  ;; *)
end

module Cont = struct
  module Minimal = struct
    (** The per-continuation context *)
    type t =
      { bindings : Bindings.t (** Local variables & type parameters bound in this continuation *)
      ; rfmtss : Refinements.t option list
      (** The stack of refinements corresponding to successive type tests, if any *)
      }
    [@@deriving create, show]

    let pp ppf t =
      Fmt.(
        vbox
        @@ record
             ~sep:cut
             [ field "bindings" (fun { bindings; _ } -> bindings) Bindings.pp
             ; field "refinements" (fun { rfmtss; _ } -> rfmtss)
               @@ list ~sep:cut
               @@ option ~none:(any "(no refinements)") Refinements.pp
             ])
        ppf
        t
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let invalidate_local_refinement ({ rfmtss; _ } as t) tm_var =
    let rfmtss =
      List.map rfmtss ~f:(fun rfmt_opt -> Option.map rfmt_opt ~f:(fun rfmt -> Refinements.invalidate_local rfmt tm_var))
    in
    { t with rfmtss }
  ;;

  let empty = { bindings = Bindings.empty; rfmtss = [] }

  (** Update the context with the changes resulting from typing an expression. This means:
      - extending the bindings so that we prefer locals and type parameters resulting from typing the expression
      - pushing any refinements onto the stack *)

  let update_expr t ~expr_delta:Expr_delta.{ rfmts; bindings } =
    let bindings = Option.value_map bindings ~default:t.bindings ~f:(fun with_ -> Bindings.extend t.bindings ~with_)
    and rfmtss = rfmts :: t.rfmtss in
    { bindings; rfmtss }
  ;;

  let update t ~delta:Delta.{ bindings } =
    let bindings = Option.value_map bindings ~default:t.bindings ~f:(fun with_ -> Bindings.extend t.bindings ~with_) in
    { t with bindings }
  ;;

  (* ~~ Locals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  (** Find the type of a term variable in the current continuation given the current bindings and in-scope refinements *)
  let find_local t tm_var =
    Option.map ~f:(fun ty ->
      List.fold_left t.rfmtss ~init:ty ~f:(fun ty rfmt_opt ->
        Option.value_map ~default:ty ~f:(fun ty_rfmt -> Ty.refine ty ~rfmt:ty_rfmt)
        @@ Option.bind rfmt_opt ~f:(fun rfmt -> Refinements.tm_var_rfmt rfmt tm_var)))
    @@ Local.find t.bindings.local tm_var
  ;;

  (* ~~ Type parameters ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  (** The type parameter refinements in the current continuation are the combination of those coming from a type
      assertion (`as`) and those coming from type tests (`is`). We can have at most one `as` refinement (subsequent
      assertions refine the existing one and never go out of scope) and possibly many `is` refinements corresponding
      to nested continuation scopes. It's possible to have `is` assignments without an `as`. *)
  let ty_param_refinement_opt { rfmtss; _ } nm =
    let rec aux acc res =
      match res with
      | Ty_param.Refinement.Bounds_top :: rest -> aux acc rest
      | Ty_param.Refinement.Bounds_bottom :: _ -> Some (Ty.Param_bounds.bottom Prov.empty)
      | Ty_param.Refinement.Bounds bounds :: rest ->
        let acc =
          Option.value_map ~default:bounds ~f:(fun acc -> Ty.Param_bounds.meet acc bounds ~prov:Prov.empty) acc
        in
        aux (Some acc) rest
      | [] -> acc
    in
    let rmfts =
      List.filter_map rfmtss ~f:(fun rfmt_opt -> Option.map rfmt_opt ~f:(fun rfmt -> Refinements.param_rfmnt rfmt nm))
    in
    aux None rmfts
  ;;

  (** The bounds for a type parameter including all refinements *)
  let ty_param_bounds t nm =
    Option.map ~f:(fun param_bounds ->
      Option.value_map ~default:param_bounds ~f:(fun param_refinement ->
        Ty.Param_bounds.meet param_bounds param_refinement ~prov:Prov.empty)
      @@ ty_param_refinement_opt t nm)
    @@ Ty_param.find t.bindings.ty_param nm
  ;;

  let bind_ty_param t Ty.Param.{ name = Located.{ elem; _ }; param_bounds } =
    let bindings = Bindings.bind_ty_param t.bindings elem param_bounds in
    { t with bindings }
  ;;

  let bind_ty_params t ty_params = List.fold_left ty_params ~init:t ~f:bind_ty_param
end

include Cont
