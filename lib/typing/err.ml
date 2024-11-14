open Core
open Reporting

module Minimal = struct
  type t =
    | Subtyping of Subtyping.Err.t
    | Alread_bound of Name.Tm_var.t
    | Unbound_local of Name.Tm_var.t Located.t
    | Unbound_at_join of
        { name : Name.Tm_var.t
        ; span_bound : Span.t
        ; span_unbound : Span.t
        }
    | Unpack_arity of
        { span : Span.t
        ; n_quants : int
        ; n_names : int
        }
  [@@deriving compare, eq, sexp, variants]

  let pp ppf t =
    match t with
    | Subtyping err ->
      Fmt.(hovbox @@ (any "subtyping: " ++ Subtyping.Err.pp)) ppf err
    | Alread_bound nm ->
      Fmt.(hovbox @@ (any "already bound: " ++ Name.Tm_var.pp)) ppf nm
    | Unbound_local nm ->
      Fmt.(hovbox @@ (any "unbound local: " ++ Located.pp Name.Tm_var.pp))
        ppf
        nm
    | Unbound_at_join { name; span_bound; span_unbound } ->
      Fmt.(
        hovbox
        @@ pair ~sep:sp (any "unbound at join: " ++ Name.Tm_var.pp)
        @@ pair
             ~sep:sp
             (any " was bound here " ++ Span.pp)
             (any " but wasn't bound in this continuation " ++ Span.pp))
        ppf
        (name, (span_bound, span_unbound))
    | Unpack_arity { n_quants; n_names; _ } ->
      Fmt.(
        hovbox
        @@ (any "unpack arity: "
            ++ pair
                 ~sep:sp
                 (int
                  ++ (any
                      @@ if n_quants = 1 then " quantifier" else " quantifiers"
                     ))
                 (int ++ (any @@ if n_names = 1 then " name" else " names"))))
        ppf
        (n_quants, n_names)
  ;;
end

include Minimal
include Pretty.Make (Minimal)
