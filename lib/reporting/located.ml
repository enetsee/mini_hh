type 'a t =
  { elem : 'a
  ; span : Span.t
  }
[@@deriving compare, create, eq, sexp, show, map]

let create_empty elem = { elem; span = Span.empty }
let span_of { span; _ } = span
let elem { elem; _ } = elem
let update_span { span; elem } ~f = { span = f span; elem }
let with_span { elem; _ } ~span = { elem; span }
