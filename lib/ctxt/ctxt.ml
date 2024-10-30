open Core
module Local = Local
module Classish = Classish
module Fn = Fn
module Def = Def
module Cont = Cont
module Ty_param = Ty_param

module Ctxt = struct
  module Minimal = struct
    (** The context across all continuations *)
    type t =
      { next : Cont.t option
      ; exit : Cont.t option (** retained for try.. finally *)
      }
    [@@deriving create, fields]

    let pp ppf t =
      Fmt.(
        vbox
        @@ record
             ~sep:cut
             [ field "next" (fun { next; _ } -> next) @@ option ~none:(any "(none)") Cont.pp
             ; field "exit" (fun { exit; _ } -> exit) @@ option ~none:(any "(none)") Cont.pp
             ])
        ppf
        t
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let empty = { next = None; exit = None }
end

module Delta = struct
  module Minimal = struct
    type t =
      { next : Cont.Delta.t option
      ; exit : Cont.Delta.t option
      }
    [@@deriving create, show]

    let pp ppf t =
      Fmt.(
        vbox
        @@ record
             ~sep:cut
             [ field "Δ next" (fun { next; _ } -> next) @@ option ~none:(any "(none)") Cont.Delta.pp
             ; field "Δ exit" (fun { exit; _ } -> exit) @@ option ~none:(any "(none)") Cont.Delta.pp
             ])
        ppf
        t
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let empty = { next = None; exit = None }
  let lift { next; exit } ~f = { next = Option.map ~f next; exit = Option.map ~f exit }

  let lift2 { next = next1; exit = exit1 } { next = next2; exit = exit2 } ~f =
    let next = Option.merge ~f next1 next2
    and exit = Option.merge ~f exit1 exit2 in
    { next; exit }
  ;;

  let join t1 t2 ~prov = lift2 t1 t2 ~f:Cont.Delta.(join ~prov)
  let extend t ~with_ = lift2 t with_ ~f:(fun t with_ -> Cont.Delta.extend t ~with_)
end

let update t ~delta =
  match delta.Delta.exit, delta.next with
  (* ~~ if we exited, put the next continuation into the exit continuation *)
  | Some _, _ -> Ctxt.create ?exit:t.Ctxt.next ()
  | _, Some delta ->
    let next = Option.map t.next ~f:(fun t -> Cont.update t ~delta) in
    Ctxt.create ?next ()
  | _ -> t
;;

include Ctxt
