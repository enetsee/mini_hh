open Core

let synth local ~ctxt =
  (* Find the type of the term variable and any refinements *)
  match Ctxt.(find_local ctxt local) with
  | None -> Error (Err.unbound_local local)
  | Some ty -> Ok ty
;;
(* Ok (Option.value_map ~default:ty ~f:(fun refinement -> Ty.refine ty refinement) refinement_opt) *)
