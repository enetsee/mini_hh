open Core

let synth local =
  (* Find the type of the term variable and any refinements *)
  match Eff.find_local local with
  | None -> Error (Err.unbound_local local)
  | Some ty -> Ok ty
;;
(* Ok (Option.value_map ~default:ty ~f:(fun refinement -> Ty.refine ty refinement) refinement_opt) *)
