include Pretty_intf

module Make1 (X : Minimal1) : S1 with type 'a t := 'a X.t = struct
  let pp pp_a ppf t = X.pp pp_a ppf t
  let pp_prec pp_a _ ppf t = X.pp (pp_a 0) ppf t
  let to_string t ~pp_a = Format.asprintf "%a" (pp pp_a) t
  let show pp_a t = to_string t ~pp_a
  let print t ~pp_a = pp pp_a Format.std_formatter t
  let print_err t ~pp_a = pp pp_a Format.err_formatter t
end

module Make1_prec (X : Minimal1_prec) : S1 with type 'a t := 'a X.t = struct
  let pp pp_a ppf t = X.pp_prec (fun _ -> pp_a) 0 ppf t
  let pp_prec pp_a prec ppf t = X.pp_prec pp_a prec ppf t
  let to_string t ~pp_a = Format.asprintf "%a" (pp pp_a) t
  let show pp_a t = to_string t ~pp_a
  let print t ~pp_a = pp pp_a Format.std_formatter t
  let print_err t ~pp_a = pp pp_a Format.err_formatter t
end

module Make (X : Minimal) : S with type t := X.t = struct
  let pp ppf t = X.pp ppf t
  let pp_prec _ ppf t = X.pp ppf t
  let to_string t = Format.asprintf "%a" pp t
  let show t = to_string t
  let print t = pp Format.std_formatter t
  let print_err t = pp Format.err_formatter t
end

module Make_prec (X : Minimal_prec) : S with type t := X.t = struct
  let pp ppf t = X.pp_prec 0 ppf t
  let pp_prec prec ppf t = X.pp_prec prec ppf t
  let to_string t = Format.asprintf "%a" pp t
  let show t = to_string t
  let print t = pp Format.std_formatter t
  let print_err t = pp Format.err_formatter t
end
