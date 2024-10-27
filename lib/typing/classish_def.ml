open Core
open Reporting

(** When we type a

    - Bounds on type parameters must respect the bounds on extends and implements
    - Bind type parameters ready to check elements
    - Gather bounds for [this]:

    + for a class: current class is the upper bound
    + for a trait: intersection of require extends and implements refine
    + for an interface: intersection of current interface  and require extends

    `uses` can introduce properties, methods and type constants but these are
    dealt with in the oracle

    - Properties: need to check any default values are subtypes of the declared
      type of the property
    - methods: need to *)

let ty_ctor_located Located.{ elem; span } =
  let node = Ty.Node.Ctor elem in
  let prov = Prov.witness span in
  Ty.create ~prov ~node ()
;;

(** For a class [this] is any subtype of the enclosing class unless the class
    is declared final in which case it is exactly the enclosing class *)
let this_bounds classish_def =
  let nom_upper = Lang.Classish_def.ty_of classish_def in
  let Lang.Classish_def.{ name; kind; require_extends; require_implements; require_class; _ } = classish_def in
  match kind.elem with
  | Lang.Classish_kind.Class { is_final; _ } ->
    (match is_final with
     | Some final_span ->
       let lower = Ty.with_prov nom_upper (Prov.witness final_span) in
       Ty.Param_bounds.create ~upper:nom_upper ~lower ()
     | _ ->
       let prov = Prov.witness @@ Located.span_of name in
       let lower = Ty.nothing prov in
       Ty.Param_bounds.create ~upper:nom_upper ~lower ())
  | Lang.Classish_kind.Intf ->
    let req_uppers = List.map require_extends ~f:ty_ctor_located in
    let prov =
      Prov.witnesses @@ (Located.span_of name :: List.map require_extends ~f:(fun Located.{ span; _ } -> span))
    in
    let upper = Ty.inter (nom_upper :: req_uppers) ~prov
    and lower = Ty.nothing (Prov.witness @@ Located.span_of name) in
    Ty.Param_bounds.create ~upper ~lower ()
  | Lang.Classish_kind.Trait ->
    let req_uppers = List.map (require_extends @ require_implements) ~f:ty_ctor_located in
    let exact_uppers = List.map require_class ~f:ty_ctor_located in
    let prov =
      Prov.witnesses @@ (Located.span_of name :: List.map require_extends ~f:(fun Located.{ span; _ } -> span))
    in
    let upper = Ty.inter ((nom_upper :: req_uppers) @ exact_uppers) ~prov
    and lower =
      match exact_uppers with
      | [] -> Ty.nothing (Prov.witness @@ Located.span_of name)
      | _ ->
        let spans = List.map require_class ~f:Located.span_of in
        let prov = Prov.witnesses spans in
        Ty.union exact_uppers ~prov
    in
    Ty.Param_bounds.create ~upper ~lower ()
;;

let synth Located.{ elem = classish_def; span = _ } ~def_ctxt ~cont_ctxt =
  (* TODO(mjt) Type parameter bounds checks, type const checks, method override checks property typing *)
  let Lang.Classish_def.{ name; ty_params; methods; _ } = classish_def in
  let def_ctxt = Ctxt.Def.enter_classish def_ctxt name in
  let cont_ctxt =
    let ty_param =
      let this_ty_param =
        let param_bounds = this_bounds classish_def in
        let name = Located.create ~elem:Name.Ty_param.this ~span:(Located.span_of name) () in
        Ty.Param.create ~name ~param_bounds ()
      in
      let ty_params = List.map ty_params ~f:Lang.Ty_param_def.to_ty_param in
      Ctxt.Ty_param.(bind_all empty @@ (this_ty_param :: ty_params))
    in
    let delta = Ctxt.Cont.Delta.create ~ty_param () in
    Ctxt.Cont.update cont_ctxt ~delta
  in
  List.iter methods ~f:(fun Located.{ elem; span } ->
    let Lang.Method_def.{ fn_def; _ } = elem in
    let fn_def = Located.create ~elem:fn_def ~span () in
    Fn_def.synth fn_def ~def_ctxt ~cont_ctxt)
;;
