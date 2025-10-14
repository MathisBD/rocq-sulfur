(** This file defines the OCaml representation of signatures, as well utilities for
    parsing and validating signatures written by the user. *)

open Prelude
module C = Constants

(**************************************************************************************)
(** *** Pre-signature. *)
(**************************************************************************************)

(** A pre-signature is a parse tree of a user-written signature. It still contains
    location information, and can contain mistakes (for instance declaring the same
    constructor twice). A pre-signature can be checked and turned into a real signature
    using [check_psignature]. *)

(** Argument type. *)
type parg_ty_r =
  | PAT_base of Constrexpr.constr_expr
  | PAT_sort of Names.lident
  | PAT_bind of Names.lident list * parg_ty

and parg_ty = parg_ty_r CAst.t

(** Declaration. *)
type decl_r =
  | SortDecl of { name : Names.lident; var_ctor : Names.lident option }
      (** Sort declaration, e.g. [term : Type]. *)
  | CtorDecl of { name : Names.lident; arg_tys : parg_ty list; ret_ty : Names.lident }
      (** Constructor declaration, e.g. [app : term -> option term -> term]. *)

and decl = decl_r CAst.t

(** Pre-signature. *)
type psignature_r = { decls : decl list }

and psignature = psignature_r CAst.t

(**************************************************************************************)
(** *** Signature. *)
(**************************************************************************************)

(** Argument type.
    - [AT_base] contains the index of the base type in the [base_types] array. *)
type arg_ty = AT_base of int | AT_term | AT_bind of arg_ty

(** An abstract signature:
    - [sort] is the name of the (unique) sort of terms.
    - [var_ctor] is the name of the variable constructor.
    - [base_types] contains the list of base types.
    - [n_ctors] is the number of _non-variable_ constructors.
    - [ctor_names] (of length [n_ctors]) contains the name of each constructor.
    - [ctor_sig] (of length [n_ctors]) contains the argument types of each constructor. *)
type signature =
  { sort_name : Names.Id.t
  ; var_ctor_name : Names.Id.t
  ; base_types : EConstr.t array
  ; n_ctors : int
  ; ctor_names : Names.Id.t array
  ; ctor_types : arg_ty list array
  }

(** [arg_ty_constr sign ty ind] builds the [EConstr.t] corresponding to [ty]. We use [ind]
    as a placeholder for the inductive type of terms. *)
let rec arg_ty_constr (sign : signature) (ty : arg_ty) (ind : EConstr.t) : EConstr.t =
  match ty with
  | AT_base i -> sign.base_types.(i)
  | AT_term -> ind
  | AT_bind ty -> arg_ty_constr sign ty ind

(** [ctor_ty_constr sign tys ind] builds the type of a constructor as a [EConstr.t]. We
    use [ind] as a placeholder for the inductive type of terms. *)
let ctor_ty_constr (sign : signature) (tys : arg_ty list) (ind : EConstr.t) : EConstr.t =
  arrows (List.map (fun ty -> arg_ty_constr sign ty ind) tys) ind

(**************************************************************************************)
(** *** Checking a pre-signature. *)
(**************************************************************************************)

(** Check a pre-signature is well formed. Checking a pre-signature is done when evaluating
    the command [Sulfur Generate ...]. We can't check a signature during parsing because
    we need access to the global environment. *)

type checked_sort = { sname : Names.Id.t; var_ctor : Names.Id.t }
type checked_ctor = { cname : Names.Id.t; arg_tys : arg_ty list }

(** State we maintain while validating a pre-signature. *)
type state =
  { (* The global environment. *)
    env : Environ.env
  ; (* The evar map, which contains the universe constraints
    generated while internalizing the base types. *)
    sigma : Evd.evar_map
  ; (* The (unique) sort, or [None] if we haven't encountered it yet. *)
    sort : checked_sort option
  ; (* The list of declared constructors, most recent last. *)
    ctors : checked_ctor list
  ; (* The list of base types, most recent last. *)
    base_types : EConstr.t list
  }

(** Check a name is fresh, i.e. it is not already present in the state. *)
let check_fresh (st : state) (name : Names.lident) : unit =
  let b1 = List.exists (fun c -> Names.Id.equal name.v c.cname) st.ctors in
  let b2 =
    match st.sort with
    | None -> false
    | Some s -> Names.Id.equal name.v s.sname || Names.Id.equal name.v s.var_ctor
  in
  (* TODO: check in the global env as well. *)
  if b1 || b2
  then Log.error ?loc:name.loc "%s is already declared." (Names.Id.to_string name.v)

(** Check a sort is declared. *)
let check_sort (st : state) (sort : Names.lident) : unit =
  match st.sort with
  | Some s when Names.Id.equal sort.v s.sname -> ()
  | _ -> Log.error ?loc:sort.loc "Undeclared sort %s." (Names.Id.to_string sort.v)

(** Internalize a base type and add it to the list of base types. *)
let check_base (st : state) (c : Constrexpr.constr_expr) : state * int =
  (* Internalize the base type, updating the evar context along the way. *)
  let c, ustate = Constrintern.interp_type st.env st.sigma c in
  let sigma = Evd.merge_universe_context st.sigma ustate in
  let c = Evarutil.nf_evar sigma c in
  (* Add it to the list. *)
  let idx = List.length st.base_types in
  let st = { st with sigma; base_types = st.base_types @ [ c ] } in
  (st, idx)

(** Check an argument type. *)
let rec check_arg_ty (st : state) (ty : parg_ty) : state * arg_ty =
  match ty.v with
  | PAT_base c ->
      let st, idx = check_base st c in
      (st, AT_base idx)
  | PAT_sort sort ->
      check_sort st sort;
      (st, AT_term)
  | PAT_bind (ids, ty) ->
      List.iter (check_sort st) ids;
      let st, ty = check_arg_ty st ty in
      (st, List.fold_right (fun _ ty -> AT_bind ty) ids ty)

(** Check a list of argument types. *)
let rec check_arg_tys (st : state) (ptys : parg_ty list) : state * arg_ty list =
  match ptys with
  | [] -> (st, [])
  | pty :: ptys ->
      let st, ty = check_arg_ty st pty in
      let st, tys = check_arg_tys st ptys in
      (st, ty :: tys)

let typecheck_fctor (f : Names.GlobRef.t) : unit m =
  let* t1 = fresh_type in
  let* t2 = fresh_type in
  let* _ = typecheck (mkglob f) (Some (arrow t1 t2)) in
  ret ()

(** Check a declaration. *)
let check_decl (st : state) (d : decl) : state =
  match d.v with
  (* Constructor declaration. *)
  | CtorDecl d' ->
      check_fresh st d'.name;
      let st, tys = check_arg_tys st d'.arg_tys in
      check_sort st d'.ret_ty;
      { st with ctors = st.ctors @ [ { cname = d'.name.v; arg_tys = tys } ] }
  (* Sort declaration. *)
  | SortDecl d' ->
      (* Check we haven't declared a sort yet. *)
      begin
        match st.sort with
        | Some _ -> Log.error ?loc:d.loc "Only one sort can be declared."
        | None -> ()
      end;
      check_fresh st d'.name;
      (* Choose a variable constructor. *)
      let var_ctor =
        match d'.var_ctor with None -> Names.Id.of_string_soft "Var" | Some var -> var.v
      in
      { st with sort = Some { sname = d'.name.v; var_ctor } }

(** Check a pre-signature. Raises an error (using Rocq's error reporting mechanism) if the
    pre-signature is not valid. *)
let check_psignature (s : psignature) : signature m =
 fun env sigma ->
  (* Build the initial state. *)
  let st = { env; sigma; sort = None; ctors = []; base_types = [] } in
  (* Check each constructor declaration. *)
  let st = List.fold_left check_decl st s.v.decls in
  (* Check we declared a sort. *)
  let sort =
    match st.sort with
    | Some s -> s
    | None -> Log.error ?loc:s.loc "At least one sort must be declared."
  in
  (* Build the signature. *)
  let sign =
    { sort_name = sort.sname
    ; var_ctor_name = sort.var_ctor
    ; n_ctors = List.length st.ctors
    ; base_types = st.base_types |> Array.of_list
    ; ctor_names = st.ctors |> List.map (fun c -> c.cname) |> Array.of_list
    ; ctor_types = st.ctors |> List.map (fun c -> c.arg_tys) |> Array.of_list
    }
  in
  (sigma, sign)
