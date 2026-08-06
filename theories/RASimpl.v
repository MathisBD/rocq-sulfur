From Sulfur Require Import Prelude Sig Constants Renamings.
From Sulfur Require ParamSyntax ExplicitSyntax Simplification Cleanup.
From Ltac2 Require Import RedFlags Printf Rewrite Std.
From Ltac2 Require Ltac2.

Module P := ParamSyntax.
Module E := ExplicitSyntax.
Module Simp := Simplification.
Module Clean := Cleanup.

(*********************************************************************************)
(** *** Simplifying level one terms/substitutions. *)
(*********************************************************************************)

(** Reduction flags to unfold all (level 2 -> level 1) evaluation
    functions (LevelTwo.v). *)
Ltac2 red_flags_eval () : RedFlags.t :=
  red_flags:(beta iota delta
    [E.eeval E.seval E.eeval_functional E.seval_functional
     E.reval E.qeval E.reval_functional E.qeval_functional
     E.assign_qnat E.assign_ren E.assign_term E.assign_subst
     E.list_nth
     ]).

(** Simplify a level one term. Returns [(t1', eq)] where [eq : t1 = t1'].  *)
Ltac2 simpl_term_one (sig : constr) (t1 : constr) : constr * constr :=
  (*printf "t1: %t" t1;*)
  (* Reify Level 1 -> Level 2. *)
  let env := E.empty_env () in
  let (env, t2) := E.reify_expr sig env t1 in
  let env := E.build_env sig env in
  (*printf "t2: %t" t2;*)
  (* Simplify on Level 2. *)
  let t2' := Std.eval_cbn RedFlags.all constr:(Simp.esimp $t2) in
  (*printf "t2': %t" t2';*)
  let t2'' := Std.eval_cbn RedFlags.all constr:(Clean.eclean $t2') in
  (*printf "t2'': %t" t2'';*)
  (* Eval Level 2 -> Level 1. *)
  let t1' := Std.eval_cbn (red_flags_eval ()) constr:(E.eeval $env $t2'') in
  (*printf "t1': %t" t1';*)
  (* [eq1 : t1 = t1']. *)
  let eq1 := constr:(eq_trans
    (Simp.ered_sound $env _ _ (Simp.esimp_red $t2))
    (Clean.ered_sound $env _ _ (Clean.eclean_red $t2')))
  in
  (t1', eq1).

(** Simplify a level one substitution. Returns [(s1', eq)] where [eq : s1 =₁ s1'].*)
Ltac2 simpl_subst_one (sig : constr) (s1 : constr) : constr * constr :=
  (*printf "s1: %t" s1;*)
  (* Reify Level 1 -> Level 2. *)
  let env := E.empty_env () in
  let (env, s2) := E.reify_subst sig env s1 in
  let env := E.build_env sig env in
  (*printf "s2: %t" s2;*)
  (* Simplify on Level 2. *)
  let s2' := Std.eval_cbn RedFlags.all constr:(Simp.ssimp $s2) in
  (*printf "s2': %t" s2';*)
  let s2'' := Std.eval_cbn RedFlags.all constr:(Clean.sclean $s2') in
  (*printf "s2'': %t" s2'';*)
  (* Eval Level 2 -> Level 1. *)
  let s1' := Std.eval_cbv (red_flags_eval ()) constr:(E.seval $env $s2'') in
  (*printf "s1': %t" s1';*)
  (* [eq1 : s1 =₁ s1']. *)
  let eq1 := constr:(eq1_trans
    (Simp.sred_sound $env _ _ (Simp.ssimp_red $s2))
    (Clean.sred_sound $env _ _ (Clean.sclean_red $s2')))
  in
  (s1', eq1).

(*********************************************************************************)
(** *** Load the plugin. *)
(*********************************************************************************)

Declare ML Module "rocq-sulfur.plugin".

Ltac2 @external simpl_term_zero : constr -> constr * constr := "rocq-sulfur.plugin" "simpl_term_zero".
Ltac2 @external simpl_subst_zero : constr -> constr * constr := "rocq-sulfur.plugin" "simpl_subst_zero".


Ltac2 mutable aunfold_list () : reference list := [].

Ltac2 Notation "constants" pl(list1(reference, ",")) := pl.
(* To be employed as
Ltac2 Set aunfold_list as old := fun () => List.append (constants foo, bla) (old ()).
*)

Import Strategy.

Ltac2 sulfur_simpl_term_rename carrier lhs _rel :=
  (* FIXME: No autounfold in Ltac2 ? should use the hints of asimpl_unfold or find an alternative extensible solution (reference to a list ?) *)
  let unfold_list := List.map (fun r => (r, AllOccurrences)) (aunfold_list ()) in
  let lhs := eval_unfold unfold_list lhs in
  let (rhs, prf) := simpl_term_zero lhs in
  if Constr.equal lhs rhs then Fail
  else Success { rel := '(@eq $carrier); rhs ; prf }.

Ltac2 mutable rasimpl_matches () : Strategy.t := Strategy.fail.

Ltac2 rasimpl0 idopt :=
  (* rewrite_strat should be focused but that's not documented *)
  Control.enter (fun () =>
  rewrite_strat (bottomup (seq (rasimpl_matches ()) (tactic sulfur_simpl_term_rename))) idopt).

Ltac2 Abbreviation rasimpl := rasimpl0 None.
Ltac2 Notation "rasimpl" "in" h(ident) := rasimpl0 (Some h).

(*********************************************************************************)
(** *** [rasimpl]. *)
(*********************************************************************************)

(** Simplify in the goal. *)
Ltac rasimpl := ltac2:(rasimpl).

(*********************************************************************************)
(** *** [rasimpl in H]. *)
(*********************************************************************************)

(** Simplify in a hypothesis [H]. *)
Tactic Notation "rasimpl" "in" hyp(H) :=
  let k := ltac2:(h |- rasimpl0 (Some (Option.get (Ltac1.to_ident h)))) in
  k H.

(** Tests... *)
