From Coq Require Export Bool Nat List String Morphisms Relations Program.Equality Lia.
From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
From Utils Require Export Fin Vector.
Export ListNotations VectorNotations.

#[export] Set Equations Transparent.

(** Just to make sure. *)
#[export] Unset Equations With UIP.

(** Ltac2 is still missing many basic Ltac1 tactics,
    so we use Ltac1 for proofs. *)
#[export] Set Default Proof Mode "Classic".

(** Coercion to view booleans as propositions. *)
Coercion is_true : bool >-> Sortclass.

(*********************************************************************************)
(** *** Convenience tactics. *)
(*********************************************************************************)

(** Split n-ary conjunctions. *)
Ltac split3 := split ; [|split].
Ltac split4 := split ; [|split3].
Ltac split5 := split ; [|split4].
Ltac split6 := split ; [|split5].
Ltac split7 := split ; [|split6].
Ltac split8 := split ; [|split7].

(** On a hypothesis of the form [H : A -> B], this generates two goals:
    - the first asks to prove [A].
    - the second asks to prove the original goal in a context where [H : A]. *)
Ltac feed H :=
  match type of H with
  | ?A -> ?B =>
    let HA := fresh "H" in
    assert (HA : A) ; [| specialize (H HA)]
  end.

Ltac feed2 H := feed H ; [| feed H].
Ltac feed3 H := feed H ; [| feed2 H].
Ltac feed4 H := feed H ; [| feed3 H].

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

(** A renaming on terms is a function [nat -> nat] which is applied
    to all free variables. *)
Definition ren := nat -> nat.

(** The identity renaming. *)
Definition rid : ren := fun i => i.

(** [rshift] shifts indices by one. *)
Definition rshift : ren := fun i => S i.

(** Cons an index with a renaming. *)
Equations rcons (i0 : nat) (r : ren) : ren :=
rcons i0 _ 0 := i0 ;
rcons i0 r (S i) := r i.

(** Compose two renamings (left to right composition). *)
Equations rcomp (r1 r2 : ren) : ren :=
rcomp r1 r2 i := r2 (r1 i).

(** Lift a renaming through a binder. *)
Equations up_ren (r : ren) : ren :=
up_ren r := rcons 0 (rcomp r rshift).

(*********************************************************************************)
(** *** Trivial properties of renamings. *)
(*********************************************************************************)

(** Pointwise equality for functions. *)
Definition eq1 {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (eq1 f g) (at level 75).

Lemma eq1_refl {A B} {x : A -> B} : x =₁ x.
Proof. reflexivity. Qed.

Lemma eq1_sym {A B} {x y : A -> B} : x =₁ y -> y =₁ x.
Proof. now intros ->. Qed.

Lemma eq1_trans {A B} {x y z : A -> B} : x =₁ y -> y =₁ z -> x =₁ z.
Proof. now intros -> ->. Qed.

Lemma congr_rcons i {r r'} :
  r =₁ r' -> rcons i r =₁ rcons i r'.
Proof. intros H [|i'] ; [reflexivity|]. now simp rcons. Qed.

Lemma congr_rcomp {r1 r1' r2 r2'} :
  r1 =₁ r1' -> r2 =₁ r2' -> rcomp r1 r2 =₁ rcomp r1' r2'.
Proof. intros H1 H2 i. simp rcomp. now rewrite H1, H2. Qed.

Lemma congr_up_ren {r r'} :
  r =₁ r' -> up_ren r =₁ up_ren r'.
Proof. intros H. simp up_ren. apply congr_rcons. now apply congr_rcomp. Qed.