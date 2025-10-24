From Sulfur Require Import Prelude.

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
