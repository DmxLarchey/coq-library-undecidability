(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation Utf8.

Set Implicit Arguments.

Import ListNotations.

(** Intuionistic Linear Logic, the ⊗, ⊸ and & fragment with constants *)

Local Infix "~ₚ" := (@Permutation _) (at level 70).

Section syntax.

  Variables (prop : Set).

  Inductive ill_connective := ill_with | ill_limp | ill_times.
  Inductive ill_constant := ill_unit | ill_bot | ill_top.

  Inductive ill_form : Set :=
    | ill_var  : prop → ill_form
    | ill_cst  : ill_constant → ill_form
    | ill_bin  : ill_connective → ill_form → ill_form → ill_form.

End syntax.

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  !   ‼  ∅  ⊢ *)

Module ILL_notations.

  Notation "⟙" := (ill_cst ill_top).
  Notation "⟘" := (ill_cst ill_bot).
  Notation "𝟙" := (ill_cst ill_unit).

  Infix "&" := (ill_bin ill_with) (at level 50).
  Infix "⊗" := (ill_bin ill_times) (at level 50).
  Infix "⊸" := (ill_bin ill_limp) (at level 51, right associativity).

  Notation "£" := ill_var.

  Notation "∅" := nil (only parsing).

End ILL_notations.

Import ILL_notations.

#[local] Reserved Notation "l '⊢' x" (at level 70, no associativity).
#[local] Reserved Notation "l '⊢ₚ' x" (at level 70, no associativity).

Section ill_cut_free.

  Variables (prop : Set).

  (** ILL sequent calculus with an explicit permutation rule *)

  Inductive ill_cut_free : list (ill_form prop) → ill_form prop → Prop :=

    | ill_cf_ax A :

              (*--------------*)
                   [A] ⊢ A

    | ill_cf_perm Γ Δ A :

            Γ ~ₚ Δ     →   Γ ⊢ A 
    →  (*-----------------------------*)
                   Δ ⊢ A

    | ill_cf_times_l Γ A B C :

               A::B::Γ ⊢ C 
    →  (*-----------------------------*)
                A⊗B::Γ ⊢ C
 
    | ill_cf_times_r Γ Δ A B :

            Γ ⊢ A    →   Δ ⊢ B
    → (*-----------------------------*)
               Γ++Δ ⊢ A⊗B

    | ill_cf_limp_l Γ Δ A B C : 

           Γ ⊢ A     →   B::Δ ⊢ C
    → (*-----------------------------*)
             A⊸B::Γ++Δ ⊢ C

    | ill_cf_limp_r Γ A B :

               A::Γ ⊢ B
    → (*-----------------------------*)
               Γ ⊢ A⊸B

    | ill_cf_with_l1 Γ A B C :

                 A::Γ ⊢ C 
    → (*-----------------------------*)
                A&B::Γ ⊢ C

    | ill_cf_with_l2 Γ A B C :

                B::Γ ⊢ C 
    → (*-----------------------------*)
               A&B::Γ ⊢ C
 
    | ill_cf_with_r Γ A B :

           Γ ⊢ A     →   Γ ⊢ B
    → (*-----------------------------*)
                Γ ⊢ A&B

  where "l ⊢ x" := (ill_cut_free l x).

  (** The permutation rule is now merged in each rule to
      and removed as an independent rule to remove that
      non decreasing rule *)

  Inductive ill_cut_free_perm : list (ill_form prop) → ill_form prop → Prop :=

    | ill_cfp_ax A :

              (*--------------*)
                   [A] ⊢ₚ A

    | ill_cfp_times_l Γ Σ A B C :

          Σ ~ₚ A⊗B::Γ  →  A::B::Γ ⊢ₚ C 
    →  (*-----------------------------*)
                   Σ ⊢ₚ C
 
    | ill_cfp_times_r Γ Δ Σ A B :

         Σ ~ₚ Γ++Δ → Γ ⊢ₚ A → Δ ⊢ₚ B
    → (*-----------------------------*)
                 Σ ⊢ₚ A⊗B

    | ill_cfp_limp_l Γ Δ Σ A B C : 

         Σ ~ₚ A⊸B::Γ++Δ → Γ ⊢ₚ A → B::Δ ⊢ₚ C
    → (*-----------------------------*)
             Σ ⊢ₚ C

    | ill_cfp_limp_r Γ A B :
 
               A::Γ ⊢ₚ B
    → (*-----------------------------*)
               Γ ⊢ₚ A⊸B

    | ill_cfp_with_l1 Γ Σ A B C :

         Σ ~ₚ A&B::Γ  →  A::Γ ⊢ₚ C 
    → (*-----------------------------*)
                Σ ⊢ₚ C

    | ill_cfp_with_l2 Γ Σ A B C :

         Σ ~ₚ A&B::Γ  →  B::Γ ⊢ₚ C 
    → (*-----------------------------*)
               Σ ⊢ₚ C
 
    | ill_cfp_with_r Γ A B :

           Γ ⊢ₚ A     →   Γ ⊢ₚ B
    → (*-----------------------------*)
                Γ ⊢ₚ A&B

  where "l ⊢ₚ x" := (ill_cut_free_perm l x).

  Hint Constructors ill_cut_free_perm Permutation : core.
  Hint Resolve Permutation_sym : core.

  Local Lemma ill_cfp_perm Γ A Σ : Γ ⊢ₚ A → Γ ~ₚ Σ → Σ ⊢ₚ A.
  Proof.
    induction 1 as
      [ 
      | Γ Σ' A B C H1 H2 IH2
      | Γ Δ Σ' A B
      | Γ Δ Σ' A B C
      | 
      | Γ Σ' A B C
      | Γ Σ' A B C
      | 
      ] in Σ |- *.
    + intros ->%Permutation_length_1_inv; auto.
    + intro; apply ill_cfp_times_l with Γ A B; eauto.
    + intro; apply ill_cfp_times_r with Γ Δ; eauto.
    + intro; apply ill_cfp_limp_l with Γ Δ A B; eauto.
    + intro; apply ill_cfp_limp_r; eauto.
    + intro; apply ill_cfp_with_l1 with Γ A B; eauto.
    + intro; apply ill_cfp_with_l2 with Γ A B; eauto.
    + intro; apply ill_cfp_with_r; eauto.
  Qed.

  Local Lemma ill_cf_inc_cfp Γ A : Γ ⊢ A → Γ ⊢ₚ A.
  Proof.
    induction 1; eauto.
    eapply ill_cfp_perm; eauto.
  Qed.

  Hint Constructors ill_cut_free : core.

  Local Lemma ill_cfp_inc_cf Γ A : Γ ⊢ₚ A → Γ ⊢ A.
  Proof. induction 1; eauto. Qed.

  Hint Resolve ill_cf_inc_cfp ill_cfp_inc_cf : core.

  (** We show the equivalence between the two systems *)

  Theorem ill_cf_iff_cfp Γ A : Γ ⊢ₚ A ↔ Γ ⊢ A.
  Proof. split; auto. Qed.

End ill_cut_free.

Check ill_cf_iff_cfp.

(** Now we should show that ill_cut_free_perm is both 
     - terminating
     - finitary
    hence decidable !! *)
