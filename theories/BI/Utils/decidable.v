(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.
From Undecidability.Shared Require Import fin_base utils_decidable fin_dec.

Import ListNotations.

Set Implicit Arguments.

Section decidable.

  Variables (stm : Type) (instances : list stm → stm → Prop).

  Unset Elimination Schemes.

  Inductive provable : stm → Prop :=
    | provable_intro h c : instances h c → Forall provable h → provable c.

  Set Elimination Schemes.

  Section provable_ind.

    Variables (P : stm → Prop)
              (HP : ∀ h c, instances h c → Forall provable h → Forall P h → P c).

    Fixpoint provable_ind c (p : provable c) : P c.
    Proof using HP.
      destruct p as [ h c H1 H2 ].
      apply HP with (1 := H1); auto.
      clear H1 c.
      induction H2; eauto.
    Qed.

  End provable_ind.

  #[global] Register Scheme provable_ind as ind_dep for provable.

  Hypothesis (wf : well_founded (λ r s, ∃h, instances h s ∧ In r h))
             (finitary : ∀c, fin_t (λ h, instances h c)).

  Hint Constructors provable : core.

  Theorem provable_wf_fin_dec c : { provable c } + { ¬ provable c }.
  Proof using wf finitary.
    induction c as [ c IH ] using (well_founded_induction_type wf).
    destruct (finitary c) as [ hh Hhh ].
    destruct list_choose_dep
      with (P := Forall provable) (Q := λ h, ¬ Forall provable h) (l := hh)
      as [ (? & ?%Hhh & ?) | C ]; eauto.
    + intros h H%Hhh.
      destruct list_choose_dep 
        with (P := λ x, ¬ provable x) (Q := provable) (l := h)
        as [ (? & H1 & ?) | ]; auto.
      * intros s Hs; destruct (IH s); eauto.
      * right; rewrite Forall_forall; contradict H1; auto.
      * left; apply Forall_forall; auto.
    + right.
      destruct 1 as [ ? ? ? D ].
      now revert D; apply C, Hhh.
  Qed.

End decidable.

Print provable.

Check provable_wf_fin_dec.
