(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Arith List Utf8.
From Undecidability.Shared Require Import fin_base utils_decidable fin_dec measure_ind.
From Undecidability.BI Require Import fin_extra.

Import ListNotations.

Set Implicit Arguments.

Section provable.

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
  
  Section decidable.

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
        * intros s ?; destruct (IH s); eauto.
        * right; rewrite Forall_forall; contradict H1; auto.
        * left; apply Forall_forall; auto.
      + right.
        destruct 1 as [ ? ? ? D ].
        now revert D; apply C, Hhh.
    Qed.

  End decidable.
  
End provable.

#[local] Hint Constructors provable : core.

Fact provable_mono stm (i1 i2 : list stm → stm → Prop) :
    (∀ l c, i1 l c → i2 l c)
  → ∀c, provable i1 c → provable i2 c.
Proof. induction 2; eauto. Qed. 

Section with_equivalence.

  Variables (stm : Type) (instances : list stm → stm → Prop)
            (E : stm → stm → Prop).

  Infix "≡" := E (at level 70).

  Hypotheses (E_refl :  ∀ s, s ≡ s)
             (E_sym :   ∀ s t, s ≡ t → t ≡ s)
             (E_trans : ∀ r s t, r ≡ s → s ≡ t → r ≡ t).

  (** Merging the equivalence rule with each instance *)
  Let instances_1 l c := ∃c', instances l c' ∧ c' ≡ c.

  (** Adding an equivalence rule to instances *)
  Let instances_2 l c := instances l c ∨ ∃c', l = [c'] ∧ c' ≡ c.

  Local Fact provable_1_E c c' : provable instances_1 c → c ≡ c' → provable instances_1 c'.
  Proof using E_refl E_sym E_trans.
    induction 1 as [ h c (d & H1 & H2) H IH ] in c' |- *; intros Hc.
    constructor 1 with h.
    + exists d; split; eauto.
    + revert IH; apply Forall_impl; eauto.
  Qed.

  Local Fact provable_2_1 c : provable instances_2 c → provable instances_1 c.
  Proof using E_refl E_sym E_trans.
    induction 1 as [ h c [ H1 | (c' & -> & H1) ] H IH ].
    + constructor 1 with h; auto.
      exists c; auto.
    + apply Forall_cons_iff in IH as [].
      eauto using provable_1_E.
  Qed.

  Local Fact provable_1_2 c : provable instances_1 c → provable instances_2 c.
  Proof.
    induction 1 as [ h c (c' & H1 & H2) H IH ].
    constructor 1 with [c'].
    + right; eauto.
    + constructor; auto.
      constructor 1 with h; auto.
      left; auto.
  Qed.

  Theorem provable_equiv_iff c : provable instances_1 c ↔ provable instances_2 c.
  Proof using E_refl E_sym E_trans. split; auto using provable_2_1, provable_1_2. Qed.

  Variables (m : stm → nat)
            (E_m : ∀ s t, s ≡ t → m s = m t)
            (instances_m : ∀ h c, instances h c → Forall (λ x, m x < m c) h).

  Local Fact instances_1_wf : well_founded (λ r s, ∃h, instances_1 h s ∧ In r h).
  Proof using E_m instances_m.
    intro c; induction on c as IH with measure (m c).
    constructor.
    intros d (h & (c' & H1%instances_m & H2%E_m) & H3).
    apply IH.
    rewrite <- H2.
    rewrite Forall_forall in H1; auto.
  Qed.

  Variables (fin_instances : ∀c, fin_t (λ h, instances h c))
            (fin_E : ∀s, fin_t (λ t, t ≡ s)).

  Local Fact instances_1_fin c : fin_t (λ h, instances_1 h c).
  Proof using fin_E fin_instances.
    apply fin_t_compose; auto.
  Qed.
  
  Local Lemma provables_1_dec c : { provable instances_1 c } + { ¬ provable instances_1 c }.
  Proof using E_m fin_E fin_instances instances_m.
    apply provable_wf_fin_dec; auto using instances_1_wf, instances_1_fin.
  Qed.
  
  (** Under the assumptions that:
      1/ instances are decreasing according to measure m,
      2/ instances are finitely branching 
      3/ the equivalence relation ≡ is finitary
      4/ and preserves the measure m 
      then the provability predicate for instances augmented with
      an equivalence rule is decdidable *)

  Theorem provable_decr_fin_equiv_dec c : { provable instances_2 c } + { ¬ provable instances_2 c }.
  Proof using E_refl E_sym E_trans E_m fin_E fin_instances instances_m.
    generalize (provables_1_dec c).
    intros [ H | H ]; [ left | right; contradict H]; revert H; apply provable_equiv_iff.
  Qed.

End with_equivalence.

Print provable.

Check provable_wf_fin_dec.
Check provable_decr_fin_equiv_dec.
