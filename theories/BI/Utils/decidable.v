(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Arith List Relations Utf8.
From Undecidability.Shared Require Import fin_base utils_decidable fin_dec measure_ind.
From Undecidability.BI Require Import fin_extra.

Import ListNotations.

Set Implicit Arguments.

Fact decidable_equiv X (P Q : X → Prop) :
    (∀x, P x ↔ Q x)
  → (∀x, { P x } + { ~ P x })
  → (∀x, { Q x } + { ~ Q x }).
Proof.
  intros H1 H2 x.
  generalize (H2 x); firstorder.
Qed.

Fact equivalence_product X Y E₁ E₂ :
    equivalence X E₁
  → equivalence Y E₂
  → equivalence _ (λ p q, E₁ (fst p) (fst q) ∧ E₂ (snd p) (snd q)).
Proof.
  intros [] []; split.
  + intros []; simpl; auto.
  + intros [] [] [] [] []; simpl; eauto.
  + intros [] [] []; simpl; auto.
Qed.  

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
        with (P := Forall provable)
             (Q := λ h, ¬ Forall provable h)
             (l := hh)
        as [ (? & ?%Hhh & ?) | C ]; eauto.
      + intros h H%Hhh.
        destruct list_choose_dep 
          with (P := λ x, ¬ provable x)
               (Q := provable)
               (l := h)
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

  Hypotheses (E_equiv : equivalence _ E).

  (** Merging the equivalence rule with each instance, at the conclusion *)
  Let instances_1 l c := ∃c', instances l c' ∧ c' ≡ c.

  (** Adding a separate equivalence rule to instances *)
  Let instances_2 l c := instances l c ∨ ∃c', l = [c'] ∧ c' ≡ c.

  (** Merging equivalence with each rule creates a provability predicate closed
      under the equivalence rule *)
  Local Lemma provable_1_equiv c c' : provable instances_1 c → c ≡ c' → provable instances_1 c'.
  Proof using E_equiv.
    destruct E_equiv.
    induction 1 as [ h c (d & H1 & H2) H IH ] in c' |- *; intros Hc.
    constructor 1 with h.
    + exists d; split; eauto.
    + revert IH; apply Forall_impl; eauto.
  Qed.

  (** Hence provable_2 is stronger than provable_1 *)
  Local Fact provable_2_1 c : provable instances_2 c → provable instances_1 c.
  Proof using E_equiv.
    destruct E_equiv.
    induction 1 as [ h c [ | (? & -> & ?) ] _ IH ].
    + constructor 1 with h; [ eexists | ]; eauto.
    + apply Forall_cons_iff in IH as [].
      eauto using provable_1_equiv.
  Qed.

  (** The converse is trivial of course *)
  Local Fact provable_1_2 c : provable instances_1 c → provable instances_2 c.
  Proof.
    induction 1 as [ ? ? (? & []) ].
    econstructor.
    + right; eauto.
    + constructor; auto.
      econstructor; eauto.
      left; auto.
  Qed.

  (** Hence the two provability predicates are equivalent *)
  Local Lemma provable_equiv_iff c : provable instances_1 c ↔ provable instances_2 c.
  Proof using E_equiv.
    split; auto using provable_2_1, provable_1_2.
  Qed.

  Variables (m : stm → nat)
            (E_m : ∀ s t, s ≡ t → m s = m t)
            (instances_m : ∀ h c, instances h c → Forall (λ x, m x < m c) h).

  Local Lemma instances_1_wf : well_founded (λ r s, ∃h, instances_1 h s ∧ In r h).
  Proof using E_m instances_m.
    intro c; induction on c as IH with measure (m c).
    constructor.
    intros d (h & (c' & H1%instances_m & H2%E_m) & H3).
    apply IH.
    rewrite <- H2.
    rewrite Forall_forall in H1; auto.
  Qed.

  Hypotheses (fin_t_instances : ∀c, fin_t (λ h, instances h c))
             (fin_t_E : ∀s, fin_t (λ t, t ≡ s)).

  Local Lemma instances_1_fin c : fin_t (λ h, instances_1 h c).
  Proof using fin_t_E fin_t_instances.
    apply fin_t_compose; auto.
  Qed.

  (** Under the assumptions that:
      1/ instances are decreasing according to measure m,
      2/ instances are finitely branching 
      3/ the equivalence relation ≡ is finitary
      4/ and preserves the measure m 
      then the provability predicate for instances augmented with
      an equivalence rule is decdidable *)

  Theorem provable_decr_fin_equiv_dec : ∀c, { provable instances_2 c } + { ¬ provable instances_2 c }.
  Proof using E_equiv E_m instances_m fin_t_E fin_t_instances.
    apply decidable_equiv with (1 := provable_equiv_iff), provable_wf_fin_dec;
      auto using instances_1_wf, instances_1_fin.
  Qed.

End with_equivalence.

Print provable.

Check provable_wf_fin_dec.
Check provable_decr_fin_equiv_dec.
