(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

From Undecidability.BI
  Require Import BI utils lbi.

Import BI_notations ListNotations LBI_tactics.

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70, format "X  ⊆  Y", no associativity).
#[local] Notation "X ≃ Y" := (X ⊆ Y ∧ Y ⊆ X) (at level 70, format "X  ≃  Y", no associativity).
#[local] Infix "∊" := In (at level 70).

Fact inc1_refl X (A : X → Prop) : A ⊆ A.
Proof. auto. Qed.

Fact inc1_trans X (A B C : X → Prop) : A ⊆ B → B ⊆ C → A ⊆ C.
Proof. intros; auto. Qed.

Fact eq1_refl X (A : X → Prop) : A ≃ A.
Proof. tauto. Qed.

Fact eq1_sym X (A B : X → Prop) : A ≃ B → B ≃ A.
Proof. tauto. Qed.

Fact eq1_trans X (A B C : X → Prop) : A ≃ B → B ≃ C → A ≃ C.
Proof. intros [] [];  split; intros; auto. Qed.

Fact equal_eq1 X (A B : X -> Prop) : A = B → A ≃ B.
Proof. intros []; auto. Qed.

#[local] Notation "A '∩' B" := (λ z, A z ∧ B z) (at level 50, format "A  ∩  B", left associativity).
#[local] Notation "A '∪' B" := (λ z, A z ∨ B z) (at level 50, format "A  ∪  B", left associativity).

(** λ ∧ ∨ ⊆ ≃ ∩ ∪ *)

#[local] Abbreviation sg := (@eq _).

Fact sg_inc1 X (A : X → Prop) x : A x ↔ sg x ⊆ A.
Proof.
  split.
  + intros ? ? []; trivial.
  + intros H; apply H; auto. 
Qed.

Ltac spec_all_rec H U :=
  try match goal with [ G : ?h -> _ |- _ ] => 
    match G with H => assert h as U; [ idtac | specialize (H U); clear U; spec_all_rec H U ] end end.

Tactic Notation "spec" "all" "in" hyp(H) := let U := fresh in spec_all_rec H U.

Section Relational_phase_semantics.

  (** We define a sound relational phase sematics for BI 
      based on stable closures 

      The algebraic developments below follow the sketch
      in the book "Lectures on Linear Logic"

      http://phil.gu.se/logic/books/Troelstra:Lectures_on_Linear_Logic.pdf

    *)

  Variable M : Type.

  Implicit Types A B C : M → Prop.

  Variable cl : (M → Prop) → (M → Prop).

  Hypothesis cl_increase   : ∀A, A ⊆ cl A.
  Hypothesis cl_monotone   : ∀ A B, A ⊆ B → cl A ⊆ cl B.
  Hypothesis cl_idempotent : ∀ A, cl (cl A) ⊆ cl A.
  
  Proposition cl_prop A B : A ⊆ cl B ↔ cl A ⊆ cl B.
  Proof using cl_increase cl_monotone cl_idempotent.
    split; intros H x Hx.
    apply cl_idempotent; revert Hx; apply cl_monotone; auto.
    apply H, cl_increase; auto.
  Qed.

  Definition cl_inc A B := proj1 (cl_prop A B).
  Definition inc_cl A B := proj2 (cl_prop A B). 

  Fact cl_eq1 A B : A ≃ B → cl A ≃ cl B.
  Proof using cl_monotone. intros []; split; apply cl_monotone; auto. Qed.

  Hint Resolve cl_inc cl_eq1 : core.

  Abbreviation closed := (λ x, cl x ⊆ x).

  Fact cl_closed A B : closed B → A ⊆ B → cl A ⊆ B.
  Proof using cl_idempotent cl_increase cl_monotone.
    intros H1 H2.
    apply inc1_trans with (2 := H1), cl_inc, 
          inc1_trans with (1 := H2), cl_increase.
  Qed.
  
  Fact closed_eq1 A : closed A → cl A ≃ A.
  Proof using cl_increase. split; auto. Qed.

  Fact cap_closed A B : closed A → closed B → closed (A ∩ B).
  Proof using cl_monotone.
    intros HA HB x Hx; split; [ apply HA | apply HB ]; revert Hx; apply cl_monotone; tauto.
  Qed.

  Hint Resolve cap_closed closed_eq1 : core.

  (* this is a relational/non-deterministic monoid *)

  Variable Compose : M → M → M → Prop.

  (* Composition lifted to predicates *)

  Inductive Composes (A B : M → Prop) : M → Prop :=
    | In_composes a b c : A a → B b → Compose a b c → Composes A B c.

  (* ⊆ ≃ ∩ ∪ ∘ *)

  Infix "∘" := Composes (at level 50, no associativity).

  Proposition composes_monotone A A' B B' : A ⊆ A' → B ⊆ B' → A ∘ B ⊆ A' ∘ B'.
  Proof. intros ? ? _ [ ? ? ? ? ? H ]; apply In_composes with (3 := H); auto. Qed.

  Hint Resolve composes_monotone : core.

  Variable e : M.

  (* Stability is the important axiom in phase semantics *)

  Definition cl_stability     :=  ∀ A B, cl A ∘ cl B ⊆ cl (A ∘ B).

  Abbreviation cl_stability_l := (∀ A B, cl A ∘    B ⊆ cl (A ∘ B)).

  Definition cl_stability_r   :=  ∀ A B,    A ∘ cl B ⊆ cl (A ∘ B).

  Proposition cl_stable_imp_stable_l : cl_stability → cl_stability_l.
  Proof using cl_increase. 
    intros H ? ? x Hx.
    apply H; revert x Hx. 
    apply composes_monotone; auto.
  Qed.

  Proposition cl_stable_imp_stable_r : cl_stability → cl_stability_r.
  Proof using cl_increase. 
    intros H ? ? x Hx.
    apply H; revert x Hx. 
    apply composes_monotone; auto.
  Qed.

  Proposition cl_stable_lr_imp_stable : cl_stability_l → cl_stability_r → cl_stability.
  Proof using cl_idempotent cl_increase cl_monotone. 
    intros H1 H2 A B x Hx.
    apply cl_idempotent.
    generalize (H1 _ _ _ Hx).
    apply cl_monotone, H2.
  Qed.

  Hint Resolve cl_stable_imp_stable_l cl_stable_imp_stable_r cl_stable_lr_imp_stable : core.

  Abbreviation cl_neutrality_1  := (∀a, cl (sg e ∘ sg a) a).
  Abbreviation cl_neutrality_2  := (∀a, sg e ∘ sg a ⊆ cl (sg a)).
  Abbreviation cl_commutativity := (∀ a b, sg a ∘ sg b ⊆ cl (sg b ∘ sg a)).
  Abbreviation cl_associativity := (∀ a b c, sg a ∘ (sg b ∘ sg c) ⊆ cl ((sg a ∘ sg b) ∘ sg c)).

  Hypothesis cl_commute : cl_commutativity.

  Proposition composes_commute_1 A B : A ∘ B ⊆ cl (B ∘ A).
  Proof using cl_commute cl_monotone.
    intros _ [ a b c Ha Hb Hc ].
    apply cl_monotone with (sg b ∘ sg a).
    apply composes_monotone; apply sg_inc1; auto.
    apply cl_commute.
    constructor 1 with (3 := Hc); auto.
  Qed.

  Hint Resolve composes_commute_1 : core.

  (* ⊆ ≃ ∩ ∪ ∘ *)

  Proposition composes_commute A B : cl (A∘B) ≃ cl (B∘A).
  Proof using cl_commute cl_idempotent cl_increase cl_monotone. 
    split; intros x Hx; apply cl_idempotent; revert Hx; apply cl_monotone; auto. 
  Qed. 

  Proposition cl_stable_l_imp_r : cl_stability_l → cl_stability_r.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    intros Hl A B x Hx.
    apply cl_idempotent.
    apply cl_monotone with (cl B ∘ A).
    apply inc1_trans with (cl ((cl B) ∘ A)); auto.
    rewrite <- cl_prop; auto.
    generalize (@composes_commute_1 B A); intros H.
    rewrite cl_prop in H; auto.
    apply composes_commute_1; auto.
  Qed.
  
  Proposition cl_stable_r_imp_l : cl_stability_r → cl_stability_l.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    intros Hl A B.
    generalize (@composes_commute_1 B A); intros H.
    rewrite cl_prop in H; auto.
    apply inc1_trans with (B := cl (B ∘ cl A)),
          inc1_trans with (2 := H); auto.
    rewrite <- cl_prop; apply Hl.
  Qed.

  Hint Resolve cl_stable_l_imp_r cl_stable_r_imp_l : core.

  Proposition cl_stable_l_imp_stable : cl_stability_l -> cl_stability.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    auto.
  Qed.

  Proposition cl_stable_r_imp_stable : cl_stability_r → cl_stability.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    auto.
  Qed.

  Hypothesis cl_stable_l : cl_stability_l.

  Proposition cl_stable_r : cl_stability_r.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    auto.
  Qed.

  Proposition cl_stable : cl_stability.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    auto.
  Qed.

  Hint Resolve cl_stable_r cl_stable : core.

  Hypothesis cl_neutral_1 : cl_neutrality_1.
  Hypothesis cl_neutral_2 : cl_neutrality_2.
  Hypothesis cl_associative : cl_associativity.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ *)

  Definition Magicwand A B k := sg k ∘ A ⊆ B.
  Infix "⊸" := Magicwand (at level 51, right associativity).

  Proposition magicwand_spec A B C : A ∘ B ⊆ C ↔ A ⊆ B ⊸ C.
  Proof.
    split; intros H x Hx.
    intros y Hy; apply H; revert Hy; apply composes_monotone; auto.
    apply sg_inc1; auto.
    destruct Hx as [ a b x Ha Hb Hx ].
    apply (H _ Ha).
    constructor 1 with a b; auto.
  Qed.

  Definition magicwand_adj_1 A B C := proj1 (magicwand_spec A B C).
  Definition magicwand_adj_2 A B C := proj2 (magicwand_spec A B C).

  (*  Hint Resolve magicwand_adj_1 magicwand_adj_2. *)

  Proposition magicwand_monotone A A' B B' : A ⊆ A' → B ⊆ B' → A' ⊸ B ⊆ A ⊸ B'.
  Proof.
    intros ? HB; apply magicwand_adj_1, inc1_trans with (2 := HB).
    intros _ [? ? ? Ha ? Hc]; apply Ha, In_composes with (3 := Hc); auto.
  Qed.

  Hint Resolve magicwand_monotone : core.

  Proposition cl_magicwand_1 X Y : cl (X ⊸ cl Y) ⊆ X ⊸ cl Y.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable_l. 
    apply magicwand_adj_1, 
          inc1_trans with (B := cl ((X ⊸ cl Y) ∘ X)); auto.
    rewrite <- cl_prop; apply magicwand_spec; auto. 
  Qed.

  Proposition cl_magicwand_2 X Y : cl X ⊸ Y ⊆ X ⊸ Y.
  Proof using cl_increase.
    apply magicwand_monotone; auto.
  Qed.

  Hint Immediate cl_magicwand_1 cl_magicwand_2 : core.

  Proposition cl_magicwand_3 X Y : X ⊸ cl Y ⊆ cl X ⊸ cl Y.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    intros c Hc y.
    apply inc1_trans with (B := cl (sg c ∘ X)); auto.
    rewrite <- cl_prop.
    intros ? [ a b d [] Hb ].
    intros; apply Hc. 
    constructor 1 with c b; auto.
  Qed.

  Hint Immediate cl_magicwand_3 : core.

  Proposition closed_magicwand X Y : closed Y → closed (X ⊸ Y).
  Proof using cl_idempotent cl_increase cl_monotone cl_stable_l. 
    simpl; intros ?.
    apply inc1_trans with (B := cl (X ⊸ cl Y)); auto.
    apply cl_monotone, magicwand_monotone; auto.
    apply inc1_trans with (B := X ⊸ cl Y); auto.
    apply magicwand_monotone; auto.
  Qed.

  Hint Resolve closed_magicwand : core.

  Proposition magicwand_eq_1 X Y : X ⊸ cl Y ≃ cl X ⊸ cl Y.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    split; auto.
  Qed.

  Proposition magicwand_eq_2 X Y : cl (X ⊸ cl Y) ≃ X ⊸ cl Y.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable_l.
    split; auto.
  Qed.

  Proposition magicwand_eq_3 X Y : cl (X ⊸ cl Y) ≃ cl X ⊸ cl Y.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    split; auto.
    apply inc1_trans with (B := X ⊸ cl Y); auto.
  Qed.

  Hint Resolve magicwand_eq_1 magicwand_eq_2 magicwand_eq_3 : core.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ *)

  Proposition cl_equiv_2 X Y : cl (cl X ∘ Y) ≃ cl (X ∘ Y).
  Proof using cl_idempotent cl_increase cl_monotone cl_stable_l. 
    split.
    rewrite <- cl_prop; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Proposition cl_equiv_3 X Y : cl (X ∘ cl Y) ≃ cl (X ∘ Y).
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    split.
    + rewrite <- cl_prop; auto.
    + apply cl_monotone, composes_monotone; auto.
  Qed.

  Proposition cl_equiv_4 X Y : cl (cl X ∘ cl Y) ≃ cl (X ∘ Y).
  Proof using cl cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l. 
    split.
    + rewrite <- cl_prop; auto.
    + apply cl_monotone, composes_monotone; auto.
  Qed.

  Hint Immediate cl_equiv_2 cl_equiv_3 cl_equiv_4 : core.

  Proposition composes_associative_1 A B C : A ∘ (B ∘ C) ⊆ cl ((A ∘ B) ∘ C).
  Proof using cl_associative cl_monotone.
    intros _ [a _ k Ha [b c y Hb Hc Hy] Hk].
    generalize (@cl_associative a b c k); intros H.
    spec all in H.
    + apply In_composes with (3 := Hk); auto.
      apply In_composes with (3 := Hy); auto.
    + revert H.
      apply cl_monotone.
      repeat apply composes_monotone; apply sg_inc1; auto.
  Qed.

  Hint Immediate composes_associative_1 : core.
  Hint Resolve composes_monotone : core.

  Proposition composes_associative A B C : cl (A ∘ (B ∘ C)) ≃ cl ((A ∘ B) ∘ C).
  Proof using cl_associative cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    split; auto.
    rewrite <- cl_prop; auto.
    rewrite <- cl_prop; auto.
    apply inc1_trans with (1 := @composes_commute_1 _ _).
    rewrite <- cl_prop.
    apply inc1_trans with (B := C ∘ cl (A ∘ B)); auto.
    1: apply composes_monotone; auto.
    apply inc1_trans with (B := C ∘ cl (B ∘ A)); auto.
    1: apply composes_monotone; auto; apply composes_commute. 
    apply inc1_trans with (1 := @cl_stable_r _ _).
    rewrite <- cl_prop.
    apply inc1_trans with (1 := @composes_associative_1 _ _ _).
    rewrite <- cl_prop.
    apply inc1_trans with (1 := @composes_commute_1 _ _). 
    rewrite <- cl_prop.
    apply inc1_trans with (B := A ∘ cl (C ∘ B)); auto.
    apply composes_monotone; auto.
    apply inc1_trans with (B := A ∘ cl (B ∘ C)); auto.
    apply composes_monotone; auto.
    apply composes_commute.
  Qed.

  Hint Immediate composes_associative : core.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ *)

  Proposition composes_congruent_1 A B C : A ⊆ cl B → C ∘ A ⊆ cl (C ∘ B).
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    intros ?.
    apply inc1_trans with (B := cl (C ∘ cl B)); auto.
    apply cl_prop, cl_monotone, composes_monotone; auto.
    apply cl_equiv_3.
  Qed.

  Hint Resolve composes_congruent_1 : core.

  Proposition composes_congruent A B C : cl A ≃ cl B → cl (C ∘ A) ≃ cl (C ∘ B).
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l. 
    intros [H1 H2].
    rewrite <- cl_prop in H1.
    rewrite <- cl_prop in H2.
    split; rewrite <- cl_prop;
    apply inc1_trans with (2 := @cl_stable_r _ _), composes_monotone; auto.
  Qed.

  Proposition composes_assoc_special A A' B B' : cl((A∘A') ∘ (B∘B')) ≃ cl ((A∘B) ∘ (A'∘B')).
  Proof using cl_associative cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    do 2 apply eq1_sym, eq1_trans with (2 := composes_associative _ _ _).
    apply composes_congruent.
    apply eq1_sym, eq1_trans with (1 := composes_commute _ _).
    apply eq1_sym, eq1_trans with (2 := composes_associative _ _ _).
    apply composes_congruent, composes_commute.
  Qed.

  Definition composes_assoc_special_1 A A' B B' := proj1 (composes_assoc_special A A' B B').

  Proposition composes_neutral_1 A : A ⊆ cl (sg e ∘ A).
  Proof using cl_monotone cl_neutral_1.
    intros a Ha.
    generalize (cl_neutral_1 a).
    apply cl_monotone, composes_monotone; auto.
    apply sg_inc1; auto.
  Qed.

  Proposition composes_neutral_2 A : sg e ∘ A ⊆ cl A.
  Proof using cl_monotone cl_neutral_2.
    intros _ [y a x [] Ha Hx].
    generalize (@cl_neutral_2 a x); intros H.
    spec all in H.
    constructor 1 with e a; auto.
    revert H; apply cl_monotone, sg_inc1; auto.
  Qed.

  Hint Resolve composes_neutral_1 composes_neutral_2 : core.

  Proposition composes_neutral A : cl (sg e ∘ A) ≃ cl A.
  Proof using cl_idempotent cl_increase cl_monotone cl_neutral_1 cl_neutral_2.
    split; rewrite <- cl_prop; auto.
  Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

  Notation "x 'glb' y " := (x ∩ y) (at level 50, no associativity).
  Notation "x 'lub' y" := (cl (x ∪ y)) (at level 50, no associativity).

  Proposition closed_glb A B : closed A → closed B → closed (A glb B).
  Proof using cl_monotone.
    exact (cap_closed _ _).
  Qed. 

  Fact cl_glb_closed A B : closed A → closed B → cl (A glb B) ≃ A glb B.
  Proof using cl_increase cl_monotone.
    auto using closed_glb, closed_eq1.
  Qed.

  Proposition lub_out A B C : closed C → A ⊆ C → B ⊆ C → A lub B ⊆ C.
  Proof using cl_increase cl_monotone. 
    simpl.
    intros H1 H2 H3.
    apply inc1_trans with (2 := H1), cl_monotone.
    intros ? [ ]; auto.
  Qed.

  Proposition glb_in A B C : C ⊆ A → C ⊆ B → C ⊆ A glb B.
  Proof. simpl; split; auto. Qed. 

  Proposition closed_lub A B : closed (A lub B).
  Proof using cl_idempotent.
    exact (cl_idempotent _).
  Qed.

  Proposition glb_out_l A B : A glb B ⊆ A .
  Proof. simpl; tauto. Qed.

  Proposition glb_out_r A B : A glb B ⊆ B.
  Proof. simpl; tauto. Qed.

  Proposition lub_in_l A B : A ⊆ A lub B.
  Proof using cl_increase.
    eauto.
  Qed.

  Proposition lub_in_r A B : B ⊆ A lub B.
  Proof using cl_increase.
    eauto.
  Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

  Notation "x ⊛ y " := (cl (x ∘ y)) (at level 59).

  Proposition closed_times A B : closed (A⊛B).
  Proof using cl_idempotent.
    simpl; eauto.
  Qed.

  Proposition times_monotone A A' B B' : A ⊆ A' → B ⊆ B' → A⊛B ⊆ A'⊛B'.
  Proof using cl_monotone.
    intros ? ?; simpl; apply cl_monotone, composes_monotone; auto.
  Qed.

  Abbreviation top := (λ _ : M, True).
  Abbreviation bot := (cl (λ _, False)).
  Abbreviation unit := (cl (sg e)). 

  Proposition closed_top : closed top.
  Proof. simpl; intros; auto. Qed.

  Proposition closed_bot : closed bot.
  Proof using cl_idempotent.
    simpl; apply cl_idempotent.
  Qed.

  Proposition closed_unit : closed unit.
  Proof using cl_idempotent.
    simpl; apply cl_idempotent.
  Qed.

  Proposition top_greatest A : A ⊆ top.
  Proof. simpl; tauto. Qed.

  Hint Resolve closed_glb closed_top : core.

  Let lcap := fold_right (λ x y, x∩y) top.

  Fact closed_mglb ll : Forall closed ll → closed (lcap ll). 
  Proof using cl_monotone.
    induction 1; simpl; auto.
  Qed.

  Hint Resolve closed_mglb : core.

  Proposition bot_least A : closed A → bot ⊆ A.
  Proof using cl_monotone.
    intro H; apply inc1_trans with (2 := H), cl_monotone; tauto.
  Qed.

  Proposition unit_neutral_1 A : closed A → unit ⊛ A ⊆ A.
  Proof using cl_idempotent cl_increase cl_monotone cl_neutral_2 cl_stable_l. 
    intros H; apply inc1_trans with (2 := H).
    rewrite <- cl_prop.
    apply inc1_trans with (1 := @cl_stable_l _ _).
    rewrite <- cl_prop.
    apply composes_neutral_2.
  Qed.

  Proposition unit_neutral_2 A : A ⊆ unit ⊛ A.
  Proof using cl_increase cl_monotone cl_neutral_1. 
    intros a Ha; simpl.
    generalize (composes_neutral_1 _ _ Ha).
    apply cl_monotone, composes_monotone; auto.
  Qed.

  (*  Hint Resolve unit_neutral_1 unit_neutral_2. *)

  Proposition unit_neutral A : closed A → unit ⊛ A ≃ A.
  Proof using cl_idempotent cl_increase cl_monotone cl_neutral_1 cl_neutral_2 cl_stable_l. 
    intros H; split. 
    revert H; apply unit_neutral_1.
    apply unit_neutral_2.
  Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

  Proposition times_commute_1 A B : A⊛B ⊆ B⊛A.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    simpl; apply cl_inc, composes_commute_1.
  Qed.

  Hint Resolve unit_neutral times_commute_1 : core.
 
  Proposition times_commute A B : A⊛B ≃ B⊛A.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    split; auto.
  Qed.

  Proposition unit_neutral' A : closed A → A ⊛ unit ≃ A.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_neutral_1 cl_neutral_2 cl_stable_l.
    intros ?; apply eq1_trans with (1 := times_commute _ _); auto.
  Qed.

  Proposition times_associative A B C : (A⊛B)⊛C ≃ A⊛(B⊛C).
  Proof using cl_associative cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    apply eq1_sym, eq1_trans with (1 := cl_equiv_3 _ _ ).
    apply eq1_sym, eq1_trans with (1 := cl_equiv_2 _ _ ).
    apply eq1_sym, composes_associative.
  Qed.

  Proposition times_associative_1 A B C : (A⊛B)⊛C ⊆ A⊛(B⊛C).
  Proof using cl_associative cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    apply times_associative.
  Qed.

  Proposition times_associative_2 A B C : A⊛(B⊛C) ⊆ (A⊛B)⊛C.
  Proof using cl_associative cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    apply times_associative.
  Qed.

  Hint Resolve times_associative_1 times_associative_2 : core.

  Proposition times_congruence A A' B B' : A ≃ A' → B ≃ B' → A⊛B ≃ A'⊛B'.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l. 
    intros H1 H2.
    apply eq1_trans with (A ⊛ B').
    apply composes_congruent; auto.
    do 2 apply eq1_sym, eq1_trans with (1 := times_commute _ _).
    apply composes_congruent; auto.
  Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

  Proposition adjunction_1 A B C : closed C → A ⊛ B ⊆ C → A ⊆ B ⊸ C.
  Proof using cl_increase.
    intros ? H; apply magicwand_adj_1, inc1_trans with (2 := H); auto.
  Qed.

  Proposition adjunction_2 A B C : closed C → A ⊆ B ⊸ C → A ⊛ B ⊆ C.
  Proof using cl_increase cl_monotone.
    intros H ?; apply inc1_trans with (2 := H), cl_monotone, magicwand_adj_2; auto.
  Qed.

  Hint Resolve times_congruence adjunction_1 (* adjunction_2 *) : core.

  Proposition adjunction A B C : closed C → A ⊛ B ⊆ C ↔ A ⊆ B ⊸ C.
  Proof using cl_increase cl_monotone.
    split; [ apply adjunction_1 | apply  adjunction_2 ]; auto.
  Qed.

  Proposition times_bot_distrib_l A : bot ⊛ A ⊆ bot.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable_l.
    apply adjunction_2; auto.
    apply bot_least; auto.
  Qed.

  Proposition times_bot_distrib_r A : A ⊛ bot ⊆ bot.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l.
    apply inc1_trans with (1 := @times_commute_1 _ _), times_bot_distrib_l.
  Qed.

  Hint Immediate times_bot_distrib_l times_bot_distrib_r : core.

  Proposition times_lub_distrib_l A B C : (A lub B) ⊛ C ⊆ (A ⊛ C) lub (B ⊛ C).
  Proof using cl_idempotent cl_increase cl_monotone cl_stable_l. 
    apply adjunction, lub_out; auto;
    apply adjunction; auto.
  Qed.

  Proposition times_lub_distrib_r A B C : C ⊛ (A lub B) ⊆ (C ⊛ A) lub (C ⊛ B).
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable_l. 
    apply inc1_trans with (1 := @times_commute_1 _ _),
          inc1_trans with (1 := @times_lub_distrib_l _ _ _); auto.
    apply lub_out; auto.
  Qed.

  Section bang.

    (* J := { x | x ∈ unit ∧ x ∈ x ⊛ x } with unit = cl e and x ⊛ x = cl (x∘x) *)

    Local Definition J x := unit x ∧ (cl (sg x ∘ sg x)) x.

    Local Fact In_J : ∀x, cl (sg e) x → (cl (sg x ∘ sg x)) x → J x.
    Proof. split; auto. Qed.

    Local Fact J_inv x : J x → unit x ∧ cl (sg x ∘ sg x) x.
    Proof. auto. Qed.

    Proposition J_inc_unit : J ⊆ unit.
    Proof. induction 1; trivial. Qed.

    Variable K : M → Prop.

    Abbreviation sub_monoid_hyp_1 := ((cl K) e).
    Abbreviation sub_monoid_hyp_2 := (K ∘ K ⊆ K).
    Abbreviation sub_J_hyp := (K ⊆ J).

    Hypothesis sub_monoid_1 : sub_monoid_hyp_1.
    Hypothesis sub_monoid_2 : sub_monoid_hyp_2.
    Hypothesis sub_J : sub_J_hyp.

    Proposition K_inc_unit : K ⊆ unit.
    Proof using sub_J.
      apply inc1_trans with J; trivial; apply J_inc_unit.
    Qed.

   (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ ❗ *)

    Proposition K_compose A B : (K ∩ A) ∘ (K ∩ B) ⊆ K ∩ (A ∘ B).
    Proof using sub_monoid_2.
      intros x Hx.
      induction Hx as [ a b c [ ] [ ] Hc ]; split.
      + apply sub_monoid_2; constructor 1 with a b; auto.
      + constructor 1 with a b; auto.
    Qed.

    Local Definition store A := cl (K∩A).

    Notation "! A" := (store A) (at level 40, no associativity, format "! A").

    Fact store_inc_unit A : !A ⊆ unit.
    Proof using cl_idempotent cl_increase cl_monotone sub_J. 
      apply inc1_trans with (cl K).
      + apply cl_monotone; tauto.
      + apply cl_inc, K_inc_unit.
    Qed.

    Hint Resolve store_inc_unit : core.

    Proposition closed_store A : closed (!A).
    Proof using cl_idempotent.
      simpl; apply cl_idempotent.
    Qed.

    Proposition store_dec A : closed A → !A ⊆ A.
    Proof using cl_monotone.
      intros HA; simpl.
      apply inc1_trans with (cl A); trivial.
      apply cl_monotone, glb_out_r.
    Qed.

    Fact store_monotone A B : A ⊆ B → !A ⊆ !B.
    Proof using cl_monotone.
      intro; apply cl_monotone.
      intros ? []; split; auto.
    Qed.

    Proposition store_der A B : closed B → !A ⊆ B → !A ⊆ !B.
    Proof using cl_increase cl_monotone.
      unfold store.
      intros ? ?; apply cl_monotone; intros x []; split; auto.
    Qed.
 
    Proposition store_unit_1 : unit ⊆ !top.
    Proof using cl_idempotent cl_increase cl_monotone sub_monoid_1.
      apply cl_inc.
      intros ? []; apply cl_monotone with K; auto.
    Qed.

    Hint Resolve J_inc_unit : core.
 
    Proposition store_unit_2 : !top ⊆ unit.
    Proof using cl_idempotent cl_increase cl_monotone sub_J.
      apply cl_inc; trivial.
      apply inc1_trans with J; auto.
      intros ? []; auto.
    Qed.

    Hint Resolve store_unit_1 store_unit_2 : core.

    Proposition store_unit : unit ≃ !top.
    Proof using cl_idempotent cl_increase cl_monotone sub_J sub_monoid_1.
      split; auto.
    Qed.

    (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

    Proposition store_comp A B : closed A → closed B → !A ⊛ !B ≃ !(A∩B).
    Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_neutral_2 cl_stable_l sub_J sub_monoid_2.
      intros HA HB; split.
      + apply inc1_trans with (cl ((K glb A) ∘ (K glb B))).
        * apply cl_inc; trivial; apply cl_stable.
        * apply cl_monotone.
          intros x [ a b c [ H1 H2 ] [ H3 H4 ] Hc ].
          assert (H5 : unit a). { apply K_inc_unit; auto. }
          assert (H6 : unit b). { apply K_inc_unit; auto. }
          split; [ | split ].
          - apply sub_monoid_2; constructor 1 with a b; auto.
          - apply unit_neutral_1; auto; apply times_commute_1, cl_increase.
            constructor 1 with a b; auto.
          - apply unit_neutral_1; auto; apply cl_increase.
            constructor 1 with a b; auto.
      + apply cl_inc; trivial.
        intros x (H1 & H2 & H3).
        apply cl_monotone with (sg x ∘ sg x).
        2: { apply sub_J in H1; destruct H1; trivial. }
        intros d [ a b ? ? Hab ]; subst a b; constructor 1 with x x; auto; 
          apply cl_increase; auto.
    Qed.

    Let ltimes := fold_right (λ x y, x ⊛ y) unit.

    Proposition ltimes_store ll : Forall closed ll → ltimes (map store ll) ≃ !(lcap ll).
    Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_neutral_2 cl_stable_l lcap ltimes sub_J sub_monoid_1 sub_monoid_2.
      unfold ltimes, lcap.
      induction 1 as [ | A ll H1 H2 IH2 ]; auto.
      + simpl; auto.
      + simpl.
        apply eq1_trans with (!A ⊛ !(lcap ll)).
        * apply times_congruence; auto.
        * apply eq1_trans with (!(A ∩ lcap ll)); auto.
          apply store_comp; auto.
    Qed.

    Proposition store_compose_idem A : closed A → !A ⊆ !A⊛!A.
    Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_neutral_2 cl_stable_l lcap sub_J sub_monoid_2.
      intros HA.
      apply inc1_trans with (!(A∩A)).
      + apply store_der. 
        * apply closed_glb; trivial.
        * apply inc1_trans with A.
          - apply store_dec; trivial.
          - tauto.
      + apply (proj2 (store_comp _ _ HA HA)).
    Qed.

  End bang.

  Section Intuitionist.
  
    Hypothesis cl_weak : ∀x, cl (sg e) x.
    Hypothesis cl_cntr : ∀x, cl (sg x ∘ sg x) x. 

    Let K := top.

    Local Fact sub_monoid_1 : cl K e.
    Proof using cl_increase.
      apply cl_increase; now red.
    Qed.

    Local Fact sub_monoid_2 : K ∘ K ⊆ K.
    Proof. now unfold K. Qed.

    Local Fact sub_J : K ⊆ J.
    Proof using cl_weak cl_cntr.
      split; auto.
    Qed.
    
    Hint Resolve sub_monoid_1 sub_monoid_2 sub_J : core.

    Local Fact K_inc_unit' : K ⊆ unit.
    Proof using cl_cntr cl_weak. apply K_inc_unit, sub_J. Qed.

    Local Fact store_inc A : A ⊆ store K A.
    Proof using cl_increase. 
      unfold store, K.
      apply inc1_trans with (2 := cl_increase _); auto.
    Qed.

    Local Fact store_eq1 A : closed A → A ≃ store K A.
    Proof using cl_increase cl_monotone.
      intros HA; split; auto using store_inc.
      now apply store_dec.
    Qed.

    Local Fact times_id_glb A B : closed A → closed B → A ⊛ B ≃ A glb B.
    Proof using cl_cntr cl_commute cl_idempotent cl_increase cl_monotone cl_neutral_2 cl_stable_l cl_weak.
      intros HA HB.
      apply eq1_trans with (store K A ⊛ store K B).
      1: auto using times_congruence, store_eq1.
      apply eq1_trans with (store K (A glb B)).
      1: auto using store_comp.
      auto using store_eq1, eq1_sym.
    Qed.

(*
    Proposition times_leq_glb A B : closed A -> closed B -> A times B inc A glb B.
    Proof. intros A B HA HB. apply (proj1 (times_id_glb _ _ HA HB)). Qed.

    Proposition glb_leq_times A B : closed A -> closed B -> A glb B inc A times B.
    Proof. intros A B HA HB. apply (proj2 (times_id_glb _ _ HA HB)). Qed.

    Hint Resolve times_leq_glb glb_leq_times.
    *)

(*
    Proposition top_neutral A : top glb A ≃ A.
    Proof. split; auto. Qed.

    Proposition top_neutral_1 A : closed A -> top glb A inc A.
    Proof. intros. auto. Qed.

    Proposition glb_monotone (A A' B B' : Predicate M) : A inc A' -> B inc B' -> A glb B inc A' glb B'.
    Proof. intros. auto. Qed.

    Proposition lub_monotone (A A' B B' : Predicate M) : A inc A' -> B inc B' -> A lub B inc A' lub B'.
    Proof. intros. auto. Qed.

    Proposition glb_commute (A B : Predicate M) : A glb B ~ B glb A.
    Proof. split; auto. Qed.

    Proposition glb_associative (A B C : Predicate M) : (A glb B) glb C ~ A glb (B glb C).
    Proof. split; auto. Qed.

    Proposition glb_congruence (A A' B B' : Predicate M) : A ~ A' -> B ~ B' -> A glb B ~ A' glb B'.
    Proof. intros A A' B B' (H1,H2) (H3,H4). split; auto. Qed.

    Proposition glb_adjunction_1 A B C : closed A -> closed B -> closed C -> A glb B inc C -> A inc B -o C.
    Proof.
      intros A B C HA HB HC H. 
      apply magicwand_adj_1. 
      apply inc_transitive with (2 := H).
      auto.
    Qed.

    Proposition glb_adjunction_2 A B C : closed A -> closed B -> closed C -> A inc B -o C -> A glb B inc C.
    Proof.
      intros A B C HA HB HC H. 
      apply magicwand_adj_2 in H.  
      apply (cl_inc_1 _ Closure) in H; auto.
      apply inc_transitive with (2 := H).
      auto.
    Qed.

    Hint Resolve glb_adjunction_1 glb_adjunction_2 : core.
 
    Proposition glb_adjunction A B C : closed A -> closed B -> closed C -> (A glb B inc C <-> A inc B -o C).
    Proof. split; auto. Qed.

    Proposition glb_bot_distrib_l A : bot glb A inc bot.
    Proof.  intros. auto. Qed. 

    Proposition glb_bot_distrib_r A : A glb bot inc bot.
    Proof. intros. auto. Qed.

    Proposition glb_lub_distrib_l A B C : closed A -> closed B -> closed C -> (A lub B) glb C inc (A glb C) lub (B glb C).
    Proof. intros. apply (inc_transitive _ ((A lub B) times C)); auto. Qed.
 
    Proposition glb_lub_distrib_r A B C : closed A -> closed B -> closed C -> C glb (A lub B) inc (C glb A) lub (C glb B).
    Proof.
      intros.
      apply (inc_transitive _ ((A lub B) glb C)); auto.
      apply (inc_transitive _ ((A glb C) lub (B glb C))); auto.
      apply cl_mono. auto.
    Qed.

  *)
  End Intuitionist.


End Relational_phase_semantics.

Section Sem_BI.

  Variables (M : Type) (cl : (M → Prop) → (M → Prop)).

  Abbreviation closed := (λ x, cl x ⊆ x).

  Hypothesis cl_increase   : ∀A, A ⊆ cl A.
  Hypothesis cl_monotone   : ∀ A B, A ⊆ B → cl A ⊆ cl B.
  Hypothesis cl_idempotent : ∀ A, cl (cl A) ⊆ cl A.

  Variables (comp_m : M → M → M → Prop) (unit_m : M)
            (comp_a : M → M → M → Prop) (unit_a : M).

  Notation " x '∘' y" := (Composes _ comp_m x y) (at level 50, no associativity).
  Notation " x '⊸' y " := (Magicwand _ comp_m x y) (at level 51, right associativity).
  Abbreviation eₘ := unit_m.

  Hypothesis cl_stable_m_l : ∀ A B, cl A ∘ B ⊆ cl (A ∘ B).
  Hypothesis cl_neutral_1_m : ∀x, cl (sg eₘ ∘ sg x) x.
  Hypothesis cl_neutral_2_m : ∀x, sg eₘ ∘ sg x ⊆ cl (sg x).
  Hypothesis cl_commute_m : ∀ x y, sg x ∘ sg y ⊆ cl (sg y ∘ sg x).
  Hypothesis cl_associative_m : ∀ x y z, sg x ∘ (sg y ∘ sg z) ⊆ cl ((sg x ∘ sg y) ∘ sg z).

  Notation " x '⨣' y" := (Composes _ comp_a x y) (at level 50, no associativity).
  Notation " x '-⨣' y " := (Magicwand _ comp_a x y) (at level 51, right associativity).
  Abbreviation eₐ := unit_a.

  Hypothesis cl_stable_a_l : ∀ A B, cl A ⨣ B ⊆ cl (A ⨣ B).
  Hypothesis cl_neutral_1_a : ∀x, cl (sg eₐ ⨣ sg x) x.
  Hypothesis cl_neutral_2_a : ∀x, sg eₐ ⨣ sg x ⊆ cl (sg x).
  Hypothesis cl_commute_a : ∀ x y, sg x ⨣ sg y ⊆ cl (sg y ⨣ sg x).
  Hypothesis cl_associative_a : ∀ x y z, sg x ⨣ (sg y ⨣ sg z) ⊆ cl ((sg x ⨣ sg y) ⨣ sg z).

  Notation "x 'glb' y" := (x ∩ y) (at level 50, no associativity).
  Notation "x 'lub' y" := (cl (x ∪ y)) (at level 50, no associativity).
  
  Abbreviation top := (λ _ : M, True).
  Abbreviation bot := (cl (λ _, False)).
  Abbreviation unit := (cl (sg eₘ)). 
  
  Hypothesis cl_weak : ∀x, cl (sg eₐ) x.
  Hypothesis cl_cntr : ∀x, cl (sg x ⨣ sg x) x.
  
  Fact compose_eq1_glb A B : closed A → closed B → cl (A ⨣ B) ≃ A glb B.
  Proof using cl_cntr cl_commute_a cl_idempotent cl_increase cl_monotone cl_neutral_2_a cl_stable_a_l cl_weak.
    apply times_id_glb with eₐ; auto.
  Qed.

  Variables (µ : BI_conn → bool) (prop : Set).

  Section sem_form.

    Variable phi : prop → M → Prop.

    Hypothesis phi_closed : ∀v, closed (phi v).

    Fixpoint sem_form (f : BI_form µ prop) { struct f } : M → Prop :=
      match f with
      | BI_form_var _ v => phi v
      | BI_form_unit _ _ BI_mult _ => cl (sg eₘ)
      | BI_form_unit _ _ BI_addi _ => cl (sg eₐ)
      | BI_form_conj BI_mult _ a b => cl (sem_form a ∘ sem_form b)
      | BI_form_conj BI_addi _ a b => cl (sem_form a ⨣ sem_form b)
      | BI_form_impl BI_mult _ a b => sem_form a ⊸ sem_form b
      | BI_form_impl BI_addi _ a b => sem_form a -⨣ sem_form b
      | BI_form_bot  _ _ _ => bot
      | BI_form_disj _ a b => sem_form a lub sem_form b
      end.
      
    Fact sem_form_closed f : closed (sem_form f).
    Proof using cl_idempotent cl_increase cl_monotone cl_stable_a_l cl_stable_m_l cl_weak comp_a comp_m phi_closed.
      induction f as [ | [] | [] | [] | | ]; simpl; eauto using closed_magicwand.
    Qed.

  End sem_form.

  Section sem_bunch.

    Definition sem_bunch phi :=
      fix loop (b : BI_bunch µ prop) : M → Prop :=
        match b with
        | ⟨A⟩ => phi A
        | øₘ => cl (sg eₘ)
        | øₐ => cl (sg eₐ)
        | Γ ⊛ₘ Δ => cl (loop Γ ∘ loop Δ)
        | Γ ⊛ₐ Δ => cl (loop Γ ⨣ loop Δ)
        end.

    Fact sem_bunch_closed phi : (∀f, closed (phi f)) → (∀f, closed (sem_bunch phi f)).
    Proof using cl_idempotent cl_monotone.
      clear cl_weak.
      intros ? f; induction f as [ | [] | [] ]; simpl; eauto.
    Qed.

    Hint Resolve sem_bunch_closed : core.

    Section bunch_eq_soundness.

      Variable phi : BI_form µ prop → M → Prop.
      Hypothesis phi_closed : ∀A, closed (phi A).

      Hint Resolve eq1_refl eq1_sym eq1_trans unit_neutral : core.

      Lemma sem_bunch_soundness Γ Δ : Γ ≡ Δ → sem_bunch phi Γ ≃ sem_bunch phi Δ.
      Proof using cl_associative_a cl_associative_m 
                  cl_commute_a cl_commute_m 
                  cl_idempotent cl_increase cl_monotone
                  cl_neutral_1_a cl_neutral_1_m 
                  cl_neutral_2_a cl_neutral_2_m
                  cl_stable_a_l 
                  cl_stable_m_l
                  phi_closed.
        induction 1 as [ | | | [] | [] | [] | [] ]; eauto.
        + apply unit_neutral; auto.
        + apply unit_neutral; auto.
        + apply times_commute; auto.
        + apply times_commute; auto.
        + apply times_associative; auto.
        + apply times_associative; auto.
        + apply times_congruence; auto.
        + apply times_congruence; auto.
      Qed.

    End bunch_eq_soundness.

    Fact sem_ctx_lub phi Σ A B (h : µ BI_disj = true) : sem_bunch (sem_form phi) Σ[⟨BI_form_disj h A B⟩] ⊆ sem_bunch (sem_form phi) Σ[⟨A⟩] lub sem_bunch (sem_form phi) Σ[⟨B⟩].
    Proof using cl_commute_a cl_commute_m cl_idempotent cl_increase cl_monotone cl_stable_a_l cl_stable_m_l.
      induction Σ as [ | [] [] G D IH ].
      + simpl; auto.
      + simpl.
        apply inc1_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ (inc1_refl _ _) IH).
        eapply inc1_trans; [ apply times_lub_distrib_r | ]; auto.
      + simpl.
        apply inc1_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ (inc1_refl _ _) IH).
        eapply inc1_trans; [ apply times_lub_distrib_r | ]; auto.
      + simpl.
        apply inc1_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ IH (inc1_refl _ _)).
        eapply inc1_trans; [ apply times_lub_distrib_l | ]; auto.
      + simpl.
        apply inc1_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ IH (inc1_refl _ _)).
        eapply inc1_trans; [ apply times_lub_distrib_l | ]; auto.
    Qed. 

    Fact sem_ctx_bot phi Σ Δ : sem_bunch phi Δ ⊆ bot → sem_bunch phi Σ[Δ] ⊆ bot.
    Proof using  cl_commute_a cl_commute_m cl_idempotent cl_increase cl_monotone cl_stable_a_l cl_stable_m_l.
      intros Hdelta.
      induction Σ as [ | [] [] G D IH ].
      1: simpl; auto.
      1,2: simpl; apply inc1_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ (inc1_refl _ _) IH); apply times_bot_distrib_r; auto.
      1,2: simpl; apply inc1_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ IH (inc1_refl _ _)); apply times_bot_distrib_l; auto.
    Qed.

    Fact sem_ctx_monotone phi Σ Γ Δ :
        sem_bunch phi Γ ⊆ sem_bunch phi Δ
      → sem_bunch phi Σ[Γ] ⊆ sem_bunch phi Σ[Δ].
    Proof using cl_monotone.
      intros H.
      induction Σ as [ | [] [] ].
      1: simpl; auto.
      all: simpl; apply times_monotone; auto.
    Qed.
    
  End sem_bunch.

  Variables (cut : BI_cut) (phi : prop → M → Prop) (phi_closed : ∀v, closed (phi v)).
 
  Hint Resolve sem_form_closed : core.
  
  Theorem LBI_soundness Γ A : Γ L⊦[cut] A → sem_bunch (sem_form phi) Γ ⊆ sem_form phi A.
  Proof using cl_idempotent cl_increase cl_monotone 
              cl_neutral_1_a cl_neutral_1_m 
              cl_neutral_2_a cl_neutral_2_m
              cl_associative_a cl_associative_m
              cl_commute_a cl_commute_m 
              cl_stable_a_l cl_stable_m_l
              cl_cntr cl_weak
              phi_closed.
    induction 1 as [ 
                     | ? Γ Δ A B _ IH1 _ IH2 
                     | Γ Δ A H _ IH
                     | Γ Δ A _ IH
                     | Γ Δ A _ IH
                     | [] hk Γ A _ IH
                     | [] hk
                     | [] hk Γ A B C _ IH
                     | [] hk Γ Δ A B _ IH1 _ IH2
                     | [] hk Γ Δ A B C _ IH1 _ IH2
                     | [] hk Γ A B _ IH
                     |
                     | Γ Δ A B C _ IH1 _ IH2
                     | ? Γ A B _ IH
                     | ? Γ A B _ IH
                     ].
    + simpl; auto.
    + apply inc1_trans with (2 := IH2), sem_ctx_monotone; now simpl.
    + apply inc1_trans with (2 := IH), sem_bunch_soundness; auto.
    + apply inc1_trans with (2 := IH), sem_ctx_monotone; simpl.
      intros ? ?; apply cl_weak.
    + apply inc1_trans with (2 := IH), sem_ctx_monotone; simpl.
      intros x Hx.
      generalize (cl_cntr x).
      apply times_monotone; auto.
      all: now intros ? [].
    + apply inc1_trans with (2 := IH), sem_ctx_monotone; now simpl.
    + apply inc1_trans with (2 := IH), sem_ctx_monotone; now simpl.
    + now simpl.
    + now simpl.
    + apply inc1_trans with (2 := IH), sem_ctx_monotone; now simpl.
    + apply inc1_trans with (2 := IH), sem_ctx_monotone; now simpl.
    + simpl; apply times_monotone; auto.
    + simpl; apply times_monotone; auto.
    + apply inc1_trans with (2 := IH2), sem_ctx_monotone; simpl.
      eapply inc1_trans; [ apply composes_commute; auto | ].
      apply cl_closed; auto.
      apply magicwand_spec, magicwand_monotone; auto.
    + apply inc1_trans with (2 := IH2), sem_ctx_monotone; simpl.
      eapply inc1_trans; [ apply composes_commute; auto | ].
      apply cl_closed; auto.
      apply magicwand_spec, magicwand_monotone; auto.
    + simpl.
      apply magicwand_spec, inc1_trans with (2 := IH).
      simpl; auto.
    + simpl.
      apply magicwand_spec, inc1_trans with (2 := IH).
      simpl; auto.
    + eapply inc1_trans; [ apply sem_ctx_bot | apply bot_least ]; auto.
    + eapply inc1_trans; [ apply sem_ctx_lub | ].
      apply lub_out; auto.
    + simpl; apply inc1_trans with (1 := IH), lub_in_l; auto.
    + simpl; apply inc1_trans with (1 := IH), lub_in_r; auto.
  Qed.

End Sem_BI.

Section cut_elim.

  Variables (µ : BI_conn → bool) (prop : Set).

  Let M := BI_bunch µ prop.

  Implicit Types (Γ : M) (X Y : M → Prop).

  Let cl X Γ := ∀ Σ A, (∀Δ, X Δ → Σ[Δ] L⊦[BI_cut_free] A) → Σ[Γ] L⊦[BI_cut_free] A.
  
  Local Fact cl_bequiv X Γ Δ : Γ ≡ Δ → cl X Γ → cl X Δ.
  Proof.
    intros H1 H2 Σ A H3.
    apply BI_bequiv_ctx with (Σ := Σ) in H1.
    apply LBI_equiv with (1 := H1); auto.
  Qed.

  Local Fact cl_increase X : X ⊆ cl X.
  Proof. intros Γ HΓ Σ A H; now apply H. Qed.

  Local Fact cl_monotone X Y : X ⊆ Y → cl X ⊆ cl Y.
  Proof.
    intros HXY Γ HΓ Σ A H.
    apply HΓ.
    intros ? ?%HXY; auto.
  Qed.

  Local Fact cl_idempotent X : cl (cl X) ⊆ cl X.
  Proof.
    intros Γ HΓ Σ A H; apply HΓ.
    intros D HD; apply HD; auto.
  Qed.
  
  Hint Resolve cl_monotone cl_increase cl_idempotent : core.

  Let comp_m (Γ Δ Θ : M) := Γ ⊛ₘ Δ ≡ Θ.
  Let comp_a (Γ Δ Θ : M) := Γ ⊛ₐ Δ ≡ Θ.

  Let unit_m : M := øₘ.
  Let unit_a : M := øₐ.

  Notation " x '∘' y" := (Composes _ comp_m x y) (at level 50, no associativity).
  Notation " x '⊸' y " := (Magicwand _ comp_m x y) (at level 51, right associativity).
  Abbreviation eₘ := unit_m.

  Notation " x '⨣' y" := (Composes _ comp_a x y) (at level 50, no associativity).
  Notation " x '-⨣' y " := (Magicwand _ comp_a x y) (at level 51, right associativity).
  Abbreviation eₐ := unit_a.
  
  Hint Constructors BI_bunch_equiv Composes : core.

  Local Fact cl_stable_m_l X Y : cl X ∘ Y ⊆ cl (X ∘ Y).
  Proof.
    intros _ [ Γ Δ Θ H1 H2 H3 ] Σ A H; red in H3.
    apply BI_bequiv_ctx with (Σ := Σ) in H3.
    apply LBI_equiv with (1 := H3).
    red in H1.
    change (Σ[Γ ⊛ₘ Δ])
    with    (Σ[(BI_ctx_comp BI_right BI_mult Δ (BI_ctx_hole _ _))[Γ]]).
    rewrite BI_ctx_compose_subst.
    apply H1.
    intros D HD.
    rewrite <- BI_ctx_compose_subst; simpl.
    apply H.
    exists D Δ; try red; auto.
  Qed.

  Local Fact cl_neutral_1_m Γ : cl (sg eₘ ∘ sg Γ) Γ.
  Proof.
    intros Σ A H; apply H.
    exists øₘ Γ; try red; auto.
  Qed.
  
  Hint Resolve BI_bequiv_ctx : core.

  Local Fact cl_neutral_2_m Γ : sg eₘ ∘ sg Γ ⊆ cl (sg Γ).
  Proof.
    intros _ [ ? ? Δ <- <- H].
    apply cl_bequiv with Γ; eauto.
  Qed.
  
  Local Fact cl_commute_m Γ Δ : sg Γ ∘ sg Δ ⊆ cl (sg Δ ∘ sg Γ).
  Proof.
    intros _ [ ? ? Θ <- <- H ].
    apply cl_bequiv with (Δ ⊛ₘ Γ); eauto.
    apply cl_increase; eauto.
    exists Δ Γ; try red; auto.
  Qed.

  Local Fact cl_associative_m Γ Δ Θ : sg Γ ∘ (sg Δ ∘ sg Θ) ⊆ cl ((sg Γ ∘ sg Δ) ∘ sg Θ).
  Proof.
    intros _ [ _ _ D <- [ _ _ C <- <- H1 ] H2 ].
    apply cl_bequiv with ((Γ ⊛ₘ Δ) ⊛ₘ Θ); auto.
    + red in H1, H2; eauto.
    + apply cl_increase.
      exists (Γ ⊛ₘ Δ) Θ; try red; auto.
      exists Γ Δ; try red; auto.
  Qed.
  
  Local Fact cl_stable_a_l X Y : cl X ⨣ Y ⊆ cl (X ⨣ Y).
  Proof.
    intros _ [ Γ Δ Θ H1 H2 H3 ] Σ A H; red in H3.
    apply BI_bequiv_ctx with (Σ := Σ) in H3.
    apply LBI_equiv with (1 := H3).
    red in H1.
    change (Σ[Γ ⊛ₐ Δ])
    with    (Σ[(BI_ctx_comp BI_right BI_addi Δ (BI_ctx_hole _ _))[Γ]]).
    rewrite BI_ctx_compose_subst.
    apply H1.
    intros D HD.
    rewrite <- BI_ctx_compose_subst; simpl.
    apply H.
    exists D Δ; try red; auto.
  Qed.

  Local Fact cl_neutral_1_a Γ : cl (sg eₐ ⨣ sg Γ) Γ.
  Proof.
    intros Σ A H; apply H.
    exists øₐ Γ; try red; auto.
  Qed.
  
  Local Fact cl_neutral_2_a Γ : sg eₐ ⨣ sg Γ ⊆ cl (sg Γ).
  Proof.
    intros _ [ ? ? Δ <- <- H].
    apply cl_bequiv with Γ; eauto.
  Qed.
  
  Local Fact cl_commute_a Γ Δ : sg Γ ⨣ sg Δ ⊆ cl (sg Δ ⨣ sg Γ).
  Proof.
    intros _ [ ? ? Θ <- <- H ].
    apply cl_bequiv with (Δ ⊛ₐ Γ); eauto.
    apply cl_increase; eauto.
    exists Δ Γ; try red; auto.
  Qed.

  Local Fact cl_associative_a Γ Δ Θ : sg Γ ⨣ (sg Δ ⨣ sg Θ) ⊆ cl ((sg Γ ⨣ sg Δ) ⨣ sg Θ).
  Proof.
    intros _ [ _ _ D <- [ _ _ C <- <- H1 ] H2 ].
    apply cl_bequiv with ((Γ ⊛ₐ Δ) ⊛ₐ Θ); auto.
    + red in H1, H2; eauto.
    + apply cl_increase.
      exists (Γ ⊛ₐ Δ) Θ; try red; auto.
      exists Γ Δ; try red; auto.
  Qed.

  Local Fact cl_weak Γ : cl (sg eₐ) Γ.
  Proof. intros Σ A H; now apply LBI_weak, H. Qed.

  Local Fact cl_cntr Γ : cl (sg Γ ⨣ sg Γ) Γ.
  Proof.
    intros Σ A H.
    apply LBI_cntr, H.
    exists Γ Γ; try red; auto.
  Qed.
  
  Let dwncl A Γ := Γ L⊦[BI_cut_free] A.  
  Let sem_form :=  sem_form _ cl comp_m unit_m comp_a unit_a µ prop (fun x => dwncl (BI_form_var µ x)).
  Let sem_bunch := sem_bunch _ cl comp_m unit_m comp_a unit_a _ _ sem_form.

  Local Fact dwncl_closed A : cl (dwncl A) ⊆ dwncl A.
  Proof.
    intros G H1.
    apply (H1 (BI_ctx_hole _ _)); simpl; auto.
  Qed.

  Hint Resolve cl_idempotent cl_increase cl_monotone 
              cl_neutral_1_a cl_neutral_1_m 
              cl_neutral_2_a cl_neutral_2_m
              cl_associative_a cl_associative_m
              cl_commute_a cl_commute_m 
              cl_stable_a_l cl_stable_m_l
              cl_cntr cl_weak 
              dwncl_closed : core.

  Local Fact sem_form_is_closed A : cl (sem_form A) ⊆ sem_form A.
  Proof. apply sem_form_closed; eauto. Qed.

  Hint Resolve sem_form_is_closed : core.

  Local Fact sem_bunch_is_closed Γ : cl (sem_bunch Γ) ⊆ sem_bunch Γ.
  Proof. apply sem_bunch_closed; eauto. Qed.

  Hint Resolve sem_bunch_is_closed : core.

  Local Lemma sem_form_Okada A : sem_form A ⟨A⟩ ∧ sem_form A ⊆ dwncl A.
  Proof.
    induction A as [ 
                   | [] Hµ 
                   | [] Hµ A [IHA1 IHA2] B [IHB1 IHB2] 
                   | [] Hµ A [IHA1 IHA2] B [IHB1 IHB2] 
                   | Hµ 
                   | Hµ A [IHA1 IHA2] B [IHB1 IHB2]  ]; simpl; split; auto.
    + apply LBI_axiom.
    + intros ? ? ?; rule LBI_unit_l at [].
    + apply cl_closed; eauto.
      intros ? <-; red.
      apply LBI_unit_r.
    + apply cl_closed; eauto.
      intros ? <-; red.
      apply LBI_unit_r.
    + intros Σ C HC; rule LBI_conj_l at [].
      apply HC.
      exists ⟨A⟩ ⟨B⟩; try red; auto.
    + apply cl_closed; eauto.
      intros _ [ G D K ? ? E ]; simpl.
      apply LBI_equiv with (1 := E).
      apply LBI_conj_r.
      * now apply IHA2.
      * now apply IHB2.
    + intros Σ C HC; rule LBI_conj_l at [].
      apply HC.
      exists ⟨A⟩ ⟨B⟩; try red; auto.
    + apply cl_closed; eauto.
      intros _ [ G D K ? ? E ]; simpl.
      apply LBI_equiv with (1 := E).
      apply LBI_conj_r.
      * now apply IHA2.
      * now apply IHB2.
    + apply magicwand_monotone with (A' := dwncl A) (B := cl (sg ⟨B⟩)); auto.
      * apply cl_closed; eauto; intros ? <-; auto.
      * intros Γ [? G D <- HG HD]; red in HG, HD.
        apply cl_bequiv with (1 := HD),
              cl_bequiv with (1 := BI_bequiv_comm _ _ _).
        intros ? ? ?; apply LBI_impl_l; auto.
    + eapply inc1_trans.
      1:{ apply magicwand_monotone with (A := sg ⟨A⟩) (B' := dwncl B); auto.
          intros ? <-; auto. }
      intros G HG; red in HG |- *.
      apply LBI_impl_r, HG.
      exists G ⟨A⟩; try red; auto.
    + apply magicwand_monotone with (A' := dwncl A) (B := cl (sg ⟨B⟩)); auto.
      * apply cl_closed; eauto; intros ? <-; auto.
      * intros Γ [? G D <- HG HD]; red in HG, HD.
        apply cl_bequiv with (1 := HD),
              cl_bequiv with (1 := BI_bequiv_comm _ _ _).
        intros ? ? ?; apply LBI_impl_l; auto.
    + eapply inc1_trans.
      1:{ apply magicwand_monotone with (A := sg ⟨A⟩) (B' := dwncl B); auto.
          intros ? <-; auto. }
      intros G HG; red in HG |- *.
      apply LBI_impl_r, HG.
      exists G ⟨A⟩; try red; auto.
    + intros ? ? ?; apply LBI_bot_l.
    + apply cl_closed; now eauto.
    + intros Σ C HC; apply LBI_disj_l; apply HC; tauto.
    + apply cl_closed; eauto.
      intros ? []; [ apply LBI_disj_r1, IHA2 | apply LBI_disj_r2, IHB2 ]; auto.
  Qed.

  Local Corollary sem_bunch_Okada Γ : sem_bunch Γ Γ.
  Proof.
    induction Γ as [ | [] | [] ]; simpl.
    + apply sem_form_Okada.
    + apply cl_increase; auto.
    + apply cl_increase; auto.
    + apply cl_increase; exists Γ1 Γ2; red; auto.
    + apply cl_increase; exists Γ1 Γ2; red; auto.
  Qed.

  Theorem LBI_cut_elim cut Γ A : Γ L⊦[cut] A → Γ L⊦[BI_cut_free] A.
  Proof.
    intros H.
    cut (sem_bunch Γ ⊆ sem_form A).
    + intros H1; apply sem_form_Okada, H1, sem_bunch_Okada.
    + revert H; apply LBI_soundness; eauto.
  Qed.

End cut_elim.

Check LBI_cut_elim. 
