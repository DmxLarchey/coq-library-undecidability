(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Utf8.

From Undecidability.BI
  Require Import BI utils lbi.

Import BI_notations LBI_tactics.

#[local] Reserved Notation "x ∘ y" (at level 50, no associativity, format "x ∘ y").
#[local] Reserved Notation "x ⊸ y" (at level 51, right associativity, format "x ⊸ y").
#[local] Reserved Notation "x ⊛ y "(at level 50, no associativity, format "x ⊛ y").

#[local] Reserved Notation "x ⨣ y" (at level 50, no associativity, format "x ⨣ y").
#[local] Reserved Notation "x '-⨣' y" (at level 51, right associativity, format "x -⨣ y").

#[local] Reserved Notation "x 'lub' y" (at level 50, no associativity, format "x  lub  y").

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70, format "X  ⊆  Y", no associativity).
#[local] Notation "X ≃ Y" := (X ⊆ Y ∧ Y ⊆ X) (at level 70, format "X  ≃  Y", no associativity).

Fact inc_refl X (A : X → Prop) : A ⊆ A.
Proof. auto. Qed.

Fact inc_trans X (A B C : X → Prop) : A ⊆ B → B ⊆ C → A ⊆ C.
Proof. intros; auto. Qed.

Fact equiv_refl X (A : X → Prop) : A ≃ A.
Proof. tauto. Qed.

Fact equiv_sym X (A B : X → Prop) : A ≃ B → B ≃ A.
Proof. tauto. Qed.

Fact equiv_trans X (A B C : X → Prop) : A ≃ B → B ≃ C → A ≃ C.
Proof. intros [] [];  split; intros; auto. Qed.

Fact equal_equiv X (A B : X → Prop) : A = B → A ≃ B.
Proof. intros []; auto. Qed.

#[local] Notation "A '∩' B" := (λ z, A z ∧ B z) (at level 50, format "A ∩ B", left associativity).
#[local] Notation "A '∪' B" := (λ z, A z ∨ B z) (at level 50, format "A ∪ B", left associativity).

(** λ ∧ ∨ ⊆ ≃ ∩ ∪ *)

#[local] Definition sg {X} := (@eq X).

Fact eq_sg X (x y : X) : x = y → sg x y.
Proof. trivial. Qed.

#[local] Hint Resolve eq_sg : core. 

Fact sg_inc X (A : X → Prop) x : A x → sg x ⊆ A.
Proof. intros ? ? []; trivial. Qed.

Fact inc_sg X (A : X → Prop) x : sg x ⊆ A → A x.
Proof. intros H; apply H; red; auto. Qed.

Fact sg_inc_iff X (A : X → Prop) x : A x ↔ sg x ⊆ A.
Proof. split; [ apply sg_inc | apply inc_sg ]. Qed.

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

  Variables (cl : (M → Prop) → (M → Prop))
            (cl_increase   : ∀ A, A ⊆ cl A)
            (cl_monotone   : ∀ A B, A ⊆ B → cl A ⊆ cl B)
            (cl_idempotent : ∀ A, cl (cl A) ⊆ cl A).

  Fact cl_prop A B : A ⊆ cl B ↔ cl A ⊆ cl B.
  Proof using cl_increase cl_monotone cl_idempotent. split; eauto. Qed.

  Definition cl_inc A B := proj1 (cl_prop A B).
  Definition inc_cl A B := proj2 (cl_prop A B). 

  Fact cl_eq1 A B : A ≃ B → cl A ≃ cl B.
  Proof using cl_monotone. intros []; split; now apply cl_monotone. Qed.

  Hint Resolve cl_inc cl_eq1 : core.

  Abbreviation closed := (λ x, cl x ⊆ x).

  Fact cl_closed A B : closed B → A ⊆ B → cl A ⊆ B.
  Proof using cl_idempotent cl_increase cl_monotone. eauto. Qed.
  
  Fact closed_eq1 A : closed A → cl A ≃ A.
  Proof using cl_increase. split; auto. Qed.

  Fact cap_closed A B : closed A → closed B → closed (A ∩ B).
  Proof using cl_monotone.
    intros HA HB x Hx; split; [ apply HA | apply HB ]; revert Hx; apply cl_monotone; tauto.
  Qed.

  Hint Resolve cap_closed closed_eq1 : core.

  (* this is a relational/non-deterministic monoid *)

  Variable comp : M → M → M → Prop.

  (* Composition lifted to predicates *)

  Inductive composes (A B : M → Prop) : M → Prop :=
    | In_composes a b c : A a → B b → comp a b c → (A∘B) c
  where "A ∘ B" := (composes A B).

  Fact composes_monotone A A' B B' : A ⊆ A' → B ⊆ B' → A∘B ⊆ A'∘B'.
  Proof. intros ? ? _ [ ? ? ? ? ? H ]; apply In_composes with (3 := H); auto. Qed.

  Hint Resolve composes_monotone : core.

  Variable e : M.

  (* Stability is the important axiom in phase semantics *)

  Abbreviation cl_stability   := (∀ A B, cl A ∘ cl B ⊆ cl (A∘B)).
  Abbreviation cl_stability_l := (∀ A B, cl A ∘    B ⊆ cl (A∘B)).
  Abbreviation cl_stability_r := (∀ A B,    A ∘ cl B ⊆ cl (A∘B)).

  Fact cl_stable_imp_stable_l : cl_stability → cl_stability_l.
  Proof using cl_increase.
    intros H ? ? x Hx; apply H.
    revert x Hx; apply composes_monotone; auto.
  Qed.

  Fact cl_stable_imp_stable_r : cl_stability → cl_stability_r.
  Proof using cl_increase. 
    intros H ? ? x Hx; apply H.
    revert x Hx; apply composes_monotone; auto.
  Qed.

  Fact cl_stable_lr_imp_stable : cl_stability_l → cl_stability_r → cl_stability.
  Proof using cl_idempotent cl_monotone.
    intros H1 H2 A B x Hx; apply cl_idempotent.
    generalize (H1 _ _ _ Hx); apply cl_monotone, H2.
  Qed.

  Hint Resolve cl_stable_imp_stable_l cl_stable_imp_stable_r cl_stable_lr_imp_stable : core.

  Abbreviation cl_neutrality_1  := (∀ a, cl (sg e ∘ sg a) a).
  Abbreviation cl_neutrality_2  := (∀ a, sg e ∘ sg a ⊆ cl (sg a)).
  Abbreviation cl_commutativity := (∀ a b, sg a ∘ sg b ⊆ cl (sg b ∘ sg a)).
  Abbreviation cl_associativity := (∀ a b c, sg a ∘ (sg b ∘ sg c) ⊆ cl ((sg a ∘ sg b) ∘ sg c)).

  Hypothesis cl_commute : cl_commutativity.

  Hint Resolve sg_inc_iff : core.

  Fact composes_commute_1 A B : A∘B ⊆ cl (B∘A).
  Proof using cl_commute cl_monotone.
    intros _ [ a b c Ha Hb Hc ].
    apply cl_monotone with (sg b ∘ sg a).
    + now apply composes_monotone; apply sg_inc.
    + apply cl_commute; constructor 1 with (3 := Hc); auto.
  Qed.

  Hint Resolve composes_commute_1 : core.

  Fact composes_commute A B : cl (A∘B) ≃ cl (B∘A).
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    split; eauto.
  Qed. 

  Fact cl_stable_l_imp_r : cl_stability_l → cl_stability_r.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    intros Hl A B x Hx.
    apply cl_idempotent.
    apply cl_monotone with (cl B ∘ A).
    apply inc_trans with (cl ((cl B) ∘ A)); auto.
    + rewrite <- cl_prop.
      generalize (@composes_commute_1 B A); intros H.
      rewrite cl_prop in H; auto.
    + apply composes_commute_1; auto.
  Qed.

  Fact cl_stable_r_imp_l : cl_stability_r → cl_stability_l.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    intros Hl A B.
    generalize (@composes_commute_1 B A); intros H.
    rewrite cl_prop in H; auto.
    apply inc_trans with (B := cl (B ∘ cl A)),
          inc_trans with (2 := H); auto.
    rewrite <- cl_prop; apply Hl.
  Qed.

  Hint Resolve cl_stable_l_imp_r cl_stable_r_imp_l : core.

  Fact cl_stable_l_imp_stable : cl_stability_l → cl_stability.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone. auto. Qed.

  Fact cl_stable_r_imp_stable : cl_stability_r → cl_stability.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone. auto. Qed.

  Hypotheses (cl_stable : cl_stability).

  Fact cl_stable_l : cl_stability_l. 
  Proof using cl_increase cl_stable. now apply cl_stable_imp_stable_l. Qed.

  Fact cl_stable_r : cl_stability_r. 
  Proof using cl_increase cl_stable. now apply cl_stable_imp_stable_r. Qed.

  Hint Resolve cl_stable_l cl_stable_r : core.

  Hypothesis cl_neutral_1 : cl_neutrality_1.
  Hypothesis cl_neutral_2 : cl_neutrality_2.
  Hypothesis cl_associative : cl_associativity.

  Definition magicwand A B k := A ∘ sg k ⊆ B.
  Infix "⊸" := magicwand.

  Fact magicwand_spec A B C : B∘A ⊆ C ↔ A ⊆ B⊸C.
  Proof.
    split; intros H x Hx.
    + intros y Hy; apply H; revert Hy; apply composes_monotone; auto.
      now apply sg_inc.
    + destruct Hx as [ a b x Ha Hb Hx ].
      apply (H _ Hb).
      constructor 1 with a b; try red; auto.
  Qed.

  Definition magicwand_adj_1 A B C := proj1 (magicwand_spec A B C).
  Definition magicwand_adj_2 A B C := proj2 (magicwand_spec A B C).

  Fact magicwand_monotone A A' B B' : A ⊆ A' → B ⊆ B' → A'⊸B ⊆ A⊸B'.
  Proof.
    intros ? HB; apply magicwand_adj_1, inc_trans with (2 := HB).
    intros _ [? ? ? ? Ha Hc]; apply Ha, In_composes with (3 := Hc); auto.
  Qed.

  Hint Resolve magicwand_monotone : core.

  Fact cl_magicwand_1 X Y : cl (X⊸cl Y) ⊆ X⊸cl Y.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable. 
    apply magicwand_adj_1, inc_trans with (1 := cl_stable_r _ _ ).
    rewrite <- cl_prop; apply magicwand_spec; auto. 
  Qed.

  Fact cl_magicwand_2 X Y : cl X ⊸ Y ⊆ X⊸Y.
  Proof using cl_increase. apply magicwand_monotone; auto. Qed.

  Hint Resolve cl_magicwand_1 cl_magicwand_2 : core.

  Fact cl_magicwand_3 X Y : X ⊸ cl Y ⊆ cl X ⊸ cl Y.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable.
    apply magicwand_spec.
    apply inc_trans with (1 := cl_stable_l _ _); auto. 
    rewrite <- cl_prop; apply magicwand_spec; auto.
  Qed.

  Hint Resolve cl_magicwand_3 : core.

  Fact closed_magicwand X Y : closed Y → closed (X⊸Y).
  Proof using cl_idempotent cl_increase cl_monotone cl_stable.
    simpl; intro; apply inc_trans with (B := cl (X ⊸ cl Y)); eauto.
  Qed.

  Hint Resolve closed_magicwand : core.

  Fact magicwand_eq_1 X Y : X ⊸ cl Y ≃ cl X ⊸ cl Y.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable. split; auto. Qed.

  Fact magicwand_eq_2 X Y : cl (X ⊸ cl Y) ≃ X ⊸ cl Y.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable. split; auto. Qed.

  Fact magicwand_eq_3 X Y : cl (X ⊸ cl Y) ≃ cl X ⊸ cl Y.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable.
    split; auto.
  Qed.

  Hint Resolve magicwand_eq_1 magicwand_eq_2 magicwand_eq_3 : core.

  Fact cl_equiv_2 X Y : cl (cl X ∘ Y) ≃ cl (X ∘ Y).
  Proof using cl_idempotent cl_increase cl_monotone cl_stable.
    split.
    + rewrite <- cl_prop; auto.
    + apply cl_monotone, composes_monotone; auto.
  Qed.

  Fact cl_equiv_3 X Y : cl (X ∘ cl Y) ≃ cl (X ∘ Y).
  Proof using cl_idempotent cl_increase cl_monotone cl_stable.
    split.
    + rewrite <- cl_prop; auto.
    + apply cl_monotone, composes_monotone; auto.
  Qed.

  Fact cl_equiv_4 X Y : cl (cl X ∘ cl Y) ≃ cl (X ∘ Y).
  Proof using cl cl_commute cl_idempotent cl_increase cl_monotone cl_stable. 
    split.
    + rewrite <- cl_prop; auto.
    + apply cl_monotone, composes_monotone; auto.
  Qed.

  Hint Resolve cl_equiv_2 cl_equiv_3 cl_equiv_4 : core.

  Fact composes_associative_1 A B C : A ∘ (B ∘ C) ⊆ cl ((A ∘ B) ∘ C).
  Proof using cl_associative cl_monotone.
    intros _ [a _ k Ha [b c y Hb Hc Hy] Hk].
    generalize (@cl_associative a b c k); intros H.
    spec all in H.
    + constructor 1 with (3 := Hk); auto.
      constructor 1 with (3 := Hy); auto.
    + revert H; apply cl_monotone.
      repeat apply composes_monotone; apply sg_inc; auto.
  Qed.

  Hint Resolve composes_associative_1 composes_monotone : core.

  Fact composes_associative A B C : cl (A∘(B∘C)) ≃ cl ((A∘B)∘C).
  Proof using cl_associative cl_commute cl_idempotent cl_increase cl_monotone cl_stable.
    split; auto.
    1: rewrite <- cl_prop; auto.
    rewrite <- cl_prop; auto.
    apply inc_trans with (1 := @composes_commute_1 _ _).
    rewrite <- cl_prop.
    apply inc_trans with (B := C ∘ cl (A ∘ B)); auto.
    1: apply composes_monotone; auto.
    apply inc_trans with (B := C ∘ cl (B ∘ A)); auto.
    1: apply composes_monotone; auto; apply composes_commute. 
    apply inc_trans with (1 := @cl_stable_r _ _).
    rewrite <- cl_prop.
    apply inc_trans with (1 := @composes_associative_1 _ _ _).
    rewrite <- cl_prop.
    apply inc_trans with (1 := @composes_commute_1 _ _). 
    rewrite <- cl_prop.
    apply inc_trans with (B := A ∘ cl (C ∘ B)); auto.
    1: apply composes_monotone; auto.
    apply inc_trans with (B := A ∘ cl (B ∘ C)); auto.
    apply composes_monotone; auto.
    apply composes_commute.
  Qed.

  Hint Resolve composes_associative : core.

  Fact composes_congruent_1 A B C : A ⊆ cl B → C ∘ A ⊆ cl (C ∘ B).
  Proof using cl_idempotent cl_increase cl_monotone cl_stable.
    intro.
    apply inc_trans with (B := cl (C ∘ cl B)); auto.
    + apply cl_prop, cl_monotone, composes_monotone; auto.
    + apply cl_equiv_3.
  Qed.

  Hint Resolve composes_congruent_1 : core.

  Fact composes_congruent A B C : cl A ≃ cl B → cl (C ∘ A) ≃ cl (C ∘ B).
  Proof using cl_idempotent cl_increase cl_monotone cl_stable. 
    intros [H1 H2]; split; rewrite <- cl_prop in H1, H2 |- *;
      apply inc_trans with (2 := @cl_stable_r _ _), composes_monotone; auto.
  Qed.

  Fact composes_assoc_special A A' B B' : cl((A∘A') ∘ (B∘B')) ≃ cl ((A∘B) ∘ (A'∘B')).
  Proof using cl_associative cl_commute cl_idempotent cl_increase cl_monotone cl_stable.
    do 2 apply equiv_sym, equiv_trans with (2 := composes_associative _ _ _).
    apply composes_congruent.
    apply equiv_sym, equiv_trans with (1 := composes_commute _ _).
    apply equiv_sym, equiv_trans with (2 := composes_associative _ _ _).
    apply composes_congruent, composes_commute.
  Qed.

  Definition composes_assoc_special_1 A A' B B' := proj1 (composes_assoc_special A A' B B').

  Fact composes_neutral_1 A : A ⊆ cl (sg e ∘ A).
  Proof using cl_monotone cl_neutral_1.
    intros a Ha.
    generalize (cl_neutral_1 a).
    apply cl_monotone, composes_monotone; auto.
    apply sg_inc; auto.
  Qed.

  Fact composes_neutral_2 A : sg e ∘ A ⊆ cl A.
  Proof using cl_monotone cl_neutral_2.
    intros _ [y a x [] Ha Hx].
    generalize (@cl_neutral_2 a x); intros H.
    spec all in H.
    constructor 1 with e a; try red; auto.
    revert H; apply cl_monotone, sg_inc; auto.
  Qed.

  Hint Resolve composes_neutral_1 composes_neutral_2 : core.

  Fact composes_neutral A : cl (sg e ∘ A) ≃ cl A.
  Proof using cl_idempotent cl_increase cl_monotone cl_neutral_1 cl_neutral_2.
    split; rewrite <- cl_prop; auto.
  Qed.

  Notation "x 'lub' y" := (cl (x ∪ y)).

  Fact lub_out A B C : closed C → A ⊆ C → B ⊆ C → A lub B ⊆ C.
  Proof using cl_increase cl_monotone. 
    simpl.
    intros H1 H2 H3.
    apply inc_trans with (2 := H1), cl_monotone.
    intros ? []; auto.
  Qed.

  Fact closed_lub A B : closed (A lub B).
  Proof using cl_idempotent.
    exact (cl_idempotent _).
  Qed.

  Fact lub_in_l A B : A ⊆ A lub B.
  Proof using cl_increase. eauto. Qed.

  Fact lub_in_r A B : B ⊆ A lub B.
  Proof using cl_increase. eauto. Qed.

  Notation "x ⊛ y " := (cl (x ∘ y)).

  Fact closed_times A B : closed (A⊛B).
  Proof using cl_idempotent. simpl; eauto. Qed.

  Fact times_monotone A A' B B' : A ⊆ A' → B ⊆ B' → A⊛B ⊆ A'⊛B'.
  Proof using cl_monotone. intros ? ?; simpl; apply cl_monotone, composes_monotone; auto. Qed.

  Abbreviation top := (λ _ : M, True).
  Abbreviation bot := (cl (λ _, False)).
  Abbreviation unit := (cl (sg e)). 

  Fact closed_top : closed top.
  Proof. simpl; intros; auto. Qed.

  Fact closed_bot : closed bot.
  Proof using cl_idempotent. simpl; apply cl_idempotent. Qed.

  Fact closed_unit : closed unit.
  Proof using cl_idempotent. simpl; apply cl_idempotent. Qed.

  Fact top_greatest A : A ⊆ top.
  Proof. simpl; tauto. Qed.

  Hint Resolve closed_top : core.

  Fact bot_least A : closed A → bot ⊆ A.
  Proof using cl_monotone.
    intro H; apply inc_trans with (2 := H), cl_monotone; tauto.
  Qed.

  Fact unit_neutral_1 A : closed A → unit ⊛ A ⊆ A.
  Proof using cl_idempotent cl_increase cl_monotone cl_neutral_2 cl_stable. 
    intros H; apply inc_trans with (2 := H).
    rewrite <- cl_prop.
    apply inc_trans with (1 := @cl_stable_l _ _).
    rewrite <- cl_prop.
    apply composes_neutral_2.
  Qed.

  Fact unit_neutral_2 A : A ⊆ unit ⊛ A.
  Proof using cl_increase cl_monotone cl_neutral_1.
    intros a Ha; simpl.
    generalize (composes_neutral_1 _ _ Ha).
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Fact unit_neutral A : closed A → unit ⊛ A ≃ A.
  Proof using cl_idempotent cl_increase cl_monotone cl_neutral_1 cl_neutral_2 cl_stable. 
    intros H; split. 
    + revert H; apply unit_neutral_1.
    + apply unit_neutral_2.
  Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

  Fact times_commute_1 A B : A⊛B ⊆ B⊛A.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    simpl; apply cl_inc, composes_commute_1.
  Qed.

  Hint Resolve unit_neutral times_commute_1 : core.

  Fact times_commute A B : A⊛B ≃ B⊛A.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone.
    split; auto.
  Qed.

  Fact unit_neutral' A : closed A → A ⊛ unit ≃ A.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_neutral_1 cl_neutral_2 cl_stable.
    intros ?; apply equiv_trans with (1 := times_commute _ _); auto.
  Qed.

  Fact times_associative A B C : (A⊛B)⊛C ≃ A⊛(B⊛C).
  Proof using cl_associative cl_commute cl_idempotent cl_increase cl_monotone cl_stable.
    apply equiv_sym, equiv_trans with (1 := cl_equiv_3 _ _ ).
    apply equiv_sym, equiv_trans with (1 := cl_equiv_2 _ _ ).
    apply equiv_sym, composes_associative.
  Qed.

  Fact times_associative_1 A B C : (A⊛B)⊛C ⊆ A⊛(B⊛C).
  Proof using cl_associative cl_commute cl_idempotent cl_increase cl_monotone cl_stable.
    apply times_associative.
  Qed.

  Fact times_associative_2 A B C : A⊛(B⊛C) ⊆ (A⊛B)⊛C.
  Proof using cl_associative cl_idempotent cl_increase cl_monotone cl_stable.
    rewrite <- cl_prop.
    apply inc_trans with (1 := cl_stable_r _ _).
    rewrite <- cl_prop.
    apply inc_trans with (1 := composes_associative_1 _ _ _).
    apply times_monotone; auto.
  Qed.

  Hint Resolve times_associative_1 times_associative_2 : core.

  Fact times_congruence A A' B B' : A ≃ A' → B ≃ B' → A⊛B ≃ A'⊛B'.
  Proof using cl_monotone. 
    intros [] []; split; apply times_monotone; auto.
  Qed.

  Fact adjunction_1 A B C : closed C → B ⊛ A ⊆ C → A ⊆ B ⊸ C.
  Proof using cl_increase.
    intros ? H; apply magicwand_adj_1, inc_trans with (2 := H); auto.
  Qed.

  Fact adjunction_2 A B C : closed C → A ⊆ B ⊸ C → B ⊛ A ⊆ C.
  Proof using cl_increase cl_monotone.
    intros H ?; apply inc_trans with (2 := H), cl_monotone, magicwand_adj_2; auto.
  Qed.

  Hint Resolve times_congruence adjunction_1 (* adjunction_2 *) : core.

  Fact adjunction A B C : closed C → B ⊛ A ⊆ C ↔ A ⊆ B ⊸ C.
  Proof using cl_increase cl_monotone.
    split; [ apply adjunction_1 | apply  adjunction_2 ]; auto.
  Qed.

  Fact times_bot_distrib_l A : A ⊛ bot ⊆ bot.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable.
    rewrite <- cl_prop.
    apply inc_trans with (1 := cl_stable_r _ _).
    rewrite <- cl_prop.
    now intros ? [].
  Qed.

  Fact times_bot_distrib_r A : bot ⊛ A ⊆ bot.
  Proof using cl_idempotent cl_increase cl_monotone cl_stable.
    rewrite <- cl_prop.
    apply inc_trans with (1 := cl_stable_l _ _).
    rewrite <- cl_prop.
    now intros ? [].
  Qed.

  Hint Immediate times_bot_distrib_l times_bot_distrib_r : core.

  Fact times_lub_distrib_l A B C : C ⊛ (A lub B) ⊆ (C ⊛ A) lub (C ⊛ B).
  Proof using cl_idempotent cl_increase cl_monotone cl_stable.
    apply adjunction, lub_out; auto;
    apply adjunction; auto.
  Qed.

  Fact times_lub_distrib_r A B C : (A lub B) ⊛ C ⊆ (A ⊛ C) lub (B ⊛ C).
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_stable. 
    apply inc_trans with (1 := @times_commute_1 _ _),
          inc_trans with (1 := @times_lub_distrib_l _ _ _); auto.
    apply lub_out; auto.
  Qed.

  (** Remarks explaining why the additive conjuction can be interpreted
      as the & of ILL *)

  Hypothesis cl_weak : ∀x, cl (sg e) x.
  Hypothesis cl_cntr : ∀x, cl (sg x ∘ sg x) x.

  Fact any_inc_unit A : A ⊆ cl (sg e).
  Proof using cl_weak. intro; auto. Qed.

  Hint Resolve any_inc_unit : core.
  
  Fact times_inc_cap A B : closed A → closed B → A ⊛ B ⊆ A ∩ B.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_neutral_1 cl_neutral_2 cl_stable cl_weak.
    intros HA HB x Hx; split; revert x Hx; apply cl_closed; auto.
    + apply inc_trans with (A ∘ cl (sg e)).
      * apply composes_monotone; auto.
      * now apply inc_trans with (1 := cl_increase _), unit_neutral'.
    + apply inc_trans with (cl (sg e) ∘ B).
      * apply composes_monotone; auto.
      * now apply inc_trans with (1 := cl_increase _), unit_neutral.
  Qed.

  Fact cap_inc_times A B : A ∩ B ⊆ A ⊛ B.
  Proof using cl_monotone cl_cntr.
    intros x [HA HB].
    generalize (cl_cntr x).
    apply cl_monotone.
    intros _ [? ? c <- <- ]; now exists x x.
  Qed.
  
  Hint Resolve times_inc_cap cap_inc_times : core.

  Fact times_equiv_cap A B : closed A → closed B → A ⊛ B ≃ A ∩ B.
  Proof using cl_commute cl_idempotent cl_increase cl_monotone cl_neutral_1 cl_neutral_2 cl_stable cl_weak cl_cntr.
    split; auto.
  Qed.
 
End Relational_phase_semantics.

Section Rel_sem_BI.

  Variables (M : Type) (cl : (M → Prop) → (M → Prop)).

  Abbreviation closed := (λ x, cl x ⊆ x).

  Hypothesis cl_increase   : ∀A, A ⊆ cl A.
  Hypothesis cl_monotone   : ∀ A B, A ⊆ B → cl A ⊆ cl B.
  Hypothesis cl_idempotent : ∀ A, cl (cl A) ⊆ cl A.

  Variables (comp_m : M → M → M → Prop) (unit_m : M)
            (comp_a : M → M → M → Prop) (unit_a : M).

  Infix "∘" := (composes _ comp_m).
  Infix "⊸" := (magicwand _ comp_m).
  Abbreviation eₘ := unit_m.

  Hypothesis cl_stable_m : ∀ A B, cl A ∘ cl B ⊆ cl (A ∘ B).
  Hypothesis cl_neutral_1_m : ∀x, cl (sg eₘ ∘ sg x) x.
  Hypothesis cl_neutral_2_m : ∀x, sg eₘ ∘ sg x ⊆ cl (sg x).
  Hypothesis cl_commute_m : ∀ x y, sg x ∘ sg y ⊆ cl (sg y ∘ sg x).
  Hypothesis cl_associative_m : ∀ x y z, sg x ∘ (sg y ∘ sg z) ⊆ cl ((sg x ∘ sg y) ∘ sg z).

  Infix "⨣" := (composes _ comp_a).
  Infix "-⨣" := (magicwand _ comp_a).
  Abbreviation eₐ := unit_a.

  Hypothesis cl_stable_a : ∀ A B, cl A ⨣ cl B ⊆ cl (A ⨣ B).
  Hypothesis cl_neutral_1_a : ∀x, cl (sg eₐ ⨣ sg x) x.
  Hypothesis cl_neutral_2_a : ∀x, sg eₐ ⨣ sg x ⊆ cl (sg x).
  Hypothesis cl_commute_a : ∀ x y, sg x ⨣ sg y ⊆ cl (sg y ⨣ sg x).
  Hypothesis cl_associative_a : ∀ x y z, sg x ⨣ (sg y ⨣ sg z) ⊆ cl ((sg x ⨣ sg y) ⨣ sg z).

  Notation "x 'lub' y" := (cl (x ∪ y)).
  Abbreviation bot := (cl (λ _, False)).

  Hypothesis cl_weak : ∀x, cl (sg eₐ) x.
  Hypothesis cl_cntr : ∀x, cl (sg x ⨣ sg x) x.

  Variables (µ : BI_conn → bool) (prop : Set).

  Reserved Notation "⟦ A ⟧ᶠ" (at level 0, format "⟦ A ⟧ᶠ").
  Reserved Notation "⟦ Θ ⟧ᵇ" (at level 0, format "⟦ Θ ⟧ᵇ").

  Section sem_BI_form.

    Variables (φ : prop → M → Prop) (Hφ: ∀v, closed (φ v)).

    Fixpoint sem_BI_form (A : BI_form µ prop) { struct A } : M → Prop :=
      match A with
      | BI_form_var _ v            => φ v
      | BI_form_unit _ _ BI_mult _ => cl (sg eₘ)
      | BI_form_unit _ _ BI_addi _ => cl (sg eₐ)
      | BI_form_conj BI_mult _ A B => cl (⟦A⟧ᶠ ∘ ⟦B⟧ᶠ)
      | BI_form_conj BI_addi _ A B => cl (⟦A⟧ᶠ ⨣ ⟦B⟧ᶠ)
      | BI_form_impl BI_mult _ A B => ⟦A⟧ᶠ ⊸ ⟦B⟧ᶠ
      | BI_form_impl BI_addi _ A B => ⟦A⟧ᶠ -⨣ ⟦B⟧ᶠ
      | BI_form_bot  _ _ _         => bot
      | BI_form_disj _ A B         => ⟦A⟧ᶠ lub ⟦B⟧ᶠ
      end
    where "⟦ A ⟧ᶠ" := (sem_BI_form A).

    Fact sem_BI_form_closed A : closed ⟦A⟧ᶠ.
    Proof using cl_idempotent cl_increase cl_monotone cl_stable_a cl_stable_m cl_weak Hφ.
      induction A as [ | [] | [] | [] | | ]; simpl; eauto using closed_magicwand.
    Qed.

  End sem_BI_form.

  Section sem_BI_bunch.

    Variables (φ : BI_form µ prop → M → Prop) (Hφ : ∀A, closed (φ A)).

    Fixpoint sem_BI_bunch Θ : M → Prop :=
      match Θ with
      | ⟨A⟩ => φ A
      | øₘ => cl (sg eₘ)
      | øₐ => cl (sg eₐ)
      | Γ ⊛ₘ Δ => cl (⟦Γ⟧ᵇ ∘ ⟦Δ⟧ᵇ)
      | Γ ⊛ₐ Δ => cl (⟦Γ⟧ᵇ ⨣ ⟦Δ⟧ᵇ)
      end
    where "⟦ Θ ⟧ᵇ" := (sem_BI_bunch Θ).

    Fact sem_BI_bunch_closed Θ : closed ⟦Θ⟧ᵇ.
    Proof using cl_idempotent cl_monotone Hφ.
      clear cl_weak.
      induction Θ as [ | [] | [] ]; simpl; eauto.
    Qed.

    Hint Resolve sem_BI_bunch_closed : core.
    Hint Resolve equiv_refl equiv_sym equiv_trans unit_neutral : core.

    Fact sem_BI_bunch_soundness Γ Δ : Γ ≡ Δ → ⟦Γ⟧ᵇ ≃ ⟦Δ⟧ᵇ.
    Proof using cl_associative_a cl_associative_m 
                cl_commute_a cl_commute_m 
                cl_idempotent cl_increase cl_monotone
                cl_neutral_1_a cl_neutral_1_m 
                cl_neutral_2_a cl_neutral_2_m
                cl_stable_a cl_stable_m
                Hφ.
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

  End sem_BI_bunch.

  Section sem_ctx.

    Fact sem_BI_ctx_monotone φ Σ Γ Δ : sem_BI_bunch φ Γ ⊆ sem_BI_bunch φ Δ → sem_BI_bunch φ Σ[Γ] ⊆ sem_BI_bunch φ Σ[Δ].
    Proof using cl_monotone.
      intros H.
      induction Σ as [ | [] [] ].
      1: simpl; auto.
      all: simpl; apply times_monotone; auto.
    Qed.

    Fact sem_BI_ctx_bot φ Σ Δ : sem_BI_bunch φ Δ ⊆ bot → sem_BI_bunch φ Σ[Δ] ⊆ bot.
    Proof using  cl_commute_a cl_idempotent cl_increase cl_monotone cl_stable_a cl_stable_m.
      intros Hdelta.
      induction Σ as [ | [] [] G D IH ]; simpl; auto.
      1,2: apply inc_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ (inc_refl _ _) IH); apply times_bot_distrib_l; auto.
      1,2: apply inc_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ IH (inc_refl _ _)); apply times_bot_distrib_r; auto.
    Qed.

    Fact sem_BI_ctx_lub φ Σ A B (h : µ BI_disj = true) : sem_BI_bunch (sem_BI_form φ) Σ[⟨BI_form_disj h A B⟩]
                                                       ⊆ sem_BI_bunch (sem_BI_form φ) Σ[⟨A⟩] lub sem_BI_bunch (sem_BI_form φ) Σ[⟨B⟩].
    Proof using cl_commute_a cl_commute_m cl_idempotent cl_increase cl_monotone cl_stable_a cl_stable_m.
      induction Σ as [ | [] [] G D IH ]; simpl; auto.
      1,2: apply inc_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ (inc_refl _ _) IH); eapply inc_trans; [ apply times_lub_distrib_l | ]; auto.
      1,2: apply inc_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ IH (inc_refl _ _)); eapply inc_trans; [ apply times_lub_distrib_r | ]; auto.
    Qed. 

  End sem_ctx.

  Variables (cut : BI_cut) (φ : prop → M → Prop) (Hφ : ∀v, closed (φ v)).

  Hint Resolve sem_BI_form_closed sem_BI_ctx_monotone sem_BI_bunch_soundness : core.

  Theorem LBI_soundness Γ A : Γ L⊦[cut] A → sem_BI_bunch (sem_BI_form φ) Γ ⊆ sem_BI_form φ A.
  Proof using cl_idempotent cl_increase cl_monotone 
              cl_neutral_1_a cl_neutral_1_m 
              cl_neutral_2_a cl_neutral_2_m
              cl_associative_a cl_associative_m
              cl_commute_a cl_commute_m 
              cl_stable_a cl_stable_m
              cl_cntr cl_weak
              Hφ.
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
    + apply inc_trans with (2 := IH2), sem_BI_ctx_monotone; now simpl.
    + apply inc_trans with (2 := IH), sem_BI_bunch_soundness; auto.
    + apply inc_trans with (2 := IH), sem_BI_ctx_monotone; simpl.
      intros ? ?; apply cl_weak.
    + apply inc_trans with (2 := IH), sem_BI_ctx_monotone; simpl.
      intros x Hx.
      generalize (cl_cntr x).
      apply times_monotone; auto.
      all: now intros ? <-.
    + apply inc_trans with (2 := IH), sem_BI_ctx_monotone; now simpl.
    + apply inc_trans with (2 := IH), sem_BI_ctx_monotone; now simpl.
    + now simpl.
    + now simpl.
    + apply inc_trans with (2 := IH), sem_BI_ctx_monotone; now simpl.
    + apply inc_trans with (2 := IH), sem_BI_ctx_monotone; now simpl.
    + simpl; apply times_monotone; auto.
    + simpl; apply times_monotone; auto.
    + apply inc_trans with (2 := IH2), sem_BI_ctx_monotone; simpl.
      apply cl_closed; auto.
      apply magicwand_spec, magicwand_monotone; auto.
    + apply inc_trans with (2 := IH2), sem_BI_ctx_monotone; simpl.
      apply cl_closed; auto.
      apply magicwand_spec, magicwand_monotone; auto.
    + apply magicwand_spec, inc_trans with (2 := IH); simpl; auto.
    + apply magicwand_spec, inc_trans with (2 := IH); simpl; auto.
    + eapply inc_trans; [ apply sem_BI_ctx_bot | apply bot_least ]; auto.
    + eapply inc_trans; [ apply sem_BI_ctx_lub | ].
      apply lub_out; auto.
    + simpl; apply inc_trans with (1 := IH), lub_in_l; auto.
    + simpl; apply inc_trans with (1 := IH), lub_in_r; auto.
  Qed.

End Rel_sem_BI.

Section LBI_cut_elim.

  Variables (µ : BI_conn → bool) (prop : Set).

  (* We consider bunches as a monoidal model for BI *)
  Let M := BI_bunch µ prop.

  Implicit Types (Γ : M) (X Y : M → Prop).

  (** The key construction of the closure operator:
         Γ is in the closure of X if 
           any context (Σ[_],A) that validates all the members of X 
           also validates Γ

      The validation relation need to be closed
      under logical rules but here we simply choose
      cut free provability L⊦[BI_cut_free]

      This generalizes the MacNeille closure over
      arbitrary contexts. Initial ideas in DLW's PhD thesis *)

  Let cl X Γ := ∀ Σ A, (∀Δ, X Δ → Σ[Δ] L⊦[BI_cut_free] A)
                                → Σ[Γ] L⊦[BI_cut_free] A.

  Local Fact cl_increase X : X ⊆ cl X.
  Proof. intros Γ HΓ Σ A H; now apply H. Qed.

  Local Fact cl_monotone X Y : X ⊆ Y → cl X ⊆ cl Y.
  Proof. intros HXY Γ HΓ Σ A H; apply HΓ; intros ? ?%HXY; auto. Qed.

  Local Fact cl_idempotent X : cl (cl X) ⊆ cl X.
  Proof. intros Γ HΓ Σ A H; apply HΓ; intros D HD; apply HD; auto. Qed.
  
  Hint Resolve cl_monotone cl_increase cl_idempotent : core.

  (** The relational bi-monoidal structure *)
  
  Let comp k (Γ Δ Θ : M) := Γ ⊛[k] Δ ≡ Θ.
  
  Notation "X '⊚[' k ']' Y" := (composes _ (comp k) X Y) (at level 50, no associativity, format "X  ⊚[ k ]  Y").
  Notation "X '-⊚[' k ']' Y" := (magicwand _ (comp k) X Y) (at level 51, right associativity, format "X  -⊚[ k ]  Y").
  Let unit k : M := ø[k].

  Infix "∘" := (composes _ (comp BI_mult)).
  Infix "⊸" := (magicwand _ (comp BI_mult)).
  Abbreviation eₘ := ø[BI_mult].

  Infix "⨣" := (composes _ (comp BI_addi)).
  Infix "-⨣" := (magicwand _ (comp BI_addi)).
  Abbreviation eₐ := ø[BI_addi].

  Hint Constructors BI_bunch_equiv composes : core.

  Local Fact cl_bequiv X Γ Δ : Γ ≡ Δ → cl X Γ → cl X Δ.
  Proof.
    intros H1 H2 Σ A H3.
    apply BI_bequiv_ctx with (Σ := Σ) in H1.
    apply LBI_equiv with (1 := H1); auto.
  Qed.

  (* Stability comes from the identities

       Σ[Γ ⊛ Δ] = Σ[_ ⊛ Δ][Γ]  and   Σ[Γ ⊛ Δ] = Σ[Γ ⊛ _][Δ]

     derivable from the composition of contexts *)

  Local Fact cl_stable_left k X Y : cl X ⊚[k] Y ⊆ cl (X ⊚[k] Y).
  Proof.
    intros _ [ Γ Δ Θ H1 H2 H3 ]; red in H1, H3.
    apply cl_bequiv with (1 := H3).
    intros Σ A HA.
    (* Σ[Γ⊛Δ]) = Σ[_⊛Δ][Γ] *)
    change (Σ[Γ ⊛[k] Δ])
    with    (Σ[(BI_ctx_comp BI_right k Δ (BI_ctx_hole _ _))[Γ]]).
    rewrite BI_ctx_compose_subst.
    apply H1.
    intros D HD.
    rewrite <- BI_ctx_compose_subst; simpl.
    apply HA; eexists D _; try red; eauto.
  Qed.

  Local Fact cl_stable_right k X Y : X ⊚[k] cl Y ⊆ cl (X ⊚[k] Y).
  Proof.
    intros _ [ Γ Δ Θ H1 H2 H3 ]; red in H2, H3.
    apply cl_bequiv with (1 := H3).
    intros Σ A HA.
    (* Σ[Γ⊛Δ]) = Σ[Γ⊛_][Δ] *)
    change (Σ[Γ ⊛[k] Δ])
    with    (Σ[(BI_ctx_comp BI_left k Γ (BI_ctx_hole _ _))[Δ]]).
    rewrite BI_ctx_compose_subst.
    apply H2.
    intros D HD.
    rewrite <- BI_ctx_compose_subst; simpl.
    apply HA; eexists _ D; try red; eauto.
  Qed.

  Local Hint Resolve cl_stable_left cl_stable_right : core.

  Local Fact cl_stable k X Y : cl X ⊚[k] cl Y ⊆ cl (X ⊚[k] Y). Proof. apply cl_stable_lr_imp_stable; eauto. Qed.

  Local Fact cl_stable_m X Y : cl X ∘ cl Y ⊆ cl (X ∘ Y). Proof. apply cl_stable. Qed.
  Local Fact cl_stable_a X Y : cl X ⨣ cl Y ⊆ cl (X ⨣ Y). Proof. apply cl_stable. Qed.

  Local Fact cl_neutral_1 k Γ : cl (sg ø[k] ⊚[k] sg Γ) Γ.
  Proof. intros Σ A H; apply H; exists (unit k) Γ; red; auto. Qed.

  Local Fact cl_neutral_1_m Γ : cl (sg eₘ ∘ sg Γ) Γ. Proof. apply cl_neutral_1. Qed.
  Local Fact cl_neutral_1_a Γ : cl (sg eₐ ⨣ sg Γ) Γ. Proof. apply cl_neutral_1. Qed.

  Hint Resolve BI_bequiv_ctx : core.
  
  Local Fact cl_sg Γ : cl (sg Γ) Γ.
  Proof. apply cl_increase; auto. Qed.
  
  Hint Resolve cl_sg : core.
  
  Local Fact cl_neutral_2 k Γ : sg ø[k] ⊚[k] sg Γ ⊆ cl (sg Γ).
  Proof. intros _ [ ? ? ? <- <- ?]; apply cl_bequiv with Γ; eauto. Qed.
  
  Local Fact cl_neutral_2_m Γ : sg eₘ ∘ sg Γ ⊆ cl (sg Γ). Proof. apply cl_neutral_2. Qed.
  Local Fact cl_neutral_2_a Γ : sg eₐ ⨣ sg Γ ⊆ cl (sg Γ). Proof. apply cl_neutral_2. Qed.

  Local Fact cl_commute k Γ Δ : sg Γ ⊚[k] sg Δ ⊆ cl (sg Δ ⊚[k] sg Γ).
  Proof.
    intros _ [ ? ? Θ <- <- H ].
    apply cl_bequiv with (Δ ⊛[k] Γ); eauto.
    apply cl_increase; eauto.
    exists Δ Γ; try red; auto.
  Qed.

  Local Fact cl_commute_m Γ Δ : sg Γ ∘ sg Δ ⊆ cl (sg Δ ∘ sg Γ).  Proof. apply cl_commute. Qed.
  Local Fact cl_commute_a Γ Δ : sg Γ ⨣ sg Δ ⊆ cl (sg Δ ⨣ sg Γ).  Proof. apply cl_commute. Qed.
  
  Local Fact cl_associative k Γ Δ Θ : sg Γ ⊚[k] (sg Δ ⊚[k] sg Θ) ⊆ cl ((sg Γ ⊚[k] sg Δ) ⊚[k] sg Θ).
  Proof.
    intros _ [ _ _ D <- [ _ _ C <- <- H1 ] H2 ].
    apply cl_bequiv with ((Γ ⊛[k] Δ) ⊛[k] Θ); auto.
    + red in H1, H2; eauto.
    + apply cl_increase.
      exists (Γ ⊛[k] Δ) Θ; try red; auto.
      exists Γ Δ; try red; auto.
  Qed.

  Local Fact cl_associative_m Γ Δ Θ : sg Γ ∘ (sg Δ ∘ sg Θ) ⊆ cl ((sg Γ ∘ sg Δ) ∘ sg Θ). Proof. apply cl_associative. Qed.
  Local Fact cl_associative_a Γ Δ Θ : sg Γ ⨣ (sg Δ ⨣ sg Θ) ⊆ cl ((sg Γ ⨣ sg Δ) ⨣ sg Θ). Proof. apply cl_associative. Qed.

  Local Fact cl_weak Γ : cl (sg eₐ) Γ.
  Proof. intros Σ A H; now apply LBI_weak, H. Qed.

  Local Fact cl_cntr Γ : cl (sg Γ ⨣ sg Γ) Γ.
  Proof.
    intros Σ A H.
    apply LBI_cntr, H.
    exists Γ Γ; red; auto.
  Qed.

  Let dwncl A Γ := Γ L⊦[BI_cut_free] A.
  Abbreviation φ  := (λ v, dwncl (BI_form_var µ v)).
  Let sem_form :=  sem_BI_form  _ cl (comp BI_mult) eₘ (comp BI_addi) eₐ µ _ φ.
  Let sem_bunch := sem_BI_bunch _ cl (comp BI_mult) eₘ (comp BI_addi) eₐ _ _ sem_form.

  Local Fact dwncl_closed A : cl (dwncl A) ⊆ dwncl A.
  Proof. intros ? H; apply (H (BI_ctx_hole _ _)); simpl; auto. Qed.

  Hint Resolve cl_idempotent cl_increase cl_monotone 
               cl_neutral_1_a cl_neutral_1_m 
               cl_neutral_2_a cl_neutral_2_m
               cl_associative_a cl_associative_m
               cl_commute_a cl_commute_m 
               cl_stable_a cl_stable_m
               cl_cntr cl_weak 
               dwncl_closed : core.

  Local Fact sem_form_is_closed A : cl (sem_form A) ⊆ sem_form A.
  Proof. apply sem_BI_form_closed; eauto. Qed.

  Hint Resolve sem_form_is_closed : core.

  Local Fact sem_bunch_is_closed Γ : cl (sem_bunch Γ) ⊆ sem_bunch Γ.
  Proof. apply sem_BI_bunch_closed; eauto. Qed.

  Hint Resolve sem_bunch_is_closed : core.

  Local Fact cl_unit_l k h : cl (sg ø[k]) ⟨BI_form_unit µ prop k h⟩.
  Proof. intros ? ? ?; auto using LBI_unit_l. Qed.

  Local Fact dwncl_unit_r k h : sg ø[k] ⊆ dwncl (BI_form_unit µ prop k h).
  Proof. apply sg_inc, LBI_unit_r. Qed. 

  Local Fact cl_conj_l k h A B : cl (sg (⟨A⟩ ⊛[k] ⟨B⟩)) ⟨BI_form_conj k h A B⟩.
  Proof. intros ? ? H; apply LBI_conj_l, H; auto. Qed.

  Local Fact dwncl_conj_r k h A B :  dwncl A ⊚[k] dwncl B ⊆ dwncl (BI_form_conj k h A B).
  Proof. intros ? [ ? ? ? ? ? H ]; red in H |- *; now apply LBI_equiv with (1 := H), LBI_conj_r. Qed.
 
  Local Fact cl_impl_l k h A B : (dwncl A -⊚[k] cl (sg ⟨B⟩)) ⟨BI_form_impl k h A B⟩.
  Proof.
    intros ? [ G D E H1 H2 H3 ]; red in H3.
    apply cl_bequiv with (1 := H3).
    rewrite <- H2.
    intros ? ? ?; apply LBI_impl_l; auto.
  Qed.

  Local Fact dwncl_impl_r k h A B : sg ⟨A⟩ -⊚[k] dwncl B ⊆ dwncl (BI_form_impl k h A B).
  Proof. intros G HG; apply LBI_impl_r, HG; exists ⟨A⟩ G; try red; auto. Qed.

  Local Fact cl_disj_l h A B : cl (sg ⟨A⟩ ∪ sg ⟨B⟩) ⟨BI_form_disj h A B⟩.
  Proof. intros ? ? H; apply LBI_disj_l; apply H; auto. Qed.

  Local Fact dwncl_disj_r1 h A B : dwncl A ⊆ dwncl (BI_form_disj h A B).
  Proof. intros ? ?; apply LBI_disj_r1; auto. Qed.

  Local Fact dwncl_disj_r2 h A B : dwncl B ⊆ dwncl (BI_form_disj h A B).
  Proof. intros ? ?; apply LBI_disj_r2; auto. Qed.


  (** This is the main insight of Okada's lemma: instead
      of proving sem_form A = dwncl A as in eg the Lindenbaum
      construction, we show a weaker form, and this weaker form
      does NOT require cut for its proof *)

  Hint Resolve composes_monotone : core.

  Local Lemma sem_form_Okada A :
      sem_form A ⟨A⟩
    ∧ sem_form A ⊆ dwncl A.
  Proof.
    induction A as [ 
                   | k Hµ 
                   | k Hµ A [IHA1 IHA2] B [IHB1 IHB2] 
                   | k Hµ A [IHA1 IHA2] B [IHB1 IHB2] 
                   | Hµ 
                   | Hµ A [IHA1 IHA2] B [IHB1 IHB2]  ]; simpl; split; trivial.
    + apply LBI_axiom.
    + destruct k; apply cl_unit_l.
    + destruct k; apply cl_closed; eauto using dwncl_unit_r.
    + destruct k; apply cl_monotone with (2 := cl_conj_l _ _ _ _), sg_inc; econstructor; eauto; red; auto.
    + destruct k; apply cl_closed; eauto; apply inc_trans with (2 := dwncl_conj_r _ _ _ _); eauto.
    + destruct k; apply magicwand_monotone with (3 := cl_impl_l _ _ _ _); auto; apply cl_closed; eauto; now apply sg_inc.
    + destruct k; apply inc_trans with (2 := dwncl_impl_r _ _ _ _); apply magicwand_monotone; auto; now apply sg_inc.
    + intros ? ? ?; apply LBI_bot_l.
    + apply cl_closed; now eauto.
    + apply cl_monotone with (2 := cl_disj_l _ _ _); intros ? [<- | <-]; auto.
    + apply cl_closed; eauto; intros ? []; [ apply dwncl_disj_r1 | apply dwncl_disj_r2 ]; auto.
  Qed.

  Local Corollary sem_bunch_Okada Γ : sem_bunch Γ Γ.
  Proof.
    induction Γ as [ | [] | [] ]; simpl; auto using cl_increase.
    + apply sem_form_Okada.
    + apply cl_increase; exists Γ1 Γ2; red; auto.
    + apply cl_increase; exists Γ1 Γ2; red; auto.
  Qed.

  Theorem LBI_cut_elim c Γ A : Γ L⊦[c] A → Γ L⊦[BI_cut_free] A.
  Proof.
    intros HA.
    cut (sem_bunch Γ ⊆ sem_form A).
    + intros H; apply sem_form_Okada, H, sem_bunch_Okada.
    + revert A HA; apply LBI_soundness; auto; eauto.
  Qed.

End LBI_cut_elim.

Check LBI_cut_elim. 

Section Rel_sem_ILL.

  (** Semantics for BI in the fragment w/o intuitionistic implication and w/o disjunction 
      identical to the phase semantics of the ILL fragment ⊛, ⊸, &, 1, ⊤, ⊥ 
      with the aim of showing that this fragment of BI, hence all its sub-fragments,
      are decidable because of the embedding into ILL *)

  Variables (M : Type) (cl : (M → Prop) → (M → Prop)).

  Abbreviation closed := (λ x, cl x ⊆ x).

  Hypothesis cl_increase   : ∀A, A ⊆ cl A.
  Hypothesis cl_monotone   : ∀ A B, A ⊆ B → cl A ⊆ cl B.
  Hypothesis cl_idempotent : ∀ A, cl (cl A) ⊆ cl A.

  Variables (comp : M → M → M → Prop) (unit : M).
  
  Infix "∘" := (composes _ comp).
  Infix "⊸" := (magicwand _ comp).
  Abbreviation e := unit.

  Hypothesis cl_stable : ∀ A B, cl A ∘ cl B ⊆ cl (A ∘ B).
  Hypothesis cl_neutral_1 : ∀x, cl (sg e ∘ sg x) x.
  Hypothesis cl_neutral_2 : ∀x, sg e ∘ sg x ⊆ cl (sg x).
  Hypothesis cl_commute : ∀ x y, sg x ∘ sg y ⊆ cl (sg y ∘ sg x).
  Hypothesis cl_associative : ∀ x y z, sg x ∘ (sg y ∘ sg z) ⊆ cl ((sg x ∘ sg y) ∘ sg z).

  Abbreviation top := (λ _, True).
  Abbreviation bot := (cl (λ _, False)).

  Variables (µ : BI_conn → bool) (prop : Set)
            (Hµ1 : µ (BI_impl BI_addi) = false)
            (Hµ2 : µ BI_disj = false).

  Reserved Notation "⟦ A ⟧ᶠ" (at level 0, format "⟦ A ⟧ᶠ").
  Reserved Notation "⟦ Θ ⟧ᵇ" (at level 0, format "⟦ Θ ⟧ᵇ").

  Hint Resolve cap_closed : core.

  Section sem_ILL_form.

    Variables (φ : prop → M → Prop) (Hφ: ∀v, closed (φ v)).

    Fixpoint sem_ILL_form (A : BI_form µ prop) { struct A } : M → Prop :=
      match A with
      | BI_form_var _ v            => φ v
      | BI_form_unit _ _ BI_mult _ => cl (sg e)
      | BI_form_unit _ _ BI_addi _ => top
      | BI_form_conj BI_mult _ A B => cl (⟦A⟧ᶠ ∘ ⟦B⟧ᶠ)
      | BI_form_conj BI_addi _ A B => ⟦A⟧ᶠ ∩ ⟦B⟧ᶠ
      | BI_form_impl BI_mult _ A B => ⟦A⟧ᶠ ⊸ ⟦B⟧ᶠ
      | BI_form_impl BI_addi _ A B => cl (sg e)
      | BI_form_bot  _ _ _         => bot
      | BI_form_disj _ A B         => cl (sg e)
      end
    where "⟦ A ⟧ᶠ" := (sem_ILL_form A).

    Fact sem_form_closed A : closed ⟦A⟧ᶠ.
    Proof using cl_idempotent cl_increase cl_monotone cl_stable Hφ.
      induction A as [ | [] | [] | [] | | ]; simpl; eauto using closed_magicwand.
    Qed.

  End sem_ILL_form.

  Section sem_ILL_bunch.

    Variables (φ : BI_form µ prop → M → Prop) (Hφ : ∀A, closed (φ A)).

    Fixpoint sem_ILL_bunch Θ : M → Prop :=
      match Θ with
      | ⟨A⟩ => φ A
      | øₘ => cl (sg e)
      | øₐ => top
      | Γ ⊛ₘ Δ => cl (⟦Γ⟧ᵇ ∘ ⟦Δ⟧ᵇ)
      | Γ ⊛ₐ Δ => ⟦Γ⟧ᵇ ∩ ⟦Δ⟧ᵇ
      end
    where "⟦ Θ ⟧ᵇ" := (sem_ILL_bunch Θ).

    Fact sem_ILL_bunch_closed Θ : closed ⟦Θ⟧ᵇ.
    Proof using cl_idempotent cl_monotone Hφ.
      induction Θ as [ | [] | [] ]; simpl; eauto.
    Qed.

    Hint Resolve sem_ILL_bunch_closed : core.
    Hint Resolve equiv_refl equiv_sym equiv_trans unit_neutral : core.

    Fact sem_ILL_bunch_soundness Γ Δ : Γ ≡ Δ → ⟦Γ⟧ᵇ ≃ ⟦Δ⟧ᵇ.
    Proof using cl_associative 
                cl_commute 
                cl_idempotent cl_increase cl_monotone
                cl_neutral_1 cl_neutral_2
                cl_stable
                Hφ.
      induction 1 as [ | | | [] | [] | [] | [] ? ? ? _ IH]; eauto.
      + apply unit_neutral; auto.
      + simpl; tauto.
      + apply times_commute; auto.
      + simpl; tauto.
      + apply times_associative; auto.
      + split; simpl; tauto.
      + apply times_congruence; auto.
      + destruct IH; split; intros ? []; split; auto.
    Qed.

  End sem_ILL_bunch.

  Section sem_ILL_ctx.

    Fact sem_ILL_ctx_monotone φ Σ Γ Δ : sem_ILL_bunch φ Γ ⊆ sem_ILL_bunch φ Δ → sem_ILL_bunch φ Σ[Γ] ⊆ sem_ILL_bunch φ Σ[Δ].
    Proof using cl_monotone.
      intros H.
      induction Σ as [ | [] [] ].
      1: simpl; auto.
      1,3: simpl; apply times_monotone; auto.
      all: simpl; intros ? []; split; auto.
    Qed.

    Fact sem_ILL_ctx_bot φ Σ Δ : sem_ILL_bunch φ Δ ⊆ bot → sem_ILL_bunch φ Σ[Δ] ⊆ bot.
    Proof using cl_idempotent cl_increase cl_monotone cl_stable.
      intros Hdelta.
      induction Σ as [ | [] [] G D IH ]; simpl; auto.
      + apply inc_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ (inc_refl _ _) IH); apply times_bot_distrib_l; auto.
      + now intros ? [_ ?%IH ].
      + apply inc_trans with (1 := times_monotone _ _ cl_monotone _ _ _ _ _ IH (inc_refl _ _)); apply times_bot_distrib_r; auto.
      + now intros ? [?%IH].
    Qed.

  End sem_ILL_ctx.

  Variables (cut : BI_cut) (φ : prop → M → Prop) (Hφ : ∀v, closed (φ v)).

  Hint Resolve sem_form_closed : core.

  Theorem LBI_ILL_sem_soundness Γ A : Γ L⊦[cut] A → sem_ILL_bunch (sem_ILL_form φ) Γ ⊆ sem_ILL_form φ A.
  Proof using cl_idempotent cl_increase cl_monotone
              cl_commute 
              cl_idempotent cl_increase cl_monotone
              cl_neutral_1 cl_neutral_2
              cl_associative
              cl_stable
              Hφ Hµ1 Hµ2.
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
    + apply inc_trans with (2 := IH2), sem_ILL_ctx_monotone; now simpl.
    + apply inc_trans with (2 := IH), sem_ILL_bunch_soundness; auto.
    + apply inc_trans with (2 := IH), sem_ILL_ctx_monotone; simpl; tauto.
    + apply inc_trans with (2 := IH), sem_ILL_ctx_monotone; simpl; tauto.
    + apply inc_trans with (2 := IH), sem_ILL_ctx_monotone; now simpl.
    + apply inc_trans with (2 := IH), sem_ILL_ctx_monotone; now simpl.
    + now simpl.
    + now simpl.
    + apply inc_trans with (2 := IH), sem_ILL_ctx_monotone; now simpl.
    + apply inc_trans with (2 := IH), sem_ILL_ctx_monotone; now simpl.
    + simpl; apply times_monotone; auto.
    + intros ? []; split; auto.
    + apply inc_trans with (2 := IH2), sem_ILL_ctx_monotone; simpl.
      apply cl_closed; auto.
      apply magicwand_spec, magicwand_monotone; auto.
    + match goal with E1: ?x = true, E2: ?x = false |- _ => now rewrite E1 in E2 end.
    + apply magicwand_spec, inc_trans with (2 := IH); simpl; auto.
    + match goal with E1: ?x = true, E2: ?x = false |- _ => now rewrite E1 in E2 end.
    + eapply inc_trans; [ apply sem_ILL_ctx_bot | apply bot_least ]; auto.
    + match goal with E1: ?x = true, E2: ?x = false |- _ => now rewrite E1 in E2 end.
    + match goal with E1: ?x = true, E2: ?x = false |- _ => now rewrite E1 in E2 end.
    + match goal with E1: ?x = true, E2: ?x = false |- _ => now rewrite E1 in E2 end.
  Qed.

End Rel_sem_ILL.

Check LBI_ILL_sem_soundness.

