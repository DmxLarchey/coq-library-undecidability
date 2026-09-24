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
  Require Import utils.

#[local] Reserved Notation "x ∘ y" (at level 50, no associativity, format "x ∘ y").
#[local] Reserved Notation "x ⊸ y" (at level 51, right associativity, format "x ⊸ y").
#[local] Reserved Notation "x ⊛ y "(at level 50, no associativity, format "x ⊛ y").
#[local] Reserved Notation "x 'lub' y" (at level 50, no associativity, format "x  lub  y").

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70, format "X  ⊆  Y", no associativity).
#[local] Notation "X ≃ Y" := (X ⊆ Y ∧ Y ⊆ X) (at level 70, format "X  ≃  Y", no associativity).
#[local] Notation "A ∩ B" := (λ z, A z ∧ B z) (at level 50, format "A ∩ B", left associativity).
#[local] Notation "A ∪ B" := (λ z, A z ∨ B z) (at level 50, format "A ∪ B", left associativity).

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

Definition sg {X} := (@eq X).

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
