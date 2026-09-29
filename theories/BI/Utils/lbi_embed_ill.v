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
  Require Import rel_phase_sem BI utils lbi ill.

Import BI_notations LBI_tactics ListNotations.

#[local] Reserved Notation "x ∘ y" (at level 50, no associativity, format "x ∘ y").
#[local] Reserved Notation "x ⊸ y" (at level 51, right associativity, format "x ⊸ y").
#[local] Reserved Notation "x ⊛ y "(at level 50, no associativity, format "x ⊛ y").

(*
#[local] Reserved Notation "x ⨣ y" (at level 50, no associativity, format "x ⨣ y").
#[local] Reserved Notation "x '-⨣' y" (at level 51, right associativity, format "x -⨣ y").

#[local] Reserved Notation "x 'lub' y" (at level 50, no associativity, format "x  lub  y").

*)

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70, format "X  ⊆  Y", no associativity).
#[local] Notation "X ≃ Y" := (X ⊆ Y ∧ Y ⊆ X) (at level 70, format "X  ≃  Y", no associativity).
#[local] Notation "A '∩' B" := (λ z, A z ∧ B z) (at level 50, format "A ∩ B", left associativity).
#[local] Notation "A '∪' B" := (λ z, A z ∨ B z) (at level 50, format "A ∪ B", left associativity).

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

  Variables (φ : prop → M → Prop) (Hφ : ∀v, closed (φ v)).

  Hint Resolve sem_form_closed : core.

  Theorem LBI_ILL_sem_soundness cut Γ A : Γ L⊦[cut] A → sem_ILL_bunch (sem_ILL_form φ) Γ ⊆ sem_ILL_form φ A.
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

  Fixpoint bi_to_ill (A : BI_form µ prop) { struct A } : ill_form prop :=
    match A with
    | BI_form_var _ v            => ill_var v 
    | BI_form_unit _ _ BI_mult _ => ill_cst _ ill_unit
    | BI_form_unit _ _ BI_addi _ => ill_cst _ ill_top
    | BI_form_bot  _ _ _         => ill_cst _ ill_bot
    | BI_form_conj BI_mult _ A B => ill_bin ill_times (bi_to_ill A) (bi_to_ill B)
    | BI_form_conj BI_addi _ A B => ill_bin ill_with (bi_to_ill A) (bi_to_ill B)
    | BI_form_impl BI_mult _ A B => ill_bin ill_limp (bi_to_ill A) (bi_to_ill B)
    | BI_form_impl BI_addi _ A B => ill_cst _ ill_unit (* arbitrary value: could be a match _ : False with end *)
    | BI_form_disj _ A B         => ill_cst _ ill_unit (* arbitrary value *)
    end.
    
  Fact bi_to_ill_sem A : sem_ILL_form φ A = sem_ill_form cl comp unit φ (bi_to_ill A).
  Proof using Hµ1 Hµ2.
    induction A as [ | [] | [] | [] | | ]; simpl; repeat f_equal; auto.
    now rewrite IHA1, IHA2.
  Qed.
  
End Rel_sem_ILL.

Arguments bi_to_ill {_ _}.
From Stdlib Require Import Permutation.

#[local] Infix "~ₚ" := (@Permutation _) (at level 70).

Section bi_to_ill_soundess.

  Let BI_fragment_decidable (c : BI_conn) : bool :=
    match c with
    | BI_impl BI_addi => false
    | BI_disj => false
    | _ => true
    end.

  Abbreviation µ := BI_fragment_decidable.
  Variables (prop : Set) (prop_dec : ∀ v w : prop, {v=w} + {v≠w}).
  
  Hint Resolve  cl_ill_cf_increase cl_ill_cf_monotone cl_ill_cf_idempotent
                cl_ill_cf_neutral_1 cl_ill_cf_neutral_2
                cl_ill_cf_associative cl_ill_cf_commute 
                cl_ill_cf_stable dwncl_ill_cf_closed : core.

  Theorem bi_to_ill_soundness cut (A : BI_form µ prop) : øₘ L⊦[cut] A → ill_cut_free nil (bi_to_ill A).
  Proof.
    intros H.
    apply ill_form_cut_free_completeness.
    rewrite <- bi_to_ill_sem; auto.
    apply LBI_ILL_sem_soundness with cut øₘ; eauto.
    simpl; intros ? ? G; now apply (G nil).
  Qed.
  
  Fixpoint ill_to_bi (A : ill_form prop) : BI_form µ prop :=
    match A with
    | ill_var v => BI_form_var _ v
    | ill_cst _ ill_unit => BI_form_unit _ _ BI_mult eq_refl
    | ill_cst _ ill_top  => BI_form_unit _ _ BI_addi eq_refl
    | ill_cst _ ill_bot  => BI_form_bot _ _ eq_refl
    | ill_bin ill_times A B => BI_form_conj BI_mult eq_refl (ill_to_bi A) (ill_to_bi B)
    | ill_bin ill_limp A B => BI_form_impl BI_mult eq_refl (ill_to_bi A) (ill_to_bi B)
    | ill_bin ill_with A B => BI_form_conj BI_addi eq_refl (ill_to_bi A) (ill_to_bi B)
    end.
    
  Fact ill_to_bi_to_ill A : ill_to_bi (bi_to_ill A) = A.
  Proof. induction A as [ | [] | [] | [] | | ]; simpl; f_equal; auto using eq_bool_pirr; easy. Qed.
  
  Let ill_list_to_bi Γ := BI_list_mult (map ill_to_bi Γ).
  
  Hint Constructors BI_bunch_equiv : core.

  Theorem ill_to_bi_soundness cut Γ A : ill_cut_free Γ A → ill_list_to_bi Γ L⊦[cut] ill_to_bi A.
  Proof.
    induction 1; simpl.
    + apply LBI_neut_r, LBI_axiom.
    + revert IHill_cut_free; apply LBI_equiv.
      now apply BI_list_mult_perm_bequiv, Permutation_map.
    + unfold ill_list_to_bi; simpl.
      rule LBI_unit_l at [lft].
      now apply LBI_neut_l.
    + apply LBI_unit_r.
    + unfold ill_list_to_bi; simpl.
      rule LBI_bot_l at [lft].
    + rule LBI_weak at [].
      apply LBI_unit_r.
    + unfold ill_list_to_bi in * |- *; simpl in *.
      rule LBI_conj_l at [lft].
      revert IHill_cut_free.
      apply LBI_equiv, BI_bequiv_sym, BI_bequiv_assoc.
    + unfold ill_list_to_bi.
      rewrite map_app.
      apply LBI_equiv with (1 := BI_bequiv_sym (BI_list_mult_app _ _)).
      now apply LBI_conj_r.
    + apply LBI_equiv with ((ill_list_to_bi Γ ⊛ₘ ⟨BI_form_impl BI_mult eq_refl (ill_to_bi A) (ill_to_bi B)⟩) ⊛ₘ ill_list_to_bi Δ).
      * unfold ill_list_to_bi; simpl.
        rewrite map_app.
        apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _).
        apply BI_bequiv_trans with (1 := BI_bequiv_sym (BI_bequiv_assoc _ _ _ _)).
        apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _).
        apply BI_bequiv_congr.
        apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _), BI_bequiv_sym.
        apply BI_list_mult_app.
      * rule LBI_impl_l at [lft].
    + apply LBI_impl_r; auto.
    + unfold ill_list_to_bi; simpl.
      rule LBI_conj_l at [lft].
      rule LBI_weak at [lft;rt].
      revert IHill_cut_free; apply LBI_equiv.
      unfold ill_list_to_bi; simpl.
      do 2 apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _), BI_bequiv_sym.
      apply BI_bequiv_congr.
      apply BI_bequiv_sym, BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _); auto.
    + unfold ill_list_to_bi; simpl.
      rule LBI_conj_l at [lft].
      rule LBI_weak at [lft;lft].
      revert IHill_cut_free; apply LBI_equiv.
      unfold ill_list_to_bi; simpl.
      do 2 apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _), BI_bequiv_sym.
      apply BI_bequiv_congr; auto.
    + rule LBI_cntr at []; now apply LBI_conj_r.
  Qed.

  Theorem bi_embed_ill cut (A : BI_form µ prop) : øₘ L⊦[cut] A ↔ ill_cut_free nil (bi_to_ill A).
  Proof.
    split.
    + apply bi_to_ill_soundness.
    + intros H%(ill_to_bi_soundness cut).
      now rewrite ill_to_bi_to_ill in H.
  Qed.

  Theorem BI_decidable_without_impl_disj cut (A : BI_form µ prop) : { øₘ L⊦[cut] A } + { ¬ øₘ L⊦[cut] A }.
  Proof using prop_dec.
    destruct (ill_cut_free_decidable prop_dec nil (bi_to_ill A)) 
      as [ H | H ]; 
      [ left | right; contradict H ];
      revert H; apply bi_embed_ill.
  Qed.

End bi_to_ill_soundess.

Check BI_decidable_without_impl_disj.
Print Assumptions BI_decidable_without_impl_disj.
