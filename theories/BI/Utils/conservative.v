(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Utf8.
From Undecidability.BI Require Import BI utils lbi cutelim.
Import BI_notations LBI_tactics.

#[local] Arguments BI_form_var {_ _}.
#[local] Arguments BI_form_unit {_ _}.
#[local] Arguments BI_form_bot {_ _}.

#[local] Arguments BI_ctx_hole {_ _}.

#[local] Reserved Notation "x '≡ᶠ' y" (at level 70, no associativity, format "x  ≡ᶠ  y").
#[local] Reserved Notation "x '≡ᵇ' y" (at level 70, no associativity, format "x  ≡ᵇ  y").
#[local] Reserved Notation "x '≡ᶜ' y" (at level 70, no associativity, format "x  ≡ᶜ  y").

Section convervative_wo_cut.

  Variable (prop : Set).

  Hint Resolve eq_bool_pirr : core.

  Section iso.

    Variables (µ µ' : BI_conn → bool).
    
    (** Structural identity for two BI formulas over different fragments as an inductive relation
        Notice that this relation is a partial bijection so working with Rocq functions instead
        of relations is going to generate lots of troubles related to dependent types and
        transport that are completely avoided when using a depoendent relation instead.
        
        This relation is a (dependent) equivalent relation, see below for refl, sym and trans *)

    Inductive BI_form_iso : BI_form µ prop → BI_form µ' prop → Prop :=
      | BI_fi_var v :                 BI_form_var v ≡ᶠ BI_form_var v
      | BI_fi_unit k h h' :           BI_form_unit k h  ≡ᶠ BI_form_unit k h'
      | BI_fi_conj k h h' A B A' B' : A ≡ᶠ A' → B ≡ᶠ B' → BI_form_conj k h A B ≡ᶠ BI_form_conj k h' A' B'
      | BI_fi_impl k h h' A B A' B' : A ≡ᶠ A' → B ≡ᶠ B' → BI_form_impl k h A B ≡ᶠ BI_form_impl k h' A' B'
      | BI_fi_bot h h'              : BI_form_bot h ≡ᶠ BI_form_bot h'
      | BI_fi_disj h h' A B A' B'   : A ≡ᶠ A' → B ≡ᶠ B' → BI_form_disj h A B ≡ᶠ BI_form_disj h' A' B' 
    where "A ≡ᶠ B" := (BI_form_iso A B).

    (* The critical tool is inversion lemma as usual *)
    Fact BI_fi_inv C D :
        C ≡ᶠ D  
      → match C with
        | BI_form_var v        => D = BI_form_var v
        | BI_form_unit k h     => ∃h', D = BI_form_unit k h'
        | BI_form_conj k h A B => ∃ A' B' h', D = BI_form_conj k h' A' B' ∧ A ≡ᶠ A' ∧ B ≡ᶠ B'
        | BI_form_impl k h A B => ∃ A' B' h', D = BI_form_impl k h' A' B' ∧ A ≡ᶠ A' ∧ B ≡ᶠ B'
        | BI_form_bot _h       => ∃h', D = BI_form_bot  h'
        | BI_form_disj h A B   => ∃ A' B' h', D = BI_form_disj h' A' B' ∧ A ≡ᶠ A' ∧ B ≡ᶠ B'
        end.
    Proof.
      intros [ | | k h h' A B A' B' | k h h' A B A' B' | h h' | h h' A B A' B' ]; eauto.
      all: exists A', B', h'; auto.
    Qed.

    (* Which gives us a functional relation *)
    Fact BI_fi_inj { A B B' } : A ≡ᶠ B → A ≡ᶠ B' → B = B'.
    Proof.
      induction 1 in B' |- *.
      + now intros ->%BI_fi_inv.
      + intros (? & ->)%BI_fi_inv; f_equal; auto.
      + intros (? & ? & ? & -> & ? & ?)%BI_fi_inv; f_equal; auto.
      + intros (? & ? & ? & -> & ? & ?)%BI_fi_inv; f_equal; auto.
      + intros (? & ->)%BI_fi_inv; f_equal; auto.
      + intros (? & ? & ? & -> & ? & ?)%BI_fi_inv; f_equal; auto.
    Qed.

    (** Now structural id. for bunches *)

    Inductive BI_bunch_iso : BI_bunch µ prop → BI_bunch µ' prop → Prop :=
      | BI_bi_atom A B         : A ≡ᶠ B → ⟨A⟩ ≡ᵇ ⟨B⟩
      | BI_bi_unit k           : ø[k] ≡ᵇ ø[k]
      | BI_bi_comp k Γ Δ Γ' Δ' : Γ ≡ᵇ Γ'→ Δ ≡ᵇ Δ' → Γ ⊛[k] Δ ≡ᵇ Γ' ⊛[k] Δ'
    where "Γ ≡ᵇ Δ" := (BI_bunch_iso Γ Δ).

    Fact BI_bi_inv Γ Δ :
        Γ ≡ᵇ Δ
      → match Γ with
        | ⟨A⟩          => ∃B, Δ = ⟨B⟩ ∧ A ≡ᶠ B
        | ø[k]         => Δ = ø[k]
        | Γ₁ ⊛[k] Γ₂  => ∃ Δ₁ Δ₂, Δ = Δ₁ ⊛[k] Δ₂ ∧ Γ₁ ≡ᵇ Δ₁ ∧ Γ₂ ≡ᵇ Δ₂
        end.
    Proof. intros []; eauto. Qed.

    (** Now structural id. for contexts, ie bunches with a single hole *)

    Inductive BI_ctx_iso : BI_ctx µ prop → BI_ctx µ' prop → Prop :=
      | BI_ci_hole               : BI_ctx_hole ≡ᶜ BI_ctx_hole
      | BI_ci_comp s k Γ Γ' Σ Σ' : Γ ≡ᵇ Γ' → Σ ≡ᶜ Σ' → BI_ctx_comp s k Γ Σ ≡ᶜ BI_ctx_comp s k Γ' Σ' 
    where "Σ ≡ᶜ Σ'" := (BI_ctx_iso Σ Σ').

    Fact BI_ci_bi_subst Σ Σ' Γ Γ' : Γ ≡ᵇ Γ' → Σ ≡ᶜ Σ' → Σ[Γ] ≡ᵇ Σ'[Γ'].
    Proof. induction 2 as [ | [] ]; simpl; eauto; constructor; auto. Qed.

    Hint Constructors BI_ctx_iso : core.

    Lemma BI_ctx_fill_inv Σ Γ Δ : Σ[Γ] ≡ᵇ Δ → ∃ Σ' Γ', Δ = Σ'[Γ'] ∧ Γ ≡ᵇ Γ' ∧ Σ ≡ᶜ Σ'.
    Proof.
      induction Σ as [ | [] k G Σ IH ] in Δ |- *; simpl.
      + exists BI_ctx_hole, Δ; auto.
      + intros (G' & D' & -> & ? & (S' & G'' & -> & [])%IH)%BI_bi_inv.
        exists (BI_ctx_comp BI_left k G' S'), G''; simpl; auto.
      + intros (G' & D' & -> & (S' & G'' & -> & [])%IH & ?)%BI_bi_inv.
        exists (BI_ctx_comp BI_right k D' S'), G''; simpl; auto.
    Qed.

  End iso.

  Arguments BI_fi_inj {_ _ _ _ _}.
  Arguments BI_form_iso {_ _}.
  Arguments BI_bunch_iso {_ _}.

  Infix "≡ᶠ" := BI_form_iso.
  Infix "≡ᵇ" := BI_bunch_iso.

  Hint Constructors BI_form_iso BI_bunch_iso : core.

  Local Remark BI_fi_refl µ (A : BI_form µ prop) : A ≡ᶠ A.
  Proof. induction A; eauto. Qed.

  Fact BI_fi_sym µ µ' (A : BI_form µ prop) (B : BI_form µ' _) : A ≡ᶠ B → B ≡ᶠ A.
  Proof. induction 1; eauto. Qed.

  Local Remark BI_fi_trans µ µ' µ'' (A : BI_form µ prop) (B : BI_form µ' _) (C : BI_form µ'' _) : A ≡ᶠ B → B ≡ᶠ C → A ≡ᶠ C.
  Proof.
    induction 1 in C |- *.
    + intros ->%BI_fi_inv; auto.
    + intros (? & ->)%BI_fi_inv; f_equal; auto.
    + intros (? & ? & ? & -> & [])%BI_fi_inv; eauto.
    + intros (? & ? & ? & -> & [])%BI_fi_inv; eauto.
    + intros (? & ->)%BI_fi_inv; auto.
    + intros (? & ? & ? & -> & [])%BI_fi_inv; eauto.
  Qed.

  Hint Resolve BI_fi_refl BI_fi_sym BI_fi_trans : core.

  Local Remark BI_bi_refl µ (Γ : BI_bunch µ prop) : Γ ≡ᵇ Γ.
  Proof. induction Γ; eauto. Qed.

  Fact BI_bi_sym µ µ' (Γ : BI_bunch µ prop) (Δ : BI_bunch µ' _) : Γ ≡ᵇ Δ → Δ ≡ᵇ Γ.
  Proof. induction 1; eauto. Qed.

  Local Remark BI_bi_trans µ µ' µ'' (Γ : BI_bunch µ prop) (Δ : BI_bunch µ' _) (Θ : BI_bunch µ'' _) : Γ ≡ᵇ Δ → Δ ≡ᵇ Θ → Γ ≡ᵇ Θ.
  Proof.
    induction 1 in Θ |- *.
    + intros (? & -> & ?)%BI_bi_inv; eauto.
    + intros ->%BI_bi_inv; auto.
    + intros (? & ? & -> & [])%BI_bi_inv; auto.
  Qed.
  
  Hint Resolve BI_bi_sym : core.

  Hint Constructors BI_bunch_equiv : core.

  (* Mutual induction needed because of the symmetry of the relation

     Remember than _ ≡ _ is bunch equivalence, not structural identity
     and it satisfies the comm. monoidal laws. *)
  Local Lemma BI_bi_bequiv_mutual µ µ' (Γ Γ' : BI_bunch µ prop) :
      Γ ≡ Γ'
    → (∀Δ : BI_bunch µ' prop, Γ ≡ᵇ Δ → ∃Δ', Δ ≡ Δ' ∧ Γ' ≡ᵇ Δ')
    ∧ (∀Δ': BI_bunch µ' prop, Γ' ≡ᵇ Δ' → ∃Δ, Δ ≡ Δ' ∧ Γ ≡ᵇ Δ).
  Proof.
    induction 1 as [ G | G G' E IH | G G' G'' E1 IH1 E2 IH2 | | | k Γ Δ Θ | k Γ Δ Θ H IH ].
    + split; eauto.
    + split; intros ? (D' & ? & ?)%IH; exists D'; auto.
    + split.
      * intros ? (D' & ? & (D'' & ? & ?)%IH2)%IH1; exists D''; eauto.
      * intros ? (D' & ? & (D'' & ? & ?)%IH1)%IH2; exists D''; eauto.
    + split.
      * intros ? (? & D & -> & ->%BI_bi_inv & ?)%BI_bi_inv; eauto.
      * intros D ?.
        exists (ø[k] ⊛[k] D); eauto.
    + split; intros ? (G & D & -> & ? & ?)%BI_bi_inv; exists (D ⊛[k] G); eauto.
    + split.
      * intros ? (? & T & -> & (G & D & -> & [])%BI_bi_inv & ?)%BI_bi_inv; eauto.
      * intros ? (G & ? & -> & ? & (D & T & -> & [])%BI_bi_inv)%BI_bi_inv; eauto.
    + split; intros ? (G & D & -> & ? & (T & [])%IH)%BI_bi_inv; exists (G ⊛[k] T); eauto.
  Qed.

  Corollary BI_bi_bequiv {µ µ'} {Γ Γ' : BI_bunch µ prop} {Δ : BI_bunch µ' prop} :
      Γ ≡ Γ' → Γ ≡ᵇ Δ → ∃Δ', Δ ≡ Δ' ∧ Γ' ≡ᵇ Δ'.
  Proof. intros H; apply BI_bi_bequiv_mutual with (1 := H). Qed.

  Hint Resolve BI_ci_bi_subst : core.

  Hint Constructors LBI_provable : core.

  Local Lemma LBI_cut_free_iso_conservative µ µ' (Γ : BI_bunch µ prop) A (Δ : BI_bunch µ' prop) B :
    Γ ≡ᵇ Δ → A ≡ᶠ B → Γ L⊦[BI_cut_free] A → Δ L⊦[BI_cut_free] B.
  Proof.
    intros H1 H2 H3; revert H3 Δ B H1 H2.
    induction 1; 
      try match goal with k : BI_kind |- _ => destruct k end.
    1: intros ? ? (? & -> & H)%BI_bi_inv <-%(BI_fi_inj H); auto.
    1: easy. (* cut is forbidden and THIS IS WHY THE PROOF WORKS !! *)
    1: match goal with H: _ ≡ _ |- _ => intros ? ? (? & [])%(BI_bi_bequiv (BI_bequiv_sym H)) ?; eauto end.
    1,2: intros ? ? (? & ? & -> & [])%BI_ctx_fill_inv ?; eauto.
    1,2: intros ? ? (? & ? & -> & (? & -> & (? & ->)%BI_fi_inv)%BI_bi_inv & ?)%BI_ctx_fill_inv ?; auto.
    1,2: intros ? ? ->%BI_bi_inv (h' & ->)%BI_fi_inv; auto.
    1,2: intros ? ? (? & ? & -> & (? & -> & (? & ? & ? & -> & [])%BI_fi_inv)%BI_bi_inv & ?)%BI_ctx_fill_inv ?; apply LBI_conj_l; auto.
    1,2: intros ? ? (? & ? & -> & [])%BI_bi_inv (? & ? & ? & -> & [])%BI_fi_inv; auto.
    1,2: intros ? ? (? & ? & -> & (? & ? & -> & ? & (? & -> & (? & ? & ? & -> & [])%BI_fi_inv)%BI_bi_inv)%BI_bi_inv & ?)%BI_ctx_fill_inv ?; apply LBI_impl_l; auto.
    1,2: intros ? ? ? (? & ? & ? & -> & [])%BI_fi_inv; auto.
    1: intros ? ? (? & ? & -> & (? & -> & (? & ->)%BI_fi_inv)%BI_bi_inv & ?)%BI_ctx_fill_inv ?; auto.
    1: intros ? ? (? & ? & -> & (? & -> & (? & ? & ? & -> & [])%BI_fi_inv)%BI_bi_inv & ?)%BI_ctx_fill_inv ?; apply LBI_disj_l; auto.
    1,2: intros ? ? ? (? & ? & ? & -> & [])%BI_fi_inv; auto.
  Qed.

  (** If Γ and Δ (resp. A and B) are structurally iso then
      Γ ⊦ A and Δ ⊦ B are equi-provable in the cut-free
      LBI calculus *)

  Corollary LBI_cut_free_conservative µ µ' (Γ : BI_bunch µ prop) A (Δ : BI_bunch µ' prop) B :
    Γ ≡ᵇ Δ → A ≡ᶠ B → Γ L⊦[BI_cut_free] A ↔ Δ L⊦[BI_cut_free] B.
  Proof. split; apply LBI_cut_free_iso_conservative; auto. Qed.

End convervative_wo_cut.

Arguments BI_form_iso {_ _ _}.
Arguments BI_bunch_iso {_ _ _}.

#[local] Infix "≡ᶠ" := BI_form_iso.
#[local] Infix "≡ᵇ" := BI_bunch_iso.

Check LBI_cut_free_conservative.

#[local] Arguments BI_form_map {_ _} _ {_ _}.
#[local] Arguments BI_bunch_map {_ _} _ {_ _}.

Section LBI_map_conservative.

  (** We derive conservativity results for the map functions 
      as straightforward corollaries because the two maps
      preserve structural identity !! *)

  Variables (µ µ' : BI_conn → bool) (Hµ : ∀c, µ c = true → µ' c = true) (prop : Set).

  (* Propositional variables are left unmodified, as requested by the definition of BI_form_iso *)

  Let fmap := BI_form_map Hµ (λ v : prop, v).
  Let bmap := BI_bunch_map Hµ (λ v : prop, v).

  Hint Constructors BI_form_iso BI_bunch_iso : core.

  Local Fact fmap_iso A : A ≡ᶠ fmap A.
  Proof. induction A; simpl; eauto. Qed.

  Hint Resolve fmap_iso : core.

  Local Fact bmap_iso Γ : Γ ≡ᵇ bmap Γ.
  Proof. induction Γ; simpl; eauto. Qed.

  Hint Resolve bmap_iso : core.

  (** if Γ ⊦ A is cut-free provable in the larger fragment, it is also
      provable in the smaller fragment thanks to LBI_cut_free_conservative. 
      The converse is much simpler to establish using LBI_map_sound which
      is not restricted to the cut-free fragment. *)

  Theorem LBI_cut_free_map_conservative Γ (A : BI_form µ prop) : 
     Γ L⊦[BI_cut_free] A ↔ bmap Γ L⊦[BI_cut_free] fmap A.
  Proof.
    split.
    + apply LBI_map_sound; auto.
    + apply LBI_cut_free_conservative; auto.
  Qed.

End LBI_map_conservative.

Check LBI_cut_free_map_conservative.

From Stdlib Require Import Arith Lia.

Section weight.

  Variables (µ : BI_conn → bool) (prop : Set).
  
  Implicit Types (Γ : BI_bunch µ prop) (Σ : BI_ctx µ prop).

  Fixpoint BI_bunch_weight Γ :=
    match Γ with
    | ⟨_⟩ => 1
    | ø[_] => 0
    | Γ ⊛[_] Δ => BI_bunch_weight Γ + BI_bunch_weight Δ
    end.
  
  Fact BI_bequiv_weight Γ Δ : Γ ≡ Δ → BI_bunch_weight Γ = BI_bunch_weight Δ.
  Proof. induction 1; simpl; lia. Qed.
  
  Fixpoint BI_ctx_weight Σ :=
    match Σ with
    | BI_ctx_hole => 0
    | BI_ctx_comp _ _ Γ Σ => BI_bunch_weight Γ + BI_ctx_weight Σ
    end.

  Fact BI_ctx_fill_weight Σ Γ : BI_bunch_weight Σ[Γ] = BI_ctx_weight Σ + BI_bunch_weight Γ.
  Proof. induction Σ as [ | [] ]; simpl; lia. Qed.

End weight.

#[local] Arguments BI_bunch_weight {_ _}.

Section Consistency.

  Variables (prop : Set).

  Lemma LBI_cut_free_consistent_weight Γ (A : BI_form (λ _, false) prop) : 
    Γ L⊦[BI_cut_free] A → BI_bunch_weight Γ ≠ 0.
  Proof.
    induction 1; try easy; eauto.
    1: match goal with H: _ ≡ _ |- _ => apply BI_bequiv_weight in H end; lia.
    1,2: match goal with H: _ ≠ 0 |- _ => rewrite BI_ctx_fill_weight in H |- * end; simpl in *; lia.
  Qed.
  
  Hint Constructors BI_form_iso BI_bunch_iso : core.

  Theorem LBI_cut_free_consistent µ k v : ~ ø[k] L⊦[BI_cut_free] @BI_form_var µ prop v.
  Proof.
    intros H.
    apply (LBI_cut_free_consistent_weight ø[k] (BI_form_var v)); auto.
    revert H; apply LBI_cut_free_conservative; auto.
  Qed.

End Consistency.

Check LBI_cut_free_consistent.