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
  Require Import BI utils lbi cutelim.

Import BI_notations LBI_tactics.

Section convervative_wo_cut.

  Variable (prop : Set).

  Section iso.

    Variables (µ µ' : BI_conn → bool).

    Inductive BI_form_iso : BI_form µ prop → BI_form µ' prop → Prop :=
      | BI_fi_var v :                 BI_form_iso (BI_form_var _ v) (BI_form_var _ v)
      | BI_fi_unit k h h' :           BI_form_iso (BI_form_unit _ _ k h) (BI_form_unit _ _ k h')
      | BI_fi_conj k h h' A B A' B' : BI_form_iso A A'
                                    → BI_form_iso B B'
                                    → BI_form_iso (BI_form_conj k h A B) (BI_form_conj k h' A' B')
      | BI_fi_impl k h h' A B A' B' : BI_form_iso A A'
                                    → BI_form_iso B B'
                                    → BI_form_iso (BI_form_impl k h A B) (BI_form_impl k h' A' B')
      | BI_fi_bot h h'              : BI_form_iso (BI_form_bot _ _ h) (BI_form_bot _ _ h')
      | BI_fi_disj h h' A B A' B'   : BI_form_iso A A'
                                    → BI_form_iso B B'
                                    → BI_form_iso (BI_form_disj h A B) (BI_form_disj h' A' B') 
      .

    Fact BI_fi_invert C D :
        BI_form_iso C D 
      → match C with
        | BI_form_var _ v      => D = BI_form_var _ v
        | BI_form_unit _ _ k h => ∃h', D = BI_form_unit _ _ k h'
        | BI_form_conj k h A B => ∃ A' B' h', D = BI_form_conj k h' A' B' ∧ BI_form_iso A A' ∧ BI_form_iso B B'
        | BI_form_impl k h A B => ∃ A' B' h', D = BI_form_impl k h' A' B' ∧ BI_form_iso A A' ∧ BI_form_iso B B'
        | BI_form_bot _ _ h    => ∃h', D = BI_form_bot _ _ h'
        | BI_form_disj h A B   => ∃ A' B' h', D = BI_form_disj h' A' B' ∧ BI_form_iso A A' ∧ BI_form_iso B B'
        end.
    Proof.
      intros [ | | k h h' A B A' B' | k h h' A B A' B' | h h' | h h' A B A' B' ]; eauto.
      all: exists A', B', h'; auto.
    Qed.

    Hint Resolve eq_bool_pirr : core.

    Fact BI_fi_inj { A B B' } : BI_form_iso A B → BI_form_iso A B' → B = B'.
    Proof.
      intros E; revert E B'.
      induction 1.
      + now intros ? ->%BI_fi_invert.
      + intros ? (? & ->)%BI_fi_invert; f_equal; auto.
      + intros ? (? & ? & ? & -> & ? & ?)%BI_fi_invert; f_equal; auto.
      + intros ? (? & ? & ? & -> & ? & ?)%BI_fi_invert; f_equal; auto.
      + intros ? (? & ->)%BI_fi_invert; f_equal; auto.
      + intros ? (? & ? & ? & -> & ? & ?)%BI_fi_invert; f_equal; auto.
    Qed.

    Inductive BI_bunch_iso : BI_bunch µ prop → BI_bunch µ' prop → Prop :=
      | BI_bi_atom A B         : BI_form_iso A B
                               → BI_bunch_iso ⟨A⟩ ⟨B⟩
      | BI_bi_unit k           : BI_bunch_iso (BI_bunch_unit _ _ k) (BI_bunch_unit _ _ k)
      | BI_bi_comp k Γ Δ Γ' Δ' : BI_bunch_iso Γ Γ'
                               → BI_bunch_iso Δ Δ'
                               → BI_bunch_iso (Γ ⊛[k] Δ) (Γ' ⊛[k] Δ')
      .

    Fact BI_bi_invert Γ Δ :
        BI_bunch_iso Γ Δ
      → match Γ with
        | ⟨A⟩                 => ∃B, Δ = ⟨B⟩ ∧ BI_form_iso A B
        | BI_bunch_unit _ _ k => Δ = BI_bunch_unit _ _ k
        | Γ' ⊛[k] Γ''         => ∃ Δ' Δ'', Δ = Δ' ⊛[k] Δ'' ∧ BI_bunch_iso Γ' Δ' ∧ BI_bunch_iso Γ'' Δ''
        end.
    Proof. intros []; eauto. Qed.

    Hint Constructors BI_bunch_equiv : core.

    Inductive BI_ctx_iso : BI_ctx µ prop → BI_ctx µ' prop → Prop :=
      | BI_ci_hole               : BI_ctx_iso (BI_ctx_hole _ _) (BI_ctx_hole _ _)
      | BI_ci_comp s k Γ Γ' Σ Σ' : BI_bunch_iso Γ Γ'
                                 → BI_ctx_iso Σ Σ'
                                 → BI_ctx_iso (BI_ctx_comp s k Γ Σ) (BI_ctx_comp s k Γ' Σ') 
      .

    Hint Constructors BI_ctx_iso : core.

    Fact BI_ci_bi_subst Σ Σ' Γ Γ' : BI_ctx_iso Σ Σ' → BI_bunch_iso Γ Γ' → BI_bunch_iso Σ[Γ] Σ'[Γ'].
    Proof.
      intros H1 H2; revert H1; induction 1 as [ | [] ]; simpl; eauto; constructor; auto.
    Qed.

    Fact BI_subst_invert Σ Γ Δ : 
        BI_bunch_iso Σ[Γ] Δ
      → ∃ Σ' Γ', Δ = Σ'[Γ'] ∧ BI_bunch_iso Γ Γ' ∧ BI_ctx_iso Σ Σ'.
    Proof.
      revert Δ.
      induction Σ as [ | [] k G Σ IH ]; intros D; simpl.
      + exists (BI_ctx_hole _ _), D; auto.
      + intros (G' & D' & -> & ? & (S' & G'' & -> & [])%IH)%BI_bi_invert.
        exists (BI_ctx_comp BI_left k G' S'), G''; simpl; auto.
      + intros (G' & D' & -> & (S' & G'' & -> & [])%IH & ?)%BI_bi_invert.
        exists (BI_ctx_comp BI_right k D' S'), G''; simpl; auto.
    Qed.

  End iso.

  Arguments BI_fi_inj {_ _ _ _ _}.
  Arguments BI_form_iso {_ _}.
  Arguments BI_bunch_iso {_ _}.

  Hint Constructors BI_form_iso BI_bunch_iso : core.

  Fact BI_fi_sym µ µ' A B : @BI_form_iso µ µ' A B → BI_form_iso B A.
  Proof. induction 1; eauto. Qed.

  Hint Resolve BI_fi_sym : core.

  Fact BI_bi_sym µ µ' Γ Δ : @BI_bunch_iso µ µ' Γ Δ → BI_bunch_iso Δ Γ.
  Proof. induction 1; eauto. Qed.

  Hint Constructors BI_bunch_equiv BI_bunch_iso : core.

  Lemma BI_bi_bequiv_rec µ µ' Γ Γ' :
      Γ ≡ Γ'
    → (∀Δ, @BI_bunch_iso µ µ' Γ Δ → ∃Δ', Δ ≡ Δ' ∧ BI_bunch_iso Γ' Δ')
    ∧ (∀Δ', @BI_bunch_iso µ µ' Γ' Δ' → ∃Δ, Δ ≡ Δ' ∧ BI_bunch_iso Γ Δ).
  Proof.
    induction 1 as [ G | G G' E IH | G G' G'' E1 IH1 E2 IH2 | | | k Γ Δ Θ | k Γ Δ Θ H IH ].
    + split; eauto.
    + split; intros ? (D' & ? & ?)%IH; exists D'; auto.
    + split.
      * intros ? (D' & ? & (D'' & ? & ?)%IH2)%IH1; exists D''; eauto.
      * intros ? (D' & ? & (D'' & ? & ?)%IH1)%IH2; exists D''; eauto.
    + split.
      * intros ? (? & D & -> & ->%BI_bi_invert & ?)%BI_bi_invert; eauto.
      * intros D ?.
        exists (ø[k] ⊛[k] D); eauto.
    + split; intros ? (G & D & -> & ? & ?)%BI_bi_invert; exists (D ⊛[k] G); eauto.
    + split.
      * intros ? (? & T & -> & (G & D & -> & [])%BI_bi_invert & ?)%BI_bi_invert; eauto.
      * intros ? (G & ? & -> & ? & (D & T & -> & [])%BI_bi_invert)%BI_bi_invert; eauto.
    + split; intros ? (G & D & -> & ? & (T & [])%IH)%BI_bi_invert; exists (G ⊛[k] T); eauto.
  Qed.

  Corollary BI_bi_bequiv {µ µ'} {Γ Γ' : BI_bunch µ prop} {Δ : BI_bunch µ' prop} :
      Γ ≡ Γ'
    → BI_bunch_iso Γ Δ 
    → ∃Δ', Δ ≡ Δ' ∧ BI_bunch_iso Γ' Δ'.
  Proof. intros H; apply BI_bi_bequiv_rec with (1 := H). Qed.

  Hint Resolve BI_ci_bi_subst : core.

  Lemma LBI_cut_free_conservative µ µ' Γ A :
    Γ L⊦[BI_cut_free] A → ∀ Δ B, @BI_bunch_iso µ µ' Γ Δ → BI_form_iso A B → Δ L⊦[BI_cut_free] B.
  Proof.
    induction 1 as   [ 
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
    + intros ? ? (B & -> & E)%BI_bi_invert <-%(BI_fi_inj E).
      apply LBI_axiom.
    + (* cut is forbidden
         AND THIS IS WHY THE PROOF WORKS !! *)
      easy.
    + intros D B' (D' & [])%(BI_bi_bequiv (BI_bequiv_sym H)) ?.
      apply LBI_equiv with D'; auto.
    + intros ? B' (Δ' & Γ' & -> & [])%BI_subst_invert ?.
      apply LBI_weak, IH; auto.
    + intros ? B' (Δ' & Γ' & -> & [])%BI_subst_invert ?.
      apply LBI_cntr, IH; auto.
    + intros ? B' (Δ' & Γ' & -> & (C & -> & (h' & ->)%BI_fi_invert)%BI_bi_invert & ?)%BI_subst_invert ?.
      apply LBI_unit_l; auto.
    + intros ? B' (Δ' & Γ' & -> & (C & -> & (h' & ->)%BI_fi_invert)%BI_bi_invert & ?)%BI_subst_invert ?.
      apply LBI_unit_l; auto.
    + intros ? ? ->%BI_bi_invert (h' & ->)%BI_fi_invert.
      apply LBI_unit_r.
    + intros ? ? ->%BI_bi_invert (h' & ->)%BI_fi_invert.
      apply LBI_unit_r.
    + intros ? ? (Δ' & Γ' & -> & (? & -> & (A' & B' & ? & -> & [])%BI_fi_invert)%BI_bi_invert & ?)%BI_subst_invert ?.
      apply LBI_conj_l; auto.
    + intros ? ? (Δ' & Γ' & -> & (? & -> & (A' & B' & ? & -> & [])%BI_fi_invert)%BI_bi_invert & ?)%BI_subst_invert ?.
      apply LBI_conj_l; auto.
    + intros ? ? (Γ' & Δ' & -> & [])%BI_bi_invert (A' & B' & ? & -> & [])%BI_fi_invert.
      apply LBI_conj_r; auto.
    + intros ? ? (Γ' & Δ' & -> & [])%BI_bi_invert (A' & B' & ? & -> & [])%BI_fi_invert.
      apply LBI_conj_r; auto.
    + intros ? ? (Γ' & ? & -> & (Δ' & ? & -> & ? & (? & -> & (A' & B' & ? & -> & [])%BI_fi_invert)%BI_bi_invert)%BI_bi_invert & ?)%BI_subst_invert ?.
      apply LBI_impl_l; eauto.
    + intros ? ? (Γ' & ? & -> & (Δ' & ? & -> & ? & (? & -> & (A' & B' & ? & -> & [])%BI_fi_invert)%BI_bi_invert)%BI_bi_invert & ?)%BI_subst_invert ?.
      apply LBI_impl_l; eauto.
    + intros ? ? ? (A' & B' & ? & -> & [])%BI_fi_invert.
      apply LBI_impl_r; auto.
    + intros ? ? ? (A' & B' & ? & -> & [])%BI_fi_invert.
      apply LBI_impl_r; auto.
    + intros ? ? (Γ' & ? & -> & (? & -> & (? & ->)%BI_fi_invert)%BI_bi_invert & ?)%BI_subst_invert ?.
      apply LBI_bot_l.
    + intros ? ? (Δ' & ? & -> & (? & -> & (A' & B' & ? & -> & [])%BI_fi_invert)%BI_bi_invert & ?)%BI_subst_invert ?.
      apply LBI_disj_l; auto.
    + intros ? ? ? (A' & B' & ? & -> & [])%BI_fi_invert.
      apply LBI_disj_r1; auto.
    + intros ? ? ? (A' & B' & ? & -> & [])%BI_fi_invert.
      apply LBI_disj_r2; auto.
  Qed.

End convervative_wo_cut.

Section LBI_map_conservative.

  Variables (µ µ' : BI_conn → bool) (Hµ : ∀c, µ c = true → µ' c = true) (prop : Set).

  Arguments BI_form_map {_ _} _ {_ _}.
  Arguments BI_bunch_map {_ _} _ {_ _}.

  Let fmap := @BI_form_map µ µ' Hµ prop _ (λ x, x).
  Let bmap := @BI_bunch_map µ µ' Hµ prop _ (λ x, x).

  (** if Γ ⊦ A is cut-free provable in the larger fragment, it is also
      provable in the smaller fragment *)

  Hint Constructors BI_form_iso BI_bunch_iso : core.

  Local Fact fmap_iso A : BI_form_iso _ _ _ (fmap A) A.
  Proof. induction A; simpl; eauto. Qed.

  Hint Resolve fmap_iso : core.

  Local Fact bmap_iso Γ : BI_bunch_iso _ _ _ (bmap Γ) Γ.
  Proof. induction Γ; simpl; eauto. Qed.

  Hint Resolve bmap_iso : core.

  Theorem LBI_cut_free_map_conservative Γ (A : BI_form µ prop) : 
     Γ L⊦[BI_cut_free] A ↔ bmap Γ L⊦[BI_cut_free] fmap A.
  Proof.
    split.
    + apply LBI_map_sound; auto.
    + intros H.
      apply LBI_cut_free_conservative with (1 := H); auto.
  Qed.

End LBI_map_conservative.

Check LBI_cut_free_map_conservative.
