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

  Variables (µ µ' : BI_conn → bool) (prop : Set).

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

  Lemma LBI_cut_free_conservative Γ A :
    Γ L⊦[BI_cut_free] A → ∀ Δ B, BI_bunch_iso Γ Δ → BI_form_iso A B → Δ L⊦[BI_cut_free] B.
  Proof.
    induction 1.
    + intros ? ? (B & -> & E)%BI_bi_invert <-%(BI_fi_inj E).
      apply LBI_axiom.
    +
  Admitted.

End convervative_wo_cut.
