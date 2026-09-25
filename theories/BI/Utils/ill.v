(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation Arith Lia Utf8.

From Undecidability.BI.Utils
  Require Import decidable rel_phase_sem.
  
From Undecidability.Shared
  Require Import measure_ind fin_base utils_list.

From Undecidability.BI
  Require Import fin_extra.

Set Implicit Arguments.

Import ListNotations.

#[local] Reserved Notation "x ∘ y" (at level 50, no associativity, format "x ∘ y").
#[local] Reserved Notation "x ⊸ y" (at level 51, right associativity, format "x ⊸ y").
#[local] Reserved Notation "x ⊛ y "(at level 50, no associativity, format "x ⊛ y").

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70, format "X  ⊆  Y", no associativity).
#[local] Notation "X ≃ Y" := (X ⊆ Y ∧ Y ⊆ X) (at level 70, format "X  ≃  Y", no associativity).
#[local] Notation "A '∩' B" := (λ z, A z ∧ B z) (at level 50, format "A ∩ B", left associativity).

#[local] Hint Resolve eq_sg : core. 

#[local] Infix "~ₚ" := (@Permutation _) (at level 70).

(** Intuionistic Linear Logic, the ⊗, ⊸ and & fragment with constants *)

Section syntax.

  Variables (prop : Set).

  Inductive ill_conn := ill_with | ill_limp | ill_times.
  Inductive ill_cnst := ill_unit | ill_bot | ill_top.

  Inductive ill_form : Set :=
    | ill_var  : prop → ill_form
    | ill_cst  : ill_cnst → ill_form
    | ill_bin  : ill_conn → ill_form → ill_form → ill_form.

End syntax.

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  !   ‼  ∅  ⊢ *)

Module ILL_notations.

  Notation "⟙" := (ill_cst ill_top).
  Notation "⟘" := (ill_cst ill_bot).
  Notation "𝟙" := (ill_cst ill_unit).

  Infix "&" := (ill_bin ill_with) (at level 50).
  Infix "⊗" := (ill_bin ill_times) (at level 50).
  Infix "-⊗" := (ill_bin ill_limp) (at level 51, right associativity).

  Notation "£" := ill_var.

  Notation "∅" := nil (only parsing).

End ILL_notations.

#[local] Reserved Notation "l '⊢' x" (at level 70, no associativity).
#[local] Reserved Notation "l '⊢ₚ' x" (at level 70, no associativity).

Section ill_cut_free.

  Import ILL_notations.

  Variables (prop : Set).

  (** ILL sequent calculus with an explicit permutation rule *)

  Inductive ill_cut_free : list (ill_form prop) → ill_form prop → Prop :=

    | ill_cf_ax A :

              (*--------------*)
                   [A] ⊢ A

    | ill_cf_perm Γ Δ A :

            Γ ~ₚ Δ     →   Γ ⊢ A 
    →  (*-----------------------------*)
                   Δ ⊢ A

    | ill_cf_times_l Γ A B C :

               A::B::Γ ⊢ C 
    →  (*-----------------------------*)
                A⊗B::Γ ⊢ C
 
    | ill_cf_times_r Γ Δ A B :

            Γ ⊢ A    →   Δ ⊢ B
    → (*-----------------------------*)
               Γ++Δ ⊢ A⊗B

    | ill_cf_limp_l Γ Δ A B C : 

           Γ ⊢ A     →   B::Δ ⊢ C
    → (*-----------------------------*)
             A-⊗B::Γ++Δ ⊢ C

    | ill_cf_limp_r Γ A B :

               A::Γ ⊢ B
    → (*-----------------------------*)
               Γ ⊢ A-⊗B

    | ill_cf_with_l1 Γ A B C :

                 A::Γ ⊢ C 
    → (*-----------------------------*)
                A&B::Γ ⊢ C

    | ill_cf_with_l2 Γ A B C :

                B::Γ ⊢ C 
    → (*-----------------------------*)
               A&B::Γ ⊢ C
 
    | ill_cf_with_r Γ A B :

           Γ ⊢ A     →   Γ ⊢ B
    → (*-----------------------------*)
                Γ ⊢ A&B

  where "l ⊢ x" := (ill_cut_free l x).

  (** The permutation rule is now merged in each rule to
      and removed as an independent rule to remove that
      non decreasing rule *)

  Inductive ill_cut_free_perm : list (ill_form prop) → ill_form prop → Prop :=

    | ill_cfp_ax A :

              (*--------------*)
                   [A] ⊢ₚ A

    | ill_cfp_times_l Γ Σ A B C :

          Σ ~ₚ A⊗B::Γ  →  A::B::Γ ⊢ₚ C 
    →  (*-----------------------------*)
                   Σ ⊢ₚ C
 
    | ill_cfp_times_r Γ Δ Σ A B :

         Σ ~ₚ Γ++Δ → Γ ⊢ₚ A → Δ ⊢ₚ B
    → (*-----------------------------*)
                 Σ ⊢ₚ A⊗B

    | ill_cfp_limp_l Γ Δ Σ A B C : 

         Σ ~ₚ A-⊗B::Γ++Δ → Γ ⊢ₚ A → B::Δ ⊢ₚ C
    → (*-----------------------------*)
             Σ ⊢ₚ C

    | ill_cfp_limp_r Γ A B :
 
               A::Γ ⊢ₚ B
    → (*-----------------------------*)
               Γ ⊢ₚ A-⊗B

    | ill_cfp_with_l1 Γ Σ A B C :

         Σ ~ₚ A&B::Γ  →  A::Γ ⊢ₚ C 
    → (*-----------------------------*)
                Σ ⊢ₚ C

    | ill_cfp_with_l2 Γ Σ A B C :

         Σ ~ₚ A&B::Γ  →  B::Γ ⊢ₚ C 
    → (*-----------------------------*)
               Σ ⊢ₚ C
 
    | ill_cfp_with_r Γ A B :

           Γ ⊢ₚ A     →   Γ ⊢ₚ B
    → (*-----------------------------*)
                Γ ⊢ₚ A&B

  where "l ⊢ₚ x" := (ill_cut_free_perm l x).

  Hint Constructors ill_cut_free_perm Permutation : core.
  Hint Resolve Permutation_sym : core.

  Local Lemma ill_cfp_perm Γ A Σ : Γ ⊢ₚ A → Γ ~ₚ Σ → Σ ⊢ₚ A.
  Proof.
    induction 1 as
      [ 
      | Γ Σ' A B C H1 H2 IH2
      | Γ Δ Σ' A B
      | Γ Δ Σ' A B C
      | 
      | Γ Σ' A B C
      | Γ Σ' A B C
      | 
      ] in Σ |- *.
    + intros ->%Permutation_length_1_inv; auto.
    + econstructor; eauto.
    + intro; apply ill_cfp_times_r with Γ Δ; eauto.
    + intro; apply ill_cfp_limp_l with Γ Δ A B; eauto.
    + intro; apply ill_cfp_limp_r; eauto.
    + intro; apply ill_cfp_with_l1 with Γ A B; eauto.
    + intro; apply ill_cfp_with_l2 with Γ A B; eauto.
    + intro; apply ill_cfp_with_r; eauto.
  Qed.

  Local Lemma ill_cf_inc_cfp Γ A : Γ ⊢ A → Γ ⊢ₚ A.
  Proof.
    induction 1; eauto.
    eapply ill_cfp_perm; eauto.
  Qed.

  Hint Constructors ill_cut_free : core.

  Local Lemma ill_cfp_inc_cf Γ A : Γ ⊢ₚ A → Γ ⊢ A.
  Proof. induction 1; eauto. Qed.

  Hint Resolve ill_cf_inc_cfp ill_cfp_inc_cf : core.

  (** We show the equivalence between the two systems *)

  Theorem ill_cf_iff_cfp Γ A : Γ ⊢ₚ A ↔ Γ ⊢ A.
  Proof. split; auto. Qed.

End ill_cut_free.

Check ill_cf_iff_cfp.

(** Now we should show that ill_cut_free_perm is both 
     - terminating
     - finitary
    hence decidable !! *)

Section ill_cfp_dec.

  Import ILL_notations.

  Variables (prop : Set)
            (prop_eq_dec : ∀ v w : prop, {v=w} + {v≠w}).

  Implicit Types (A B : ill_form prop) (Γ Δ : list (ill_form prop)).

  (** Equality of formula, and of lists of those is decidable *)

  Local Fact ill_form_eq_dec A B : {A=B} + {A≠B}.
  Proof using prop_eq_dec. decide equality; auto; decide equality. Qed.

  Hint Resolve ill_form_eq_dec : core.

  Local Fact ill_list_form_eq_dec Γ Δ : {Γ=Δ} + {Γ≠Δ}.
  Proof using prop_eq_dec. apply list_eq_dec; auto. Qed.
  
  (** We split the system into 8 individual rules for a modular treatment *)

  Let stm := (list (ill_form prop) * ill_form prop)%type.

  Inductive ill_rule_id : list stm → stm → Prop :=
    | ill_rid_intro A : ill_rule_id [] ([A],A).

  Inductive ill_rule_times_l : list stm → stm → Prop :=
    | ill_rtimes_l_intro Γ Σ A B C : Σ ~ₚ A⊗B::Γ → ill_rule_times_l [(A::B::Γ,C)] (Σ,C).

  Inductive ill_rule_times_r : list stm → stm → Prop :=
    | ill_rtimes_r_intro Γ Δ Σ A B : Σ ~ₚ Γ++Δ → ill_rule_times_r [(Γ,A);(Δ,B)] (Σ,A⊗B).

  Inductive ill_rule_limp_l : list stm → stm → Prop :=
    | ill_rlimp_l_intro Γ Δ Σ A B C :  Σ ~ₚ A-⊗B::Γ++Δ → ill_rule_limp_l [(Γ,A);(B::Δ,C)] (Σ,C).

  Inductive ill_rule_limp_r : list stm → stm → Prop :=
    | ill_rlimp_r_intro Γ A B : ill_rule_limp_r [(A::Γ,B)] (Γ,A-⊗B).

  Inductive ill_rule_with_l1 : list stm → stm → Prop :=
    | ill_rwith_l1_intro Γ Σ A B C : Σ ~ₚ A&B::Γ → ill_rule_with_l1 [(A::Γ,C)] (Σ,C).

  Inductive ill_rule_with_l2 : list stm → stm → Prop :=
    | ill_rwith_l2_intro Γ Σ A B C : Σ ~ₚ A&B::Γ → ill_rule_with_l2 [(B::Γ,C)] (Σ,C).

  Inductive ill_rule_with_r : list stm → stm → Prop := 
    | ill_rwith_r_intro Γ A B : ill_rule_with_r [(Γ,A);(Γ,B)] (Γ,A&B).

  Let rule_map n := 
    match n with
    | 0 => ill_rule_id
    | 1 => ill_rule_times_l
    | 2 => ill_rule_times_r
    | 3 => ill_rule_limp_l
    | 4 => ill_rule_limp_r
    | 5 => ill_rule_with_l1
    | 6 => ill_rule_with_l2
    | _ => ill_rule_with_r
    end.

  (** This is the system of rules, indexed with a natural number for each 8 rules *)
  Let instances l s := ∃n, rule_map n l s ∧ n < 8.

  Tactic Notation "solve" "with" "rule" constr(r) :=
     econstructor 1; [ exists r; split; [ econstructor; eauto | try lia ] | auto ].

  Tactic Notation "split" "disj" "eqs" hyp(H) :=
    repeat match type of H with
           | False => destruct H
           | _ = _ \/ _ => destruct H as [ <- | H ]
           end.

  Tactic Notation "split" "Forall" :=
    repeat match goal with
           | H: Forall _ [] |- _ => clear H
           | H: Forall _ (_::_) |- _ => apply Forall_cons_iff in H as [ ? H ]
           end.

  Section equivalence.

    Hint Constructors ill_cut_free_perm : core.

    Notation "l ⊢ₚ x" := (@ill_cut_free_perm prop l x).

    Local Lemma ill_cfp_iff_rules Γ A : Γ ⊢ₚ A ↔ provable instances (Γ,A).
    Proof.
      split.
      + induction 1.
        * solve with rule 0.
        * solve with rule 1.
        * solve with rule 2.
        * solve with rule 3.
        * solve with rule 4.
        * solve with rule 5.
        * solve with rule 6.
        * solve with rule 7.
      + change A with (snd (Γ,A)) at 2.
        change Γ with (fst (Γ,A)) at 2.
        generalize (Γ,A).
        induction 1 as [ ? ? (n & Hn & _) ].
        do 7 (try destruct n as [|n]);
          destruct Hn; simpl; split Forall; eauto.
    Qed.

  End equivalence.

  Section well_founded.

    (** We show rule implications is well-founded *)

    Let Fixpoint ill_form_weight (A : ill_form prop) :=
      match A with
      | ill_cst _ _   => 1
      | ill_var _     => 1
      | ill_bin _ A B => 1 + ill_form_weight A + ill_form_weight B
      end.

    Let ill_list_weight := fold_right (λ x y, ill_form_weight x+y) 0.

    Local Fact ill_list_weight_perm Γ Δ : Γ ~ₚ Δ → ill_list_weight Γ = ill_list_weight Δ.
    Proof. induction 1; simpl; lia. Qed.

    Local Fact ill_list_weight_app Γ Δ : ill_list_weight (Γ++Δ) = ill_list_weight Γ + ill_list_weight Δ.
    Proof. induction Γ; simpl; lia. Qed.

    Let ill_seq_weight '(Γ,A) := ill_list_weight Γ + ill_form_weight A.

    (* By strong induction on the weight *)
    Local Lemma wf_instances : well_founded (λ r s, ∃h, instances h s ∧ In r h).
    Proof.
      intros s; induction on s as IH with measure (ill_seq_weight s).
      constructor; intros c (h & ((n & Hn & _) & H3)).
      apply IH; clear IH.
      do 7 (try destruct n as [|n]);
        destruct Hn; simpl in H3;
        split disj eqs H3; simpl.
      all: try match goal with H: _ ~ₚ _ |- _ => apply ill_list_weight_perm in H; simpl in H end; try lia.
      all: try rewrite  ill_list_weight_app in *; try lia.
    Qed.

  End well_founded.

  Section finitary.

    (** We show that each individual rule is finitary *)

    Hint Resolve fin_t_cst_left fin_t_eq fin_t_empty
                 ill_list_form_eq_dec : core.

    Local Fact fin_t_ill_rule_id s : fin_t (λ l, ill_rule_id l s).
    Proof using prop_eq_dec.
      destruct s as (Γ,A).
      apply fin_t_equiv with (λ l, Γ = [A] ∧ l = []).
      + split.
        * intros []; subst; constructor.
        * now inversion 1.
      + apply fin_t_cst_left; auto.
    Qed.

    Local Fact fin_t_ill_rule_times_l s : fin_t (λ l, ill_rule_times_l l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv 
        with (P := λ l, ∃ D Γ, Σ ~ₚ D::Γ 
                          ∧ match D with 
                            | A⊗B => l = [(A::B::Γ,C)] 
                            | _   => False 
                            end).
      + split.
        * intros ([ | | [] ] & ? & []); now subst.
        * inversion 1; subst; do 2 eexists; split; simpl; eauto; now simpl.
      + apply fin_t_perm_head.
        intros [ | | [] ] Γ E; simpl; auto.
    Qed.

    Local Fact fin_t_ill_rule_times_r s : fin_t (λ l, ill_rule_times_r l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, match C with
                        | A⊗B => ∃ Γ Δ, Σ ~ₚ Γ++Δ ∧ l = [(Γ,A);(Δ,B)]
                        | _   => False
                        end).
      + split.
        * destruct C as [ | | [] ]; simpl; try easy.
          intros (? & ? & []); now subst.
        * inversion 1; subst; eauto.
      + destruct C as [ | | [] ]; simpl; auto.
        apply fin_t_perm_split; auto.
    Qed.

    Local Fact fin_t_ill_rule_limp_l s : fin_t (λ l, ill_rule_limp_l l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, ∃ D Γ Δ, Σ ~ₚ D::Γ++Δ 
                          ∧ match D with
                            | A-⊗B => l = [(Γ,A);(B::Δ,C)]
                            | _    => False
                            end).
      + split.
        * intros ([ | | [] ] & ? & ? & []); now subst.
        * inversion 1; subst; do 3 eexists; split; simpl; eauto; now simpl.
      + apply fin_t_perm_head_split.
        intros [ | | [] ] ? ?; simpl; auto.
    Qed.
  
    Local Fact fin_t_ill_rule_limp_r s : fin_t (λ l, ill_rule_limp_r l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, match C with
                        | A-⊗B => l = [(A::Σ,B)]
                        | _    => False
                        end).
      + split.
        * destruct C as [ | | [] ]; simpl; intros; now subst.
        * inversion 1; subst; eauto.
      + destruct C as [ | | [] ]; simpl; auto.
    Qed.

    Local Fact fin_t_ill_rule_with_l1 s : fin_t (λ l, ill_rule_with_l1 l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, ∃ D Γ, Σ ~ₚ D::Γ
                          ∧ match D with
                            | A&B => l = [(A::Γ,C)]
                            | _   => False
                            end).
      + split.
        * intros ([ | | [] ] & ? & []); try easy; subst; econstructor; eauto.
        * inversion 1; subst; do 2 eexists; split; simpl; eauto; now simpl.
      + apply fin_t_perm_head.
        intros [ | | [] ] ? ?; simpl; auto.
    Qed.

    Local Fact fin_t_ill_rule_with_l2 s : fin_t (λ l, ill_rule_with_l2 l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, ∃ D Γ, Σ ~ₚ D::Γ
                          ∧ match D with
                            | A&B => l = [(B::Γ,C)]
                            | _   => False
                            end).
      + split.
        * intros ([ | | [] ] & ? & []); try easy; subst; econstructor; eauto.
        * inversion 1; subst; do 2 eexists; split; simpl; eauto; now simpl.  
      + apply fin_t_perm_head.
        intros [ | | [] ] ? ?; simpl; auto.
    Qed.

    Local Fact fin_t_ill_rule_with_r s : fin_t (λ l, ill_rule_with_r l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, match C with
                        | A&B => l = [(Σ,A);(Σ,B)]
                        | _   => False
                        end).
      + split.
        * destruct C as [ | | [] ]; simpl; intros; now subst.
        * inversion 1; subst; eauto.
      + destruct C as [ | | [] ]; simpl; auto.
    Qed.

    Hint Resolve fin_t_ill_rule_id
                 fin_t_ill_rule_times_l fin_t_ill_rule_times_r
                 fin_t_ill_rule_limp_l fin_t_ill_rule_limp_r
                 fin_t_ill_rule_with_l1 fin_t_ill_rule_with_l2 fin_t_ill_rule_with_r : core.

    Local Lemma fin_t_instances c : fin_t (λ h, instances h c).
    Proof using prop_eq_dec.
      apply fin_t_idx_union.
      intros n _; do 7 (try destruct n as [|n]); simpl; auto.
    Qed.

  End finitary.

  (* We use the decidability algorithm for well-founded finitely branching
     proofs systems *)
  Local Theorem ill_instances_dec : ∀s, { provable instances s } + { ¬ provable instances s }.
  Proof using prop_eq_dec.
    apply provable_wf_fin_dec.
    + apply wf_instances.
    + apply fin_t_instances.
  Qed.

  Notation "l ⊢ x" := (@ill_cut_free prop l x).

  (* We transport decidability along equivalence *)
  Corollary iff_cut_free_decidable Γ A : { Γ ⊢ A } + { ¬ Γ ⊢ A }.
  Proof using prop_eq_dec.
    destruct (ill_instances_dec (Γ,A)); [ left | right ];
      rewrite <- ill_cf_iff_cfp, ill_cfp_iff_rules; trivial.
  Qed.

End ill_cfp_dec.

Check iff_cut_free_decidable.

Section ill_rel_sem.

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

  Reserved Notation "⟦ A ⟧ᶠ" (at level 0, format "⟦ A ⟧ᶠ").
  Reserved Notation "⟦ Θ ⟧ᵇ" (at level 0, format "⟦ Θ ⟧ᵇ").

  Hint Resolve cap_closed : core.

  Variables (prop : Set).

  Section sem_ill_form.

    Variables (φ : prop → M → Prop) (Hφ: ∀v, closed (φ v)).

    Fixpoint sem_ill_form (A : ill_form prop) { struct A } : M → Prop :=
      match A with
      | ill_var v             => φ v
      | ill_cst _ ill_unit    => cl (sg e)
      | ill_cst _ ill_top     => top
      | ill_cst _ ill_bot     => bot
      | ill_bin ill_times A B => cl (⟦A⟧ᶠ ∘ ⟦B⟧ᶠ)
      | ill_bin ill_with A B  => ⟦A⟧ᶠ ∩ ⟦B⟧ᶠ
      | ill_bin ill_limp A B  => ⟦A⟧ᶠ ⊸ ⟦B⟧ᶠ
      end
    where "⟦ A ⟧ᶠ" := (sem_ill_form A).

    Fact sem_ill_form_closed A : closed ⟦A⟧ᶠ.
    Proof using cl_idempotent cl_increase cl_monotone cl_stable Hφ.
      induction A as [ | [] | [] ]; simpl; eauto using closed_magicwand.
    Qed.

  End sem_ill_form.

  Section sem_ill_list_form.

    Variables (φ : ill_form prop → M → Prop) (Hφ : ∀A, closed (φ A)).

    Definition sem_ill_list_form := fold_right (λ A x, cl (φ A ∘ x)) (cl (sg e)).

    Notation "⟦ Θ ⟧ᵇ" := (sem_ill_list_form Θ).

    Fact sem_ill_list_form_closed Θ : closed ⟦Θ⟧ᵇ.
    Proof using cl_idempotent cl_monotone Hφ.
      induction Θ as [ | [] ]; simpl; eauto.
    Qed.

    Hint Resolve sem_ill_list_form_closed : core.
    Hint Resolve equiv_refl equiv_sym equiv_trans unit_neutral : core.

    Fact sem_ill_list_form_perm Γ Δ : Γ ~ₚ Δ → ⟦Γ⟧ᵇ ≃ ⟦Δ⟧ᵇ.
    Proof using cl_associative 
                cl_commute 
                cl_idempotent cl_increase cl_monotone
                cl_neutral_1 cl_neutral_2
                cl_stable
                Hφ.
      induction 1; simpl; eauto using times_congruence.
      eapply equiv_trans.
      1: eapply equiv_sym, times_associative; eauto.
      eapply equiv_trans.
      2: apply times_associative; eauto.
      apply times_congruence; auto.
      apply times_commute; auto.
    Qed.

    Fact sem_ill_list_form_app Γ Δ : ⟦Γ++Δ⟧ᵇ ≃ cl (⟦Γ⟧ᵇ ∘ ⟦Δ⟧ᵇ).
    Proof using cl_associative cl_commute
                cl_idempotent 
                cl_increase cl_monotone 
                cl_neutral_1 cl_neutral_2
                cl_stable
                Hφ.
      induction Γ; simpl.
      + eapply equiv_sym, unit_neutral; auto.
      + eapply equiv_sym, equiv_trans.
        1: eapply times_associative; eauto.
        apply equiv_sym, times_congruence; auto.
    Qed.

  End sem_ill_list_form.

  Variables (φ : prop → M → Prop) (Hφ : ∀v, closed (φ v)).

  Hint Resolve sem_ill_form_closed : core.

  Theorem ill_sem_soundness Γ A : ill_cut_free Γ A → sem_ill_list_form (sem_ill_form φ) Γ ⊆ sem_ill_form φ A.
  Proof using cl_idempotent cl_increase cl_monotone
              cl_commute 
              cl_idempotent cl_increase cl_monotone
              cl_neutral_1 cl_neutral_2
              cl_associative
              cl_stable
              Hφ.
    induction 1.
    + simpl; apply unit_neutral'; eauto.
    + apply inc_trans with (2 := IHill_cut_free).
      apply sem_ill_list_form_perm; auto.
    + apply inc_trans with (2 := IHill_cut_free); simpl.
      apply times_associative; eauto.
    + simpl.
      eapply inc_trans; [ eapply sem_ill_list_form_app | ]; auto.
      apply times_monotone; auto.
    + simpl.
      apply inc_trans with (2 := IHill_cut_free2); simpl.
      eapply inc_trans.
      * eapply times_monotone; [ eauto |apply inc_refl; eauto |].
        eapply sem_ill_list_form_app; auto.
      * eapply inc_trans; [ eapply times_associative; eauto | ].
        apply times_monotone; eauto.
        eapply inc_trans; [ eapply times_commute; eauto | ].
        apply cl_closed; auto.
        apply magicwand_spec, magicwand_monotone; auto.
    + simpl.
      apply magicwand_spec.
      apply inc_trans with (2 := IHill_cut_free); simpl; auto.
    + simpl.
      apply inc_trans with (2 := IHill_cut_free); simpl; auto.
      apply times_monotone; eauto; tauto.
    + simpl.
      apply inc_trans with (2 := IHill_cut_free); simpl; auto.
      apply times_monotone; eauto; tauto.
    + simpl; split; auto.
  Qed.

End ill_rel_sem.

Section ill_cut_free_completeness.

Section ill_cut_free_completeness.

  Variables (prop : Set).

  Let M := list (ill_form prop).

  Implicit Types (Γ : M) (X Y : M → Prop).
  
  Notation "l ⊢ x" := (@ill_cut_free prop l x).
  
  Let cl X Γ := ∀ Σ A, (∀Δ, X Δ → Δ++Σ ⊢ A)
                                → Γ++Σ ⊢ A.

  Local Fact cl_increase X : X ⊆ cl X.
  Proof. intros Γ HΓ Σ A H; now apply H. Qed.

  Local Fact cl_monotone X Y : X ⊆ Y → cl X ⊆ cl Y.
  Proof. intros HXY Γ HΓ Σ A H; apply HΓ; intros ? ?%HXY; auto. Qed.

  Local Fact cl_idempotent X : cl (cl X) ⊆ cl X.
  Proof. intros Γ HΓ Σ A H; apply HΓ; intros D HD; apply HD; auto. Qed.
  
  Hint Resolve cl_monotone cl_increase cl_idempotent : core.

  (** The relational bi-monoidal structure *)
  
  Let comp (Γ Δ Θ : M) := Γ++Δ ~ₚ Θ.

  Infix "∘" := (composes _ comp).
  Infix "⊸" := (magicwand _ comp).
  Abbreviation e := ([] : M).
  
  Hint Resolve Permutation_app Permutation_app_comm : core.

  Local Fact cl_perm X Γ Δ : Γ ~ₚ Δ → cl X Γ → cl X Δ.
  Proof.
    intros H1 H2 Σ A H3.
    apply ill_cf_perm with (Γ++Σ); auto.
  Qed.

  Local Fact cl_stable_left X Y : cl X ∘ Y ⊆ cl (X ∘ Y).
  Proof.
    intros _ [ Γ Δ Θ H1 H2 H3 ]; red in H1, H3.
    apply cl_perm with (1 := H3).
    intros Σ A HA.
    rewrite <- app_assoc.
    apply H1.
    intros D HD; rewrite app_assoc.
    apply HA; eexists D _; try red; eauto.
  Qed.

  Local Fact cl_stable_right X Y : X ∘ cl Y ⊆ cl (X ∘ Y).
  Proof.
    intros _ [ Γ Δ Θ H1 H2 H3 ]; red in H2, H3.
    apply cl_perm with (1 := H3).
    intros Σ A HA.
    apply ill_cf_perm with (Δ++(Γ++Σ)).
    1: rewrite app_assoc; eauto.
    apply H2.
    intros D HD.
    rewrite app_assoc.
    apply HA; eexists _ D; try red; eauto.
  Qed.

  Local Hint Resolve cl_stable_left cl_stable_right : core.

  Local Fact cl_stable X Y : cl X ∘ cl Y ⊆ cl (X ∘ Y).
  Proof. apply cl_stable_lr_imp_stable; eauto. Qed.

  Local Fact cl_sg Γ : cl (sg Γ) Γ.
  Proof. apply cl_increase; eauto. Qed.

  Hint Resolve cl_sg : core.
  
  Hint Constructors Permutation : core.

  Local Fact cl_neutral_1 Γ : cl (sg e ∘ sg Γ) Γ.
  Proof. intros Σ A H; apply H; exists e Γ; red; auto. Qed.

  Local Fact cl_neutral_2 Γ : sg e ∘ sg Γ ⊆ cl (sg Γ).
  Proof. intros _ [ ? ? ? <- <- ?]; apply cl_perm with Γ; eauto. Qed.

  Local Fact cl_commute Γ Δ : sg Γ ∘ sg Δ ⊆ cl (sg Δ ∘ sg Γ).
  Proof.
    intros _ [ ? ? Θ <- <- H ]; red in H.
    apply cl_perm with (Δ ++ Γ); eauto.
    apply cl_increase; eauto.
    exists Δ Γ; try red; auto.
  Qed.

  Local Fact cl_associative Γ Δ Θ : sg Γ ∘ (sg Δ ∘ sg Θ) ⊆ cl ((sg Γ ∘ sg Δ) ∘ sg Θ).
  Proof.
    intros _ [ _ _ D <- [ _ _ C <- <- H1 ] H2 ].
    apply cl_perm with ((Γ ++ Δ) ++ Θ); auto.
    + red in H1, H2; rewrite <- app_assoc; eauto.
    + apply cl_increase.
      exists (Γ ++ Δ) Θ; try red; auto.
      exists Γ Δ; try red; auto.
  Qed.

  Let dwncl A Γ := Γ ⊢ A.
  Abbreviation φ := (λ v, dwncl (ill_var v)).
  Let sem_form :=  sem_ill_form cl comp e φ.
  Let sem_list := sem_ill_list_form cl comp e sem_form.

  Local Fact dwncl_closed A : cl (dwncl A) ⊆ dwncl A.
  Proof. intros ? H; rewrite <- app_nil_r; apply (H []); intro; rewrite app_nil_r; auto. Qed.

  Hint Resolve cl_idempotent cl_increase cl_monotone 
               cl_neutral_1 cl_neutral_2
               cl_associative cl_commute 
               cl_stable 
               dwncl_closed : core.

  Local Fact sem_form_is_closed A : cl (sem_form A) ⊆ sem_form A.
  Proof. apply sem_ill_form_closed; eauto. Qed.

  Hint Resolve sem_form_is_closed : core.

  Local Fact sem_list_is_closed Γ : cl (sem_list Γ) ⊆ sem_list Γ.
  Proof. apply sem_ill_list_form_closed; eauto. Qed.

  Hint Resolve sem_list_is_closed : core.
  
  (*

  Local Fact cl_unit_l k h : cl (sg e ⟨BI_form_unit µ prop k h⟩.
  Proof. intros ? ? ?; auto using LBI_unit_l. Qed.

  Local Fact dwncl_unit_r k h : sg ø[k] ⊆ dwncl (BI_form_unit µ prop k h).
  Proof. apply sg_inc, LBI_unit_r. Qed. 
  
  *)
  
  Import ILL_notations.
  
  Hint Constructors ill_cut_free : core.

  Local Fact cl_times_l A B : cl (sg [A;B]) [A⊗B].
  Proof. intros ? ? H; apply ill_cf_times_l, (H [_;_]); auto. Qed.

  Local Fact dwncl_conj_r A B :  dwncl A ∘ dwncl B ⊆ dwncl (A⊗B).
  Proof. intros ? [ ? ? ? ? ? H ]; red in H |- *; eauto. Qed.
 
  Local Fact cl_impl_l A B : (dwncl A ⊸ cl (sg [B])) [A-⊗B].
  Proof.
    intros ? [ G D E H1 H2 H3 ]; red in H3.
    apply cl_perm with (1 := H3).
    rewrite <- H2.
    intros ? ? ?.
    eapply ill_cf_perm with ([A-⊗B]++(G++Σ)).
    + rewrite app_assoc; auto.
    + simpl; apply ill_cf_limp_l; auto.
      apply (H [_]); auto.
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


  



  