(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation Relations Arith Lia Utf8.

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

#[local] Fact In_inv X (x : X) l :
    In x l
  → match l with 
    | []   => False
    | y::l => y = x ∨ In x l
    end.
Proof. now destruct l. Qed.

Tactic Notation "split" "In" hyp(H) :=
  repeat match type of H with
  | In _ []     => apply In_inv in H as []
  | In _ (_::_) => apply In_inv in H as [ <- | H ]
  end.

Tactic Notation "split" "In_t" hyp(H) :=
  repeat match type of H with
  | In_t _ []     => apply In_t_inv in H as []
  | In_t _ (_::_) => apply In_t_inv in H as [ <- | H ]
  end.

Tactic Notation "split" "Forall" :=
  repeat match goal with
  | H: Forall _ [] |- _ => clear H
  | H: Forall _ (_::_) |- _ => apply Forall_cons_iff in H as [ ? H ]
  end.

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

  Notation "⟙" := (ill_cst _ ill_top).
  Notation "⟘" := (ill_cst _ ill_bot).
  Notation "𝟙" := (ill_cst _ ill_unit).

  Infix "&" := (ill_bin ill_with) (at level 50).
  Infix "⊗" := (ill_bin ill_times) (at level 50).
  Infix "-⊗" := (ill_bin ill_limp) (at level 51, right associativity).

  Notation "£" := ill_var.

  Notation "∅" := nil (only parsing).

End ILL_notations.

#[local] Reserved Notation "l '⊢' x" (at level 70, no associativity).
#[local] Reserved Notation "l '⊢ₚ' x" (at level 70, no associativity).

Section ill_cut_free_decidable.

  Import ILL_notations.

  Variables (prop : Set).
  
  Implicit Types (A B : ill_form prop) (Γ Δ : list (ill_form prop)).

  (** ILL sequent calculus with an explicit permutation rule *)

  Inductive ill_cut_free : list (ill_form prop) → ill_form prop → Prop :=

    | ill_cf_ax A :

              (*--------------*)
                   [A] ⊢ A

    | ill_cf_perm Γ Δ A :

            Γ ~ₚ Δ     →   Γ ⊢ A 
    →  (*-----------------------------*)
                   Δ ⊢ A

    | ill_cf_unit_l Γ C :
    
                Γ ⊢ C
    →     (*--------------*)
         (* *) 𝟙::Γ ⊢ C

    | ill_cf_unit_r :

        (*--------------*)
              [] ⊢ 𝟙

    | ill_cf_bot_l Γ C :
 
        (*--------------*)
       (* *) ⟘::Γ ⊢ C

    | ill_cf_top_r Γ :
 
        (*--------------*)
              Γ ⊢ ⟙

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

  (** Equality of formula, and of lists of those is decidable *)
  Hypothesis prop_eq_dec : ∀ v w : prop, {v = w} + {v ≠ w}.

  Local Fact ill_form_eq_dec A B : {A=B} + {A≠B}.
  Proof using prop_eq_dec. decide equality; auto; decide equality. Qed.

  Hint Resolve ill_form_eq_dec : core.

  Local Fact ill_list_form_eq_dec Γ Δ : {Γ=Δ} + {Γ≠Δ}.
  Proof using prop_eq_dec. apply list_eq_dec; auto. Qed.
  
  (** We split the system into individual rules for a modular treatment,
      excluding the permutation rule which is dealt with
      separatly via Theorem provable_decr_fin_equiv_dec *)

  Let stm := (list (ill_form prop) * ill_form prop)%type.

  Inductive ill_rule_id : list stm → stm → Prop :=
    | ill_rid_intro A : ill_rule_id [] ([A],A).

  Inductive ill_rule_unit_l : list stm → stm → Prop :=
    | ill_runit_l_intro Γ C : ill_rule_unit_l [(Γ,C)] (𝟙::Γ,C).

  Inductive ill_rule_unit_r : list stm → stm → Prop :=
    | ill_runit_r_intro : ill_rule_unit_r [] ([],𝟙).

  Inductive ill_rule_bot_l : list stm → stm → Prop :=
    | ill_rbot_l_intro Γ C : ill_rule_bot_l [] (⟘::Γ,C).

  Inductive ill_rule_top_r : list stm → stm → Prop :=
    | ill_rtop_r_intro Γ : ill_rule_top_r [] (Γ,⟙).

  Inductive ill_rule_times_l : list stm → stm → Prop :=
    | ill_rtimes_l_intro Γ A B C : ill_rule_times_l [(A::B::Γ,C)] (A⊗B::Γ,C).

  Inductive ill_rule_times_r : list stm → stm → Prop :=
    | ill_rtimes_r_intro Γ Δ A B : ill_rule_times_r [(Γ,A);(Δ,B)] (Γ++Δ,A⊗B).

  Inductive ill_rule_limp_l : list stm → stm → Prop :=
    | ill_rlimp_l_intro Γ Δ A B C : ill_rule_limp_l [(Γ,A);(B::Δ,C)] (A-⊗B::Γ++Δ,C).

  Inductive ill_rule_limp_r : list stm → stm → Prop :=
    | ill_rlimp_r_intro Γ A B : ill_rule_limp_r [(A::Γ,B)] (Γ,A-⊗B).

  Inductive ill_rule_with_l1 : list stm → stm → Prop :=
    | ill_rwith_l1_intro Γ A B C : ill_rule_with_l1 [(A::Γ,C)] (A&B::Γ,C).

  Inductive ill_rule_with_l2 : list stm → stm → Prop :=
    | ill_rwith_l2_intro Γ A B C : ill_rule_with_l2 [(B::Γ,C)] (A&B::Γ,C).

  Inductive ill_rule_with_r : list stm → stm → Prop := 
    | ill_rwith_r_intro Γ A B : ill_rule_with_r [(Γ,A);(Γ,B)] (Γ,A&B).

  (** Notice that the permutation rule is voluntarily excluded in ill_cf_rules *)
  Let ill_cf_rules := [ ill_rule_id
                      ; ill_rule_unit_l ; ill_rule_unit_r
                      ; ill_rule_bot_l
                      ; ill_rule_top_r 
                      ; ill_rule_times_l ; ill_rule_times_r 
                      ; ill_rule_limp_l ; ill_rule_limp_r
                      ; ill_rule_with_l1 ; ill_rule_with_l2 ; ill_rule_with_r ].
  Let ill_cf h c := ∃r, r h c ∧ In r ill_cf_rules.

  (** Now we add the permutation rule here *)
  Let E (c c' : stm) := fst c ~ₚ fst c' ∧ snd c = snd c'.
  Let ill_cf_perm h c := ill_cf h c ∨ ∃c', h = [c'] ∧ E c' c.

  Section equivalence.

    Hint Constructors ill_cut_free : core.

     Tactic Notation "solve" "with" "rule" constr(r) :=
     econstructor 1; [ left; exists r; split; [ econstructor; eauto | ] | ]; simpl; auto; firstorder.

    Local Lemma ill_cf_iff_rules Γ A : Γ ⊢ A ↔ provable ill_cf_perm (Γ,A).
    Proof.
      split.
      + induction 1.
        * solve with rule ill_rule_id.
        * (* The permutation rule has a special treatment *) 
          constructor 1 with [(Γ,A)].
          - right; eexists; unfold E; eauto.
          - constructor; auto.
        * solve with rule ill_rule_unit_l.
        * solve with rule ill_rule_unit_r.
        * solve with rule ill_rule_bot_l.
        * solve with rule ill_rule_top_r.
        * solve with rule ill_rule_times_l.
        * solve with rule ill_rule_times_r.
        * solve with rule ill_rule_limp_l.
        * solve with rule ill_rule_limp_r.
        * solve with rule ill_rule_with_l1.
        * solve with rule ill_rule_with_l2.
        * solve with rule ill_rule_with_r.
      + change A with (snd (Γ,A)) at 2.
        change Γ with (fst (Γ,A)) at 2.
        generalize (Γ,A).
        induction 1 as [ ? ? [ (r & H1 & Hr) | (c' & -> & ? & <-) ] ? H ].
        * unfold ill_cf_rules in Hr.
          split In Hr; destruct H1; simpl; split Forall; eauto.
        * apply Forall_cons_iff in H as []; eauto.
    Qed.

  End equivalence.

  Section decreasing.

    (** We show that reverse rule application for ill_cf is decreasing (hence well-founded) *)

    Local Fixpoint ill_form_weight (A : ill_form prop) :=
      match A with
      | ill_cst _ _   => 1
      | ill_var _     => 1
      | ill_bin _ A B => 1 + ill_form_weight A + ill_form_weight B
      end.

    Local Definition ill_list_weight := fold_right (λ x y, ill_form_weight x+y) 0.

    Local Fact ill_list_weight_perm Γ Δ : Γ ~ₚ Δ → ill_list_weight Γ = ill_list_weight Δ.
    Proof. induction 1; simpl; lia. Qed.

    Local Fact ill_list_weight_app Γ Δ : ill_list_weight (Γ++Δ) = ill_list_weight Γ + ill_list_weight Δ.
    Proof. induction Γ; simpl; lia. Qed.

    Local Definition ill_seq_weight '(Γ,A) := ill_list_weight Γ + ill_form_weight A.

    (* By strong induction on the weight *)
    Local Lemma instances_decr h c : ill_cf h c → Forall (λ x, ill_seq_weight x < ill_seq_weight c) h.
    Proof.
      intros (r & H1 & Hr).
      unfold ill_cf_rules in Hr.
      split In Hr; destruct H1; repeat apply Forall_cons; auto; simpl; try lia.
      all: try rewrite  ill_list_weight_app in *; try lia.
    Qed.

  End decreasing.

  Section finitary.

    (** We show that each individual rule of ill_cf is finitary *)

    Hint Resolve fin_t_cst_left fin_t_eq fin_t_empty fin_t_of_split fin_t_In
                 ill_list_form_eq_dec : core.

    Local Fact fin_t_ill_rule_id s : fin_t (λ l, ill_rule_id l s).
    Proof using prop_eq_dec.
      destruct s as (Γ,A).
      apply fin_t_equiv with (λ l, Γ = [A] ∧ l = []); auto.
      split.
      + intros []; subst; constructor.
      + now inversion 1.
    Qed.

    Local Fact fin_t_ill_rule_unit_l s : fin_t (λ l, ill_rule_unit_l l s).
    Proof.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, match Σ with 
                        | 𝟙::Γ => l = [(Γ,C)]
                        | _ => False 
                        end).
      + split.
        * destruct Σ as [ | [ | [] | ] ]; intros; now subst.
        * inversion 1; now subst.
      + destruct Σ as [ | [ | [] | ] ]; auto.
    Qed.

    Local Fact fin_t_ill_rule_unit_r s : fin_t (λ l, ill_rule_unit_r l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, Σ = [] ∧ C = 𝟙 ∧ l = []); auto.
      split.
      + intros (-> & -> & ->); constructor.
      + inversion 1; now subst.
    Qed.

    Local Fact fin_t_ill_rule_bot_l s : fin_t (λ l, ill_rule_bot_l l s).
    Proof.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, match Σ with 
                        | ⟘::Γ => l = []
                        | _    => False 
                        end).
      + split.
        * destruct Σ as [ | [ | [] | ] ]; intros; now subst.
        * inversion 1; now subst.
      + destruct Σ as [ | [ | [] | ] ]; auto.
    Qed.

    Local Fact fin_t_ill_rule_top_r s : fin_t (λ l, ill_rule_top_r l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, C = ⟙ ∧ l = []); auto.
      split.
      + intros (-> & ->); constructor.
      + inversion 1; now subst.
    Qed.

    Local Fact fin_t_ill_rule_times_l s : fin_t (λ l, ill_rule_times_l l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv 
        with (P := λ l, match Σ with 
                        | A⊗B::Γ => l = [(A::B::Γ,C)] 
                        | _   => False 
                        end).
      + split.
        * destruct Σ as [ | [ | [] | [] ] ]; intros; now subst.
        * inversion 1; now subst.
      + destruct Σ as [ | [ | [] | [] ] ]; now subst.
    Qed.

    Local Fact fin_t_ill_rule_times_r s : fin_t (λ l, ill_rule_times_r l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, match C with
                        | A⊗B => ∃ Γ Δ, Σ = Γ++Δ ∧ l = [(Γ,A);(Δ,B)]
                        | _   => False
                        end).
      + split.
        * destruct C as [ | | [] ]; simpl; try easy.
          intros (? & ? & []); now subst.
        * inversion 1; subst; eauto.
      + destruct C as [ | | [] ]; simpl; auto.
    Qed.

    Local Fact fin_t_ill_rule_limp_l s : fin_t (λ l, ill_rule_limp_l l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, match Σ with
                        | A-⊗B::Σ' => ∃ Γ Δ, Σ' = Γ++Δ ∧ l = [(Γ,A);(B::Δ,C)]
                        | _    => False
                        end).
      + split.
        * destruct Σ as [ | [ | [] | [] ] ]; try easy.
          now intros (? & ? & -> & ->).
        * inversion 1; subst; eauto.
      + destruct Σ as [ | [ | [] | [] ] ]; auto.
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
        with (P := λ l, match Σ with
                        | A&B::Γ => l = [(A::Γ,C)]
                        | _   => False
                        end).
      + split.
        * destruct Σ as [ | [ | [] | [] ] ]; intros; now subst.
        * inversion 1; now subst.
      + destruct Σ as [ | [ | [] | [] ] ]; auto.
    Qed.
    
    Local Fact fin_t_ill_rule_with_l2 s : fin_t (λ l, ill_rule_with_l2 l s).
    Proof using prop_eq_dec.
      destruct s as (Σ,C).
      apply fin_t_equiv
        with (P := λ l, match Σ with
                        | A&B::Γ => l = [(B::Γ,C)]
                        | _   => False
                        end).
      + split.
        * destruct Σ as [ | [ | [] | [] ] ]; intros; now subst.
        * inversion 1; now subst.
      + destruct Σ as [ | [ | [] | [] ] ]; auto.
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
                 fin_t_ill_rule_unit_l fin_t_ill_rule_unit_r
                 fin_t_ill_rule_bot_l
                 fin_t_ill_rule_top_r
                 fin_t_ill_rule_times_l fin_t_ill_rule_times_r
                 fin_t_ill_rule_limp_l fin_t_ill_rule_limp_r
                 fin_t_ill_rule_with_l1 fin_t_ill_rule_with_l2 fin_t_ill_rule_with_r : core.

    Local Lemma fin_t_instances c : fin_t (λ h, ill_cf h c).
    Proof using prop_eq_dec.
      apply fin_t_compose_In_t; auto.
      simpl; intros r Hr; unfold ill_cf_rules in Hr.
      split In_t Hr; auto.
    Qed.

  End finitary.
  
  Hint Constructors Permutation : core.
  Hint Resolve Permutation_sym ill_list_weight_perm : core.
  Hint Resolve fin_t_eq fin_t_perm' : core.
  Hint Resolve instances_decr fin_t_instances : core.

  Local Lemma prov_instances'_dec : ∀c, { provable ill_cf_perm c } + { ¬ provable ill_cf_perm c }.
  Proof using prop_eq_dec.
    apply provable_decr_fin_equiv_dec with (m := ill_seq_weight); eauto.
    + apply equivalence_product; split; red; eauto; intros; subst; auto.
    + intros [] [] []; simpl in *; subst; f_equal; auto.
    + intros (l,c); simpl; apply fin_t_prod with (P := λ x, x ~ₚ l) (Q := λ x, x = c); auto.
  Qed.

  (* We transport decidability along logical equivalence *)
  Theorem ill_cut_free_decidable Γ A : { Γ ⊢ A } + { ¬ Γ ⊢ A }.
  Proof using prop_eq_dec.
    destruct (prov_instances'_dec (Γ,A)); [ left | right ]; now rewrite ill_cf_iff_rules.
  Qed.

End ill_cut_free_decidable.

Check ill_cut_free_decidable.

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

  Hint Resolve sem_ill_form_closed sem_ill_list_form_closed : core.

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
    + simpl.
      apply inc_trans with (2 := IHill_cut_free).
      apply unit_neutral_1; eauto.
    + simpl; auto.
    + simpl.
      eapply inc_trans; [ eapply times_bot_distrib_r; eauto | apply bot_least; auto ].
    + simpl; auto.
    + simpl.
      apply inc_trans with (2 := IHill_cut_free); simpl.
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

  Variables (prop : Set).

  Let M := list (ill_form prop).

  Implicit Types (Γ : M) (X Y : M → Prop).
  
  Notation "l ⊢ x" := (@ill_cut_free prop l x).
  
  Let cl X Γ := ∀ Σ A, (∀Δ, X Δ → Δ++Σ ⊢ A)
                                → Γ++Σ ⊢ A.

  Fact cl_ill_cf_increase X : X ⊆ cl X.
  Proof. intros Γ HΓ Σ A H; now apply H. Qed.

  Fact cl_ill_cf_monotone X Y : X ⊆ Y → cl X ⊆ cl Y.
  Proof. intros HXY Γ HΓ Σ A H; apply HΓ; intros ? ?%HXY; auto. Qed.

  Fact cl_ill_cf_idempotent X : cl (cl X) ⊆ cl X.
  Proof. intros Γ HΓ Σ A H; apply HΓ; intros D HD; apply HD; auto. Qed.
  
  Hint Resolve cl_ill_cf_monotone cl_ill_cf_increase cl_ill_cf_idempotent : core.

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

  Fact cl_ill_cf_stable X Y : cl X ∘ cl Y ⊆ cl (X ∘ Y).
  Proof. apply cl_stable_lr_imp_stable; eauto. Qed.

  Local Fact cl_sg Γ : cl (sg Γ) Γ.
  Proof. apply cl_ill_cf_increase; eauto. Qed.

  Hint Resolve cl_sg : core.
  
  Hint Constructors Permutation : core.

  Fact cl_ill_cf_neutral_1 Γ : cl (sg e ∘ sg Γ) Γ.
  Proof. intros Σ A H; apply H; exists e Γ; red; auto. Qed.

  Fact cl_ill_cf_neutral_2 Γ : sg e ∘ sg Γ ⊆ cl (sg Γ).
  Proof. intros _ [ ? ? ? <- <- ?]; apply cl_perm with Γ; eauto. Qed.

  Fact cl_ill_cf_commute Γ Δ : sg Γ ∘ sg Δ ⊆ cl (sg Δ ∘ sg Γ).
  Proof.
    intros _ [ ? ? Θ <- <- H ]; red in H.
    apply cl_perm with (Δ ++ Γ); eauto.
    apply cl_ill_cf_increase; eauto.
    exists Δ Γ; try red; auto.
  Qed.

  Fact cl_ill_cf_associative Γ Δ Θ : sg Γ ∘ (sg Δ ∘ sg Θ) ⊆ cl ((sg Γ ∘ sg Δ) ∘ sg Θ).
  Proof.
    intros _ [ _ _ D <- [ _ _ C <- <- H1 ] H2 ].
    apply cl_perm with ((Γ ++ Δ) ++ Θ); auto.
    + red in H1, H2; rewrite <- app_assoc; eauto.
    + apply cl_ill_cf_increase.
      exists (Γ ++ Δ) Θ; try red; auto.
      exists Γ Δ; try red; auto.
  Qed.

  Let dwncl A Γ := Γ ⊢ A.
  Abbreviation φ := (λ v, dwncl (ill_var v)).
  Let sem_form :=  sem_ill_form cl comp e φ.
  Let sem_list := sem_ill_list_form cl comp e sem_form.

  Fact dwncl_ill_cf_closed A : cl (dwncl A) ⊆ dwncl A.
  Proof. intros ? H; rewrite <- app_nil_r; apply (H []); intro; rewrite app_nil_r; auto. Qed.

  Hint Resolve cl_ill_cf_neutral_1 cl_ill_cf_neutral_2
               cl_ill_cf_associative cl_ill_cf_commute 
               cl_ill_cf_stable 
               dwncl_ill_cf_closed : core.

  Local Fact sem_form_is_closed A : cl (sem_form A) ⊆ sem_form A.
  Proof. apply sem_ill_form_closed; eauto. Qed.

  Hint Resolve sem_form_is_closed : core.

  Local Fact sem_list_is_closed Γ : cl (sem_list Γ) ⊆ sem_list Γ.
  Proof. apply sem_ill_list_form_closed; eauto. Qed.

  Hint Resolve sem_list_is_closed : core.

  Import ILL_notations.
  
  Hint Constructors ill_cut_free : core.

  Local Fact cl_unit_l : cl (sg e) [𝟙].
  Proof. intros ? ? H; apply ill_cf_unit_l, (H []); auto. Qed.

  Local Fact dwncl_unit_r : sg [] ⊆ dwncl 𝟙.
  Proof. apply sg_inc, ill_cf_unit_r. Qed.

  Local Fact cl_bot_l : cl (λ _, False) [⟘].
  Proof. intros ? ? ?; apply ill_cf_bot_l. Qed.

  Local Fact cl_times_l A B : cl (sg [A;B]) [A⊗B].
  Proof. intros ? ? H; apply ill_cf_times_l, (H [_;_]); auto. Qed.

  Local Fact dwncl_times_r A B :  dwncl A ∘ dwncl B ⊆ dwncl (A⊗B).
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

  Local Fact dwncl_impl_r A B : sg [A] ⊸ dwncl B ⊆ dwncl (A-⊗B).
  Proof. intros G HG; apply ill_cf_limp_r, HG; exists [A] G; try red; auto. Qed.

  Local Fact cl_with_l1 A B : cl (sg [A]) [A&B].
  Proof. intros ? ? H; apply ill_cf_with_l1, (H [_]); auto. Qed.

  Local Fact cl_with_l2 A B : cl (sg [B]) [A&B].
  Proof. intros ? ? H; apply ill_cf_with_l2, (H [_]); auto. Qed.

  Local Fact dwncl_with_r A B :  dwncl A ∩ dwncl B ⊆ dwncl (A&B).
  Proof. intros ? []; apply ill_cf_with_r; auto. Qed. 

  Hint Resolve composes_monotone : core.

  Local Lemma sem_form_Okada A :
      sem_form A [A]
    ∧ sem_form A ⊆ dwncl A.
  Proof.
    induction A as [ v
                   | [] 
                   | [] A [] B [] ]; simpl; split; trivial.
    + apply ill_cf_ax.
    + apply cl_unit_l.
    + apply cl_closed; eauto using dwncl_unit_r.
    + apply cl_bot_l.
    + apply cl_closed; now eauto.
    + intros G _; apply ill_cf_top_r.
    + split.
      * generalize (@cl_with_l1 A B).
        apply cl_closed; eauto.
        now apply sg_inc.
      * generalize (@cl_with_l2 A B).
        apply cl_closed; eauto.
        now apply sg_inc.
    + intros ? []; apply dwncl_with_r; auto.
    + apply magicwand_monotone with (3 := @cl_impl_l _ _); auto; apply cl_closed; eauto; now apply sg_inc.
    + apply inc_trans with (2 := @dwncl_impl_r _ _); apply magicwand_monotone; auto; now apply sg_inc.
    + apply cl_ill_cf_monotone with (2 := @cl_times_l _ _), sg_inc; econstructor; eauto; red; auto.
    + apply cl_closed; eauto; apply inc_trans with (2 := @dwncl_times_r _ _); eauto.
  Qed.

  Local Corollary sem_list_Okada Γ : sem_list Γ Γ.
  Proof.
    induction Γ as [ | ]; simpl; auto using cl_ill_cf_increase.
    apply cl_ill_cf_increase; eexists _ _; eauto; [ eapply sem_form_Okada | ].
    constructor; auto.
  Qed.

  Theorem ill_cut_free_completeness Γ A : sem_list Γ ⊆ sem_form A → Γ ⊢ A.
  Proof. intros H; apply sem_form_Okada, H, sem_list_Okada. Qed.
  
  Theorem ill_form_cut_free_completeness A : sem_form A e → [] ⊢ A.
  Proof.
    intros H; apply ill_cut_free_completeness.
    simpl.
    apply cl_closed; eauto.
    apply sg_inc; auto.
  Qed.

End ill_cut_free_completeness.

Check ill_form_cut_free_completeness.


  



  