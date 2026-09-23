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
  Require Import decidable.
  
From Undecidability.Shared
  Require Import measure_ind fin_base utils_list.

Set Implicit Arguments.

Import ListNotations.

Local Infix "~ₚ" := (@Permutation _) (at level 70).

Fact fin_t_In X (l : list X) : fin_t (λ x, In x l).
Proof. now exists l. Qed.

Section fin_compose.

  Variable (X Y : Type) (R : X → Y → Prop) (P : Y → Prop).

  (** A very useful lemma to compose finitary relations *)

  Lemma fin_t_compose :
             (∀y, P y → fin_t (λ x, R x y))
           → fin_t P
           → fin_t (λ x, ∃ y, R x y ∧ P y).
  Proof.
    intros H (lP & HP).
    apply fin_t_equiv with (fun x => exists y, R x y /\ In y lP).
    + intros x; split; intros (y & Hy); exists y; revert Hy; rewrite HP; auto.
    + cut (forall y, In y lP -> fin_t (fun x => R x y)).
      2: intros; apply H, HP; auto.
      clear P HP H.
      induction lP as [ | y lP IHlP ]; intros H.
      * exists nil; intros k; split.
        - intros (? & _ & []).
        - intros [].
      * destruct IHlP as (ll & Hll).
        - intros; apply H; simpl; auto.
        - destruct (H y) as (l & Hl); simpl; auto.
          exists (l++ll); intros x; rewrite in_app_iff, <- Hl, <- Hll.
          split.
          ++ intros (y' & H1 & [ <- | H2 ]); auto.
             right; exists y'; auto.
          ++ intros [ | (y' & ? & ?) ].
             ** exists y; auto.
             ** exists y'; auto.
  Qed.

End fin_compose.

Fact fin_t_idx_union X n (R : nat → X → Prop) : 
          (∀i, i < n → fin_t (R i))
        → fin_t (λ y, ∃i, R i y ∧ i < n).
Proof.
  intros H; apply fin_t_compose; auto.
  apply fin_t_equiv with (P := fun x => In x (list_an 0 n)).
  + intro; rewrite list_an_spec; lia.
  + apply fin_t_In.
Qed.

Fact fin_t_empty X : fin_t (λ _ : X, False).
Proof. exists []; simpl; tauto. Qed.

Fact fin_t_cst_left X P (Q : X → Prop) : { P } + { ~ P } → fin_t Q → fin_t (λ x, P ∧ Q x).
Proof.
  intros [H|H].
  + apply fin_t_equiv; tauto.
  + intros _; apply fin_t_equiv with (P := fun _ => False).
    * tauto.
    * apply fin_t_empty.
Qed.

Fact fin_t_eq X (x : X) : fin_t (λ y, y = x).
Proof. exists [x]; simpl; firstorder. Qed.

Fact fin_t_cons X (l : list X) : fin_t (λ p, l = fst p :: snd p).
Proof.
  destruct l as [ | x l ].
  + now apply fin_t_equiv with (2 := fin_t_empty _).
  + exists [(x,l)].
    intros []; simpl; split.
    * intros [=]; subst; auto.
    * intros [ [=] | [] ]; subst; auto.
Qed.

Fact fin_t_split X (l : list X) : fin_t (λ p, l = fst p ++ snd p).
Proof.
  induction l as [ | x l (ll & Hll) ].
  + exists [([],[])]; intros (l,m); simpl; split.
    * intros []%eq_sym%app_eq_nil; subst; auto.
    * intros [ [=] | [] ]; now subst.
  + exists (([],x::l)::(map (fun '(p,q) => (x::p,q)) ll)).
    intros ([ | y p ],q); simpl; split.
    * intros <-; simpl; auto.
    * intros [ [=] | ([] & [=] & _)%in_map_iff ]; auto.
    * intros [=]; subst; right; apply in_map_iff; exists (p,q); rewrite <- Hll; now simpl.
    * intros [ [=] | ([] & [=] & ?%Hll)%in_map_iff ]; subst; now simpl.
Qed.

#[local] Hint Resolve fin_t_split fin_t_cons fin_t_eq : core.

Fact fin_t_perm X (l : list X) : fin_t (λ m, l ~ₚ m).
Proof.
  induction l as [ | x l IH ].
  + exists [[]]; simpl; split.
    * intros ->%Permutation_nil; auto.
    * intros [ [] | [] ]; auto.
  + apply fin_t_equiv with (P := λ m, exists p, m = fst p++[x]++snd p /\ exists k, k = fst p++snd p /\ l ~ₚ k).
    * intros m; split.
      - intros ([] & ? & ? & ? & ?); subst; simpl in *; auto using Permutation_cons_app.
      - intros H.
        destruct (in_split x m) as (p & q & ->).
        ++ apply Permutation_in with (1 := H); simpl; auto.
        ++ apply Permutation_cons_app_inv in H.
           exists (p,q); simpl; eauto.
    * apply fin_t_compose.
      - intros [] _; auto.
      - apply fin_t_compose; auto.
Qed.

#[local] Hint Resolve fin_t_perm : core.

Fact fin_t_perm_head X Y (l : list X) (R : X → list X → Y → Prop) :
    (∀ x m, l ~ₚ x::m → fin_t (R x m))
  → fin_t (λ y, ∃ x m, l ~ₚ x::m ∧ R x m y).
Proof.
  intros H.
  apply fin_t_equiv with (P := λ y, ∃ p, R (fst p) (snd p) y ∧ exists k, k = fst p::snd p /\ l ~ₚ k).
  + intros y; split.
    * intros ([] & ? & ? & -> & ?); simpl in *; eauto.
    * intros (x & m & []); exists (x,m); eauto.
  + apply fin_t_compose.
    * intros [] E; apply H.
      now destruct E as (? & -> & ?).
    * apply fin_t_compose; auto.
Qed.

Fact fin_t_perm_split X Y (l : list X) (R : list X → list X → Y → Prop) :
    (∀ m p, l ~ₚ m++p → fin_t (R m p))
  → fin_t (λ y, ∃ m p, l ~ₚ m++p ∧ R m p y).
Proof.
  intros H.
  apply fin_t_equiv with (P := λ y, ∃ p, R (fst p) (snd p) y ∧ exists k, k = fst p++snd p /\ l ~ₚ k).
  + intros y; split.
    * intros ([] & ? & ? & -> & ?); simpl in *; eauto.
    * intros (x & m & []); exists (x,m); eauto.
  + apply fin_t_compose.
    * intros [] E; apply H.
      now destruct E as (? & -> & ?).
    * apply fin_t_compose; auto.
Qed.

Fact fin_t_perm_head_split X Y (l : list X) (R : X → list X → list X → Y → Prop) :
    (∀ x m p, l ~ₚ x::m++p → fin_t (R x m p))
  → fin_t (λ y, ∃ x m p, l ~ₚ x::m++p ∧ R x m p y).
Proof.
  intros H.
  apply fin_t_equiv with (P := λ y, ∃ x m, l ~ₚ x::m ∧ exists k, R x (fst k) (snd k) y /\ m = fst k++snd k ).
  + intros y; split.
    * intros (x & m & ? & (p,q) & ? & ->); simpl in *; eauto.
    * intros (x & m & p & ? & ?); exists x, (m++p); split; auto; exists (m,p); simpl; auto.
  + apply fin_t_perm_head.
    intros ? ? ?.
    apply fin_t_compose; auto.
    intros ? ->; auto.
Qed. 

(** Intuionistic Linear Logic, the ⊗, ⊸ and & fragment with constants *)

Section syntax.

  Variables (prop : Set).

  Inductive ill_connective := ill_with | ill_limp | ill_times.
  Inductive ill_constant := ill_unit | ill_bot | ill_top.

  Inductive ill_form : Set :=
    | ill_var  : prop → ill_form
    | ill_cst  : ill_constant → ill_form
    | ill_bin  : ill_connective → ill_form → ill_form → ill_form.

End syntax.

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  !   ‼  ∅  ⊢ *)

Module ILL_notations.

  Notation "⟙" := (ill_cst ill_top).
  Notation "⟘" := (ill_cst ill_bot).
  Notation "𝟙" := (ill_cst ill_unit).

  Infix "&" := (ill_bin ill_with) (at level 50).
  Infix "⊗" := (ill_bin ill_times) (at level 50).
  Infix "⊸" := (ill_bin ill_limp) (at level 51, right associativity).

  Notation "£" := ill_var.

  Notation "∅" := nil (only parsing).

End ILL_notations.

Import ILL_notations.

#[local] Reserved Notation "l '⊢' x" (at level 70, no associativity).
#[local] Reserved Notation "l '⊢ₚ' x" (at level 70, no associativity).

Section ill_cut_free.

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
             A⊸B::Γ++Δ ⊢ C

    | ill_cf_limp_r Γ A B :

               A::Γ ⊢ B
    → (*-----------------------------*)
               Γ ⊢ A⊸B

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

         Σ ~ₚ A⊸B::Γ++Δ → Γ ⊢ₚ A → B::Δ ⊢ₚ C
    → (*-----------------------------*)
             Σ ⊢ₚ C

    | ill_cfp_limp_r Γ A B :
 
               A::Γ ⊢ₚ B
    → (*-----------------------------*)
               Γ ⊢ₚ A⊸B

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

  Variables (prop : Set) (prop_eq_dec : ∀ v w : prop, { v = w } + { v <> w }).

  Fact ill_form_eq_dec (A B : ill_form prop) : { A = B } + { A ≠ B }.
  Proof using prop_eq_dec. decide equality; auto; decide equality. Qed.

  Hint Resolve ill_form_eq_dec : core.

  Local Fact ill_list_form_eq_dec (l m : list (ill_form prop)) : { l = m } + { l ≠ m }.
  Proof using prop_eq_dec. apply list_eq_dec; auto. Qed.

  Let stm := (list (ill_form prop) * ill_form prop)%type. 

  Inductive ill_rule_id : list stm → stm → Prop :=
    | ill_rid_intro A : ill_rule_id [] ([A],A).

  Inductive ill_rule_times_l : list stm → stm → Prop :=
    | ill_rtimes_l_intro Γ Σ A B C : Σ ~ₚ A⊗B::Γ → ill_rule_times_l [(A::B::Γ,C)] (Σ,C).

  Inductive ill_rule_times_r : list stm → stm → Prop :=
    | ill_rtimes_r_intro Γ Δ Σ A B : Σ ~ₚ Γ++Δ → ill_rule_times_r [(Γ,A);(Δ,B)] (Σ,A⊗B).

  Inductive ill_rule_limp_l : list stm → stm → Prop :=
    | ill_rlimp_l_intro Γ Δ Σ A B C :  Σ ~ₚ A⊸B::Γ++Δ → ill_rule_limp_l [(Γ,A);(B::Δ,C)] (Σ,C).

  Inductive ill_rule_limp_r : list stm → stm → Prop :=
    | ill_rlimp_r_intro Γ A B : ill_rule_limp_r [(A::Γ,B)] (Γ,A⊸B).

  Inductive ill_rule_with_l1 : list stm → stm → Prop :=
    | ill_rwith_l1_intro Γ Σ A B C : Σ ~ₚ A&B::Γ → ill_rule_with_l1 [(A::Γ,C)] (Σ,C).

  Inductive ill_rule_with_l2 : list stm → stm → Prop :=
    | ill_rwith_l2_intro Γ Σ A B C : Σ ~ₚ A&B::Γ → ill_rule_with_l2 [(B::Γ,C)] (Σ,C).

  Inductive ill_rule_with_r : list stm → stm → Prop := 
    | ill_rwith_r_intro Γ A B : ill_rule_with_r [(Γ,A);(Γ,B)] (Γ,A&B).

 (* Let ill_rules := [ill_rule_id;ill_rule_times_l;ill_rule_times_r;ill_rule_limp_l;ill_rule_limp_r;ill_rule_with_l1;ill_rule_with_l2;ill_rule_with_r]. *)
  
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

  Hint Constructors ill_cut_free_perm : core.

  Notation "l ⊢ₚ x" := (@ill_cut_free_perm prop l x).
  
  (* Automation helps a lot ... *)
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

  Local Fixpoint ill_form_weight (A : ill_form prop) :=
    match A with
    | ill_cst _ _ => 1
    | ill_var _ => 1
    | ill_bin _ A B => 1 + ill_form_weight A + ill_form_weight B
    end.

  Local Definition ill_list_weight Γ := fold_right (fun x y => ill_form_weight x+y) 0 Γ.

  Local Fact ill_list_weight_perm Γ Δ : Γ ~ₚ Δ → ill_list_weight Γ = ill_list_weight Δ.
  Proof. induction 1; simpl; lia. Qed.

  Local Fact ill_list_weight_app Γ Δ : ill_list_weight (Γ++Δ) = ill_list_weight Γ + ill_list_weight Δ.
  Proof. induction Γ; simpl; lia. Qed.

  Local Definition ill_seq_weight '(Γ,A) := ill_list_weight Γ + ill_form_weight A.
  
  Hint Resolve fin_t_cst_left fin_t_eq ill_list_form_eq_dec : core.
  
  Local Fact fin_t_ill_rule_id s : fin_t (λ l, ill_rule_id l s).
  Proof using prop_eq_dec.
    destruct s as (Γ,A).
    apply fin_t_equiv with (λ l, Γ = [A] /\ l = []).
    + intros ?; split.
      * intros []; subst; constructor.
      * now inversion 1.
    + apply fin_t_cst_left; auto.
  Qed.

  Hint Resolve fin_t_empty : core.

  Local Fact fin_t_ill_rule_times_l s : fin_t (λ l, ill_rule_times_l l s).
  Proof using prop_eq_dec.
    destruct s as (Σ,C).
    apply fin_t_equiv with (P := λ l, exists D Γ, Σ ~ₚ D::Γ /\ match D with A⊗B => l = [(A::B::Γ,C)] | _ => False end).
    + intros h; split.
      * intros ([ | | [] ] & ? & []); now subst.
      * inversion 1; subst; do 2 eexists; split; simpl; eauto; now simpl.  
    + apply fin_t_perm_head.
      intros [ | | [] ] Γ E; simpl; auto.
  Qed.

  Local Fact fin_t_ill_rule_times_r s : fin_t (λ l, ill_rule_times_r l s).
  Proof using prop_eq_dec.
    destruct s as (Σ,C).
    apply fin_t_equiv with (P := λ l, match C with A⊗B => exists Γ Δ, Σ ~ₚ Γ++Δ /\ l = [(Γ,A);(Δ,B)] | _ => False end).
    + intros h; split.
      * destruct C as [ | | [] ]; simpl; try easy.
        intros (? & ? & []); now subst.
      * inversion 1; subst; eauto.
    + destruct C as [ | | [] ]; simpl; auto.
      apply fin_t_perm_split; auto.
  Qed.

  Local Fact fin_t_ill_rule_limp_l s : fin_t (λ l, ill_rule_limp_l l s).
  Proof using prop_eq_dec.
    destruct s as (Σ,C).
    apply fin_t_equiv with (P := λ l, exists D Γ Δ, Σ ~ₚ D::Γ++Δ /\ match D with A⊸B => l = [(Γ,A);(B::Δ,C)] | _ => False end).
    + intros h; split.
      * intros ([ | | [] ] & ? & ? & []); now subst.
      * inversion 1; subst; do 3 eexists; split; simpl; eauto; now simpl.  
    + apply fin_t_perm_head_split.
      intros [ | | [] ] Γ E; simpl; auto.
  Qed.
  
  Local Fact fin_t_ill_rule_limp_r s : fin_t (λ l, ill_rule_limp_r l s).
  Proof using prop_eq_dec.
    destruct s as (Σ,C).
    apply fin_t_equiv with (P := λ l, match C with A⊸B => l = [(A::Σ,B)] | _ => False end).
    + intros h; split.
      * destruct C as [ | | [] ]; simpl; intros; now subst.
      * inversion 1; subst; eauto.
    + destruct C as [ | | [] ]; simpl; auto.
  Qed.
  
  Local Fact fin_t_ill_rule_with_l1 s : fin_t (λ l, ill_rule_with_l1 l s).
  Proof using prop_eq_dec.
    destruct s as (Σ,C).
    apply fin_t_equiv with (P := λ l, exists D Γ, Σ ~ₚ D::Γ /\ match D with A&B => l = [(A::Γ,C)] | _ => False end).
    + intros h; split.
      * intros ([ | | [] ] & ? & []); try easy; subst; econstructor; eauto.
      * inversion 1; subst; do 2 eexists; split; simpl; eauto; now simpl.  
    + apply fin_t_perm_head.
      intros [ | | [] ] Γ E; simpl; auto.
  Qed.
  
  Local Fact fin_t_ill_rule_with_l2 s : fin_t (λ l, ill_rule_with_l2 l s).
  Proof using prop_eq_dec.
    destruct s as (Σ,C).
    apply fin_t_equiv with (P := λ l, exists D Γ, Σ ~ₚ D::Γ /\ match D with A&B => l = [(B::Γ,C)] | _ => False end).
    + intros h; split.
      * intros ([ | | [] ] & ? & []); try easy; subst; econstructor; eauto.
      * inversion 1; subst; do 2 eexists; split; simpl; eauto; now simpl.  
    + apply fin_t_perm_head.
      intros [ | | [] ] Γ E; simpl; auto.
  Qed.
  
  Local Fact fin_t_ill_rule_with_r s : fin_t (λ l, ill_rule_with_r l s).
  Proof using prop_eq_dec.
    destruct s as (Σ,C).
    apply fin_t_equiv with (P := λ l, match C with A&B => l = [(Σ,A);(Σ,B)] | _ => False end).
    + intros h; split.
      * destruct C as [ | | [] ]; simpl; intros; now subst.
      * inversion 1; subst; eauto.
    + destruct C as [ | | [] ]; simpl; auto.
  Qed.

  Hint Resolve fin_t_ill_rule_id
               fin_t_ill_rule_times_l fin_t_ill_rule_times_r
               fin_t_ill_rule_limp_l fin_t_ill_rule_limp_r
               fin_t_ill_rule_with_l1 fin_t_ill_rule_with_l2 fin_t_ill_rule_with_r : core.

  Local Lemma ill_instances_dec : ∀s, { provable instances s } + { ¬ provable instances s }.
  Proof using prop_eq_dec.
    apply provable_wf_fin_dec.
    + intros s; induction on s as IH with measure (ill_seq_weight s).
      constructor; intros c (h & ((n & Hn & _) & H3)).
      apply IH; clear IH.
      do 7 (try destruct n as [|n]); destruct Hn; simpl in H3;
        split disj eqs H3; simpl.
      all: try match goal with H: _ ~ₚ _ |- _ => apply ill_list_weight_perm in H; simpl in H end; try lia.
      all: try rewrite  ill_list_weight_app in *; try lia.
    + intros c.
      apply fin_t_idx_union.
      intros n _; do 7 (try destruct n as [|n]); simpl; auto.
  Qed.

  Notation "l ⊢ x" := (@ill_cut_free prop l x).

  Theorem iff_cut_free_decidable Γ A : { Γ ⊢ A } + { ¬ Γ ⊢ A }.
  Proof using prop_eq_dec.
    destruct (ill_instances_dec (Γ,A)) as [ H | H ]; [ left | right ];
      rewrite <- ill_cf_iff_cfp, ill_cfp_iff_rules; trivial.
  Qed.
  
End ill_cfp_dec.

Check iff_cut_free_decidable.

  