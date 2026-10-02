(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation Arith Lia Utf8.

From Undecidability.Shared
  Require Import fin_base utils_list.

Set Implicit Arguments.

Import ListNotations.

Local Infix "~ₚ" := (@Permutation _) (at level 70).

Fact fin_t_empty X : fin_t (λ _ : X, False).
Proof. exists []; simpl; tauto. Qed.

Fact fin_t_In X (l : list X) : fin_t (λ x, In x l).
Proof. now exists l. Qed.

Fact fin_t_eq X (x : X) : fin_t (λ y, y = x).
Proof. exists [x]; simpl; firstorder. Qed.

Fact fin_t_lt n : fin_t (λ i, i < n).
Proof.
  apply fin_t_equiv with (P := fun x => In x (list_an 0 n)).
  + intro; rewrite list_an_spec; lia.
  + apply fin_t_In.
Qed.

Fact fin_t_bin_union X (P Q : X → Prop) :
  fin_t P → fin_t Q → fin_t (λ x, P x ∨ Q x).
Proof.
  intros (l & Hl) (m & Hm); exists (l++m).
  intro; now rewrite in_app_iff, Hl, Hm.
Qed.

#[local] Hint Resolve fin_t_empty fin_t_bin_union : core.

Inductive In_t {X} (x : X) : list X → Type :=
  | In_t_left l : In_t x (x::l)
  | In_t_right y l : In_t x l → In_t x (y::l).

#[local] Hint Constructors In_t : core.

Fact In_t__In X (x : X) l : In_t x l → In x l.
Proof. induction 1; simpl; eauto. Qed.

Fact In_t_inv X (x : X) l :
    In_t x l
  → match l return Type with 
    | []   => False
    | y::l => ((y = x) + In_t x l)%type
    end.
Proof. destruct 1; auto. Qed. 

Section fin_t_compose_In_t.

  Variable (X Y : Type) (R : X → Y → Prop).

  (** A very useful lemma to compose finitary relations *)

  Lemma fin_t_compose_In_t l :
      (∀x, In_t x l → fin_t (R x))
    → fin_t (λ y, ∃ x, R x y ∧ In x l).
  Proof.
    induction l as [ | x l IHl ].
    + intros _; apply fin_t_equiv with (λ _, False); auto.
      simpl; firstorder.
    + intros H.
      apply fin_t_equiv with (λ y, (∃x', R x' y ∧ In x' l) ∨ R x y).
      * split.
        - intros [ (? & []) | ]; eexists; simpl; eauto.
        - intros (? & ? & [ |]); subst; eauto.
      * apply fin_t_bin_union; eauto.
  Qed.  

End fin_t_compose_In_t.

Section fin_compose.

  Variable (X Y : Type) (R : X → Y → Prop) (P : Y → Prop).

  (** A very useful lemma to compose finitary relations *)

  Lemma fin_t_compose :
             (∀y, P y → fin_t (λ x, R x y))
           → fin_t P
           → fin_t (λ x, ∃ y, R x y ∧ P y).
  Proof.
    intros H (lP & HP).
    apply fin_t_equiv with (λ y, ∃ x, R y x ∧ In x lP).
    + firstorder.
    + apply fin_t_compose_In_t.
      intros ? ?%In_t__In%HP; auto.
  Qed.

End fin_compose.

Fact fin_t_idx_union X n (R : nat → X → Prop) : 
          (∀i, i < n → fin_t (R i))
        → fin_t (λ y, ∃i, R i y ∧ i < n).
Proof. intro; apply fin_t_compose; auto using fin_t_lt. Qed.

Fact fin_t_cst_left X P (Q : X → Prop) :
    { P } + { ~ P }
  → fin_t Q
  → fin_t (λ x, P ∧ Q x).
Proof.
  intros [H|H].
  + apply fin_t_equiv; tauto.
  + intro; apply fin_t_equiv with (2 := fin_t_empty _); tauto.
Qed.

Fact fin_t_cons X (l : list X) : fin_t (λ p, l = fst p :: snd p).
Proof.
  destruct l as [ | x l ].
  + now apply fin_t_equiv with (2 := fin_t_empty _).
  + apply fin_t_equiv with (2 := fin_t_eq (x,l)).
    intros []; simpl; split.
    * intros [=]; subst; auto.
    * now inversion 1.
Qed.

Fact fin_t_split X (l : list X) : fin_t (λ p, l = fst p ++ snd p).
Proof.
  induction l as [ | x l (ll & Hll) ].
  + apply fin_t_equiv with (2 := fin_t_eq ([],[])).
    intros (l,m); simpl; split.
    * now inversion 1.
    * intros []%eq_sym%app_eq_nil; subst; auto.
  + exists (([],x::l)::(map (fun '(p,q) => (x::p,q)) ll)).
    intros ([ | y p ],q); simpl; split.
    * intros <-; simpl; auto.
    * intros [ [=] | ([] & [=] & _)%in_map_iff ]; auto.
    * intros [=]; subst; right; apply in_map_iff; exists (p,q); rewrite <- Hll; now simpl.
    * intros [ [=] | ([] & [=] & ?%Hll)%in_map_iff ]; subst; now simpl.
Qed.

#[local] Hint Resolve fin_t_split fin_t_cons fin_t_eq : core.

Fact fin_t_of_split X Y (l : list X) (R : list X → list X → Y → Prop) :
    (∀ m p, l = m++p → fin_t (R m p))
  → fin_t (λ y, ∃ m p, l = m++p ∧ R m p y).
Proof.
  intros H.
  apply fin_t_equiv
    with (P := λ y, ∃p, R (fst p) (snd p) y
                    ∧ l = fst p++snd p).
  + intros y; split.
    * intros ([] & ? & ->); simpl in *; eauto.
    * intros (m & p & []); exists (m,p); eauto.
  + apply fin_t_compose; auto.
Qed.

Fact fin_t_perm X (l : list X) : fin_t (λ m, l ~ₚ m).
Proof.
  induction l as [ | x l IH ].
  + apply fin_t_equiv with (2 := fin_t_eq []); split.
    * intros ->; auto.
    * now intros ?%Permutation_nil.
  + apply fin_t_equiv 
      with (P := λ m, ∃p, m = fst p++[x]++snd p 
                      ∧ ∃k, k = fst p++snd p ∧ l ~ₚ k).
    * intros m; split.
      - intros ([] & ? & ? & ? & ?); subst; simpl in *;
          auto using Permutation_cons_app.
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

Fact fin_t_perm' X (l : list X) : fin_t (λ m, m ~ₚ l).
Proof.
  apply fin_t_equiv with (Permutation l); auto.
  split; auto using Permutation_sym.
Qed.

Fact fin_t_perm_head X Y (l : list X) (R : X → list X → Y → Prop) :
    (∀ x m, l ~ₚ x::m → fin_t (R x m))
  → fin_t (λ y, ∃ x m, l ~ₚ x::m ∧ R x m y).
Proof.
  intros H.
  apply fin_t_equiv
    with (P := λ y, ∃p, R (fst p) (snd p) y 
                    ∧ ∃k, k = fst p::snd p ∧ l ~ₚ k).
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
  apply fin_t_equiv
    with (P := λ y, ∃p, R (fst p) (snd p) y
                    ∧ ∃k, k = fst p++snd p ∧ l ~ₚ k).
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
  apply fin_t_equiv
    with (P := λ y, ∃ x m, l ~ₚ x::m 
                    ∧ ∃k, R x (fst k) (snd k) y ∧ m = fst k++snd k ).
  + intros y; split.
    * intros (x & m & ? & (p,q) & ? & ->); simpl in *; eauto.
    * intros (x & m & p & ? & ?); exists x, (m++p); split; auto; exists (m,p); simpl; auto.
  + apply fin_t_perm_head.
    intros ? ? ?.
    apply fin_t_compose; auto.
    intros ? ->; auto.
Qed. 
