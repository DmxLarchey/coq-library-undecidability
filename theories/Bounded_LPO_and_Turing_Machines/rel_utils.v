(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia.

Set Implicit Arguments.

#[global] Reserved Notation "M '//' s '-1>' t" (at level 70, format "M  //  s  -1>  t").
#[global] Reserved Notation "M '//' s '-[' n ']->' t" (at level 70, format "M  //  s  -[ n ]->  t").
#[global] Reserved Notation "M '//' s '->>' t" (at level 70, format "M  //  s  ->>  t").
#[global] Reserved Notation "M '//' s '~~>' t" (at level 70, format "M  //  s  ~~>  t").

Definition functional {X Y} (R : X -> Y -> Prop) :=
  forall x y₁ y₂, R x y₁ -> R x y₂ -> y₁ = y₂.

Section rel_iter.

  Variable (X : Type). 

  Implicit Type (R : X -> X -> Prop).

  Fixpoint rel_iter R n :=
    match n with 
      | 0   => eq
      | S n => fun x y => exists z, R x z /\ R // z -[n]-> y
    end
  where "R // x -[ n ]-> y" := (rel_iter R n x y).

  Variable (R : X -> X -> Prop).

  Fact rel_iter_1 x y : R // x -[1]-> y <-> R x y.
  Proof. simpl; firstorder; subst; auto. Qed.

  Fact rel_iter_plus a b x y : R // x -[a+b]-> y <-> exists z, R // x -[a]-> z /\ R // z -[b]-> y.
  Proof.
    revert x y; induction a as [ | a IHa ]; intros x y; simpl.
    + firstorder; subst; auto.
    + split.
      * intros (z & H1 & H2).
        apply IHa in H2 as (k & H2 & H3).
        exists k; split; auto; exists z; auto.
      * intros (z & (k & H1 & H2) & H3).
        exists k; split; auto.
        apply IHa; eauto.
  Qed.

  Hypothesis next : forall x, { y | R x y } + { forall y, ~ R x y }.

  Fact rel_iter_next n x : { y | R // x -[n]-> y } + { y : _ & { m | m < n /\ R // x -[m]-> y /\ forall z, ~ R y z } }.
  Proof.
    revert x; induction n as [ | n IHn ]; intros x.
    + left; exists x; red; simpl; auto.
    + destruct (next x) as [ (y & Hy) | H ].
      * destruct (IHn y) as [ (z & Hz) | (z & m & H1 & H2 & H3) ].
        - left; exists z, y; auto.
        - right; exists z, (S m); split; try lia; split; auto.
          exists y; auto.
      * right; exists x, 0; repeat split; auto; lia.
  Qed.

  Let Fixpoint norm_Acc x (D : Acc (fun x y => R y x) x) : { y : _ & { n | R // x -[n]-> y /\ forall z, ~ R y z } }.
  Proof.
    destruct (next x) as [ (y & Hy) | Hx ].
    + destruct (norm_Acc y) as (z & n & H1 & H2).
      * apply Acc_inv with (1 := D), Hy.
      * exists z, (S n); split; auto; exists y; auto.
    + exists x, 0; simpl; auto.
  Qed.

  Hypothesis Rfun : functional R.

  Fact rel_iter_fun n : functional (rel_iter R n).
  Proof.
    induction n as [ | n IHn ]; intros x y1 y2; simpl.
    + intros; subst; auto.
    + intros (z1 & H1 & H2) (z2 & H3 & H4).
      generalize (Rfun H1 H3); intros; subst.
      revert H2 H4; apply IHn.
  Qed.

  Fact rel_iter_fun_no_further n m x y z : 
           R // x -[n]-> y 
        -> R // x -[m]-> z 
        -> (forall k, ~ R z k) 
        -> n <= m.
  Proof.
    intros H1 H2 H3.
    destruct (le_lt_dec n m) as [ | H ]; auto; exfalso.
    assert (exists k, n = m + S k) as (k & ->).
    1: exists (n-m-1); lia.
    apply rel_iter_plus in H1 as (u & H0 & r & H1 & _).
    generalize (rel_iter_fun _ _ _ _ H0 H2); intros <-.
    apply (H3 _ H1).
  Qed.

  Arguments rel_iter_fun_no_further {_ _ _ _ _}.

  Fact normal_form_fun_uniq n m x y z : 
           R // x -[n]-> y 
        -> R // x -[m]-> z 
        -> (forall k, ~ R y k) 
        -> (forall k, ~ R z k)
        -> n = m /\ y = z.
  Proof.
    intros H1 H2 H3 H4.
    generalize (rel_iter_fun_no_further H1 H2 H4)
               (rel_iter_fun_no_further H2 H1 H3).
    intros H5 H6.
    assert (n = m) by lia; split; auto; subst m.
    revert H1 H2; apply rel_iter_fun.
  Qed.

  Let has_nf_Acc n x y : R // x -[n]-> y -> (forall z, ~ R y z) -> Acc (fun x y => R y x) x.
  Proof.
    revert x y; induction n as [ | n IHn ]; simpl; intros x y H1 H2.
    + subst y; constructor; intros z Hz; destruct (H2 _ Hz).
    + destruct H1 as (z & H0 & H1).
      constructor 1; intros k Hk.
      generalize (Rfun H0 Hk); intros <-; eauto.
  Qed.

  Theorem normalize_fun x : (exists y n, R // x -[n]-> y /\ forall z, ~ R y z)
                         -> { y : _ & { n | R // x -[n]-> y /\ forall z, ~ R y z } }.
  Proof.
    intros H; apply norm_Acc.
    destruct H as (y & n & H1 & H2).
    revert H1 H2; apply has_nf_Acc.
  Qed.

End rel_iter.
