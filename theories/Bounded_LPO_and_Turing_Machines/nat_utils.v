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

#[local] Reserved Notation "f '↑' n"  (at level 1, left associativity, format "f ↑ n").

Section nat_rev_ind.

  Variables (P : nat -> Prop)
            (HP : forall n, P (S n) -> P n).

  Theorem nat_rev_ind x y : x <= y -> P y -> P x.
  Proof. induction 1; auto. Qed.

End nat_rev_ind.

Section minimize.

  Variable (P : nat -> Prop) (HP : forall n, { P n } + { ~ P n }).

  Inductive bar n : Prop := 
    | bar_stop : P n -> bar n
    | bar_next : bar (S n) -> bar n.

  Let Fixpoint bar_min n (D : bar n) : { m | P m /\ n <= m /\ forall i, P i -> i < n \/ m <= i }.
  refine (match HP n with
    | left H  => exist _ n _
    | right H => let (m,Hm) := bar_min (S n) _ in exist _ m _
  end).
  Proof.
    + split; auto; split; intros; lia.
    + inversion D; auto; tauto.
    + destruct Hm as (H1 & H2 & H3); split; auto; split; try lia.
      intros i Hi.
      destruct (eq_nat_dec i n) as [ -> | ]; try tauto.
      apply H3 in Hi; lia.
  Qed.

  Let le_P_bar : ex P -> bar 0.
  Proof.  
    intros (n & Hn).
    cut (bar n).
    + apply nat_rev_ind.
      * now constructor 2.
      * lia.
    + now constructor 1.
  Qed.

  Theorem minimize : ex P -> { n | P n /\ forall i, P i -> n <= i }.
  Proof.
    intros H.
    destruct bar_min with (1 := le_P_bar H) as (n & H1 & H2 & H3).
    exists n; split; auto.
    intros i H4.
    apply H3 in H4; lia.
  Qed.

  Corollary ex_iff_ex_min : ex P <-> exists n, P n /\ forall m, P m -> n <= m.
  Proof.
    split.
    + intros H.
      apply minimize in H as (n & ? & ?); eauto.
    + intros (n & ? & _); eauto.
  Qed.

End minimize.

Section iter.

  Variable (X : Type).

  Implicit Type (f : X -> X).

  Fixpoint iter f n :=
    match n with
      | 0   => fun x => x
      | S n => fun x => f↑n (f x)
    end
  where "f ↑ n" := (iter f n).

  Fact iter_fix f n x : f↑(S n) x = f↑n (f x).
  Proof. trivial. Qed.

  Fact iter_plus f n m x : f↑(n+m) x = f↑m (f↑n x).
  Proof. revert x; induction n; simpl; auto. Qed.

  Fact iter_S f n x : f↑(S n) x = f (f↑n x).
  Proof.
    replace (S n) with (n+1) by lia.
    rewrite iter_plus; auto.
  Qed.

End iter.

Module NatUtilsNotations.

  Infix "↑" := iter.

End NatUtilsNotations.
