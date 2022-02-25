(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia Bool Eqdep_dec.

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

Section fin_dec.

  Variable (P : nat -> Prop) (Pdec : forall x, { P x } + { ~ P x }).

  Theorem bfall_choose n : { m | m < n /\ P m } + { forall m, P m -> n <= m }.
  Proof.
    induction n as [ | n [ (m & H1 & H2) | H ] ].
    + right; intros; lia.
    + left; exists m; split; auto; lia.
    + destruct (Pdec n) as [ H1 | H1 ].
      * left; exists n; split; auto.
      * right; intros m Hm.
        destruct (eq_nat_dec n m) as [ <- | ? ]; try easy.
        apply H in Hm; lia.
  Qed.

  Theorem bfall_dec n : { forall m, P m -> n <= m } + { ~ forall m, P m -> n <= m }.
  Proof.
    destruct (bfall_choose n) as [ (m & H1 & H2) | H ]; auto; right.
    intros H; apply H in H2; lia.
  Qed.

End fin_dec.

Record p_quotient {X} (R : X -> X -> Prop) := {
  pq_type :> Type;
  pq_class : X -> option pq_type;
  pq_repr : pq_type -> X;
  pq_eq : forall c, pq_class (pq_repr c) = Some c;
  pq_None : forall x, ~ R x x <-> pq_class x = None;
  pq_Some : forall x y, R x y <-> pq_class x = pq_class y /\ pq_class x <> None;
}.

Record quotient {X} (R : X -> X -> Prop) := {
  q_type :> Type;
  q_class : X -> q_type;
  q_repr : q_type -> X;
  q_surj : forall c, q_class (q_repr c) = c;
  q_equiv : forall x y, R x y <-> q_class x = q_class y 
}.

Section per_nat_quotient.

  Variables (R : nat -> nat -> Prop)
            (Rsym : forall x y, R x y -> R y x)
            (Rtrans : forall x y z, R x y -> R y z -> R x z)
            (Rdec : forall x y, { R x y } + { ~ R x y }).

  Let P n := R n n /\ forall m, R n m -> n <= m.

  Let Pdec n : { P n } + { ~ P n }.
  Proof.
    unfold P.
    destruct (Rdec n n) as [ H1 | H1 ]; try tauto.
    destruct bfall_dec with (P := R n) (n := n); auto; tauto.
  Qed.

  Let Q n := (if Pdec n then true else false) = true.

  Let HQ n : Q n <-> R n n /\ forall m, R n m -> n <= m.
  Proof.
    fold (P n); unfold Q.
    destruct (Pdec n) as [ H | H ]; try tauto; now split.
  Qed.

  Let Y := sig Q.

  Let HY (a b : Y) : a = b <-> proj1_sig a = proj1_sig b.
  Proof.
    split.
    + intros []; auto.
    + revert a b; intros [ a Ha ] [ b Hb ]; simpl; intros <-; f_equal.
      apply UIP_dec, bool_dec.
  Qed.

  Let find x : { y : Y | R (proj1_sig y) x } + { ~ R x x }.
  Proof.
    destruct (Rdec x x) as [ H | H ]; try tauto; left.
    destruct minimize with (P := R x) as (y & H1 & H2); eauto.
    assert (Hy : Q y).
    1:{ apply HQ; split; eauto. }
    exists (exist _ y Hy); simpl; auto.
  Qed.

  Definition per_nat_quotient : p_quotient R.
  Proof.
    exists Y (fun x => match find x with inleft (exist _ x _) => Some x | inright _ => None end) (@proj1_sig _ _).
    + intros (x & Hx); simpl.
      destruct (find x) as [ ((y & Hy) & H1) | H ].
      * simpl in H1.
        f_equal; apply HY; simpl.
        apply HQ in Hx as [ H3 H4 ].
        apply HQ in Hy as [ H5 H6 ].
        generalize (Rsym H1); intros H0.
        apply H4 in H0.
        apply H6 in H1.
        lia.
      * destruct H.
        apply HQ in Hx; tauto.
    + intros x.
      destruct (find x) as [ ((y & Hy) & H1) | H ]; simpl in *; try tauto.
      split; try easy; intros []; eauto.
    + intros x y.
      destruct (find x) as [ ((x' & H2) & H1) | H1 ]; simpl in *; try tauto.
      2:{ split; try easy; intros H; destruct H1; eauto. }
      destruct (find y) as [ ((y' & H4) & H3) | H3 ]; simpl in *; try tauto.
      2:{ split; try easy; intros H; destruct H3; eauto. }
      split.
      * intros H; split; try easy; f_equal.
        apply HY; simpl.
        apply HQ in H2 as [ H0 H2 ].
        apply HQ in H4 as [ H4 H7 ].
        apply le_antisym; eauto.
      * intros [ H _ ]; injection H; intros; subst; eauto.
  Qed.

End per_nat_quotient.

Section nat_quotient.

  Variables (R : nat -> nat -> Prop)
            (Rrefl : forall x, R x x)
            (Rsym : forall x y, R x y -> R y x)
            (Rtrans : forall x y z, R x y -> R y z -> R x z)
            (Rdec : forall x y, { R x y } + { ~ R x y }).

  Definition nat_quotient : quotient R.
  Proof.
    destruct per_nat_quotient with (R := R) as [ X cls repr surj none some ]; auto.
    assert (f : forall n, { x | cls n = Some x } ).
    1:{ intros n.
        generalize (some n) (none n).
        case_eq (cls n).
        + intros x; exists x; auto.
        + intros Hn H1 H2; exfalso.
          apply H2; auto. }
    exists X (fun n => proj1_sig (f n)) repr.
    + intro n.
      destruct (f (repr n)) as (x & Hx); simpl.
      rewrite surj in Hx; inversion Hx; auto.
    + intros x y.
      destruct (f x) as (n & Hn).
      destruct (f y) as (m & Hm); simpl.
      rewrite some, Hn, Hm; split.
      * intros (H & _); inversion H; auto.
      * intros ->; easy.
  Qed.

End nat_quotient.


        
     
   
       
    

  

