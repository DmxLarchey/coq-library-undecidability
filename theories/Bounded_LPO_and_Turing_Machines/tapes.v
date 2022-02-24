(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Bool.

From TuringDec
  Require Import nat_utils Z_utils.

Import NatUtilsNotations.

Set Implicit Arguments.

Reserved Notation "x '~b' y" (at level 70, no associativity).
Reserved Notation "m '⇈' l"  (at level 1, left associativity, format "m ⇈ l").

Fixpoint list_repeat X n (x : X) :=
  match n with 
    | 0 => nil
    | S n => x::list_repeat n x
  end.

Inductive dir := lft | rt.

Section move_many.

  Variables (T : Type).

  Implicit Type (mv : dir -> T -> T).

  Definition move_many mv := fold_left (fun t d => mv d t).

  Infix "⇈" := move_many.
  
  Fact move_many_fix mv d l t : mv⇈(d::l) t = mv⇈l (mv d t).
  Proof. reflexivity. Qed.

  Fact move_many_app mv l r t : mv⇈(l++r) t = mv⇈r (mv⇈l t).
  Proof. apply fold_left_app. Qed.

  Fact move_list_repeat mv n d t : mv⇈(list_repeat n d) t = (mv d)↑n t.
  Proof. revert t; induction n; simpl; auto. Qed.

End move_many.

#[local] Infix "⇈" := move_many.

Section bisimilarity.

  (* As an heterogenoeus relation:

           t₁ is bisimilar to t₂ 

      if for whatever of moves performed on both
      t₁ and t₂, reading after that gives out the 
      same results. Said otherwise, there is no 
      way to distinguish t₁ from t₂ using move and
      read operations *)

  Definition bisimilar X T₁ (r₁ : T₁ -> X) (m₁ : dir -> T₁ -> T₁) 
                         T₂ (r₂ : T₂ -> _) (m₂ : dir -> T₂ -> T₂) :=
     fun t₁ t₂ => forall l, r₁ (m₁⇈l t₁) = r₂ (m₂⇈l t₂).

  Fact bisimilar_refl X T r m t : @bisimilar X T r m _ r m t t.
  Proof. intro; reflexivity. Qed.

  Fact bisimilar_sym X T₁ r₁ m₁ T₂ r₂ m₂ t₁ t₂ : 
         @bisimilar X T₁ r₁ m₁ T₂ r₂ m₂ t₁ t₂ 
       -> bisimilar r₂ m₂ r₁ m₁ t₂ t₁.
  Proof. intros H l; symmetry; apply H. Qed.

  Fact bisimilar_trans X T₁ r₁ m₁ T₂ r₂ m₂ T₃ r₃ m₃ t₁ t₂ t₃ : 
       @bisimilar X T₁ r₁ m₁ T₂ r₂ m₂ t₁ t₂ 
    -> @bisimilar _ _  r₂ m₂ T₃ r₃ m₃ t₂ t₃
    ->  bisimilar r₁ m₁ r₃ m₃ t₁ t₃.
  Proof. intros H1 H2 l; rewrite H1; auto. Qed.

End bisimilarity.

Section TapeSpec.

  Let bisim (X T : Type) rd mv := @bisimilar X T rd mv T rd mv.

  Record TapeSpec := {
    tape :> Type;
    move : dir -> tape -> tape;
    read : tape -> bool;
    write : bool -> tape -> tape;
    read_write : forall t b, read (write b t) = b;
    write_read : forall t, (bisim read move) (write (read t) t) t;
    move_write : forall t n d b, read ((move d)↑(S n) (write b t)) = read ((move d)↑(S n) t);
    write_write : forall t b c, (bisim read move) (write b (write c t)) (write b t);
    left_right : forall t, (bisim read move) (move lft (move rt t)) t;
    right_left : forall t, (bisim read move) (move rt (move lft t)) t;
  }.

End TapeSpec.

Implicit Type T : TapeSpec.

Definition bisimilar_TS T1 T2 := bisimilar (read T1) (move T1) (read T2) (move T2).

#[local] Infix "~b" := (@bisimilar_TS _ _) (at level 70).

Arguments read {_}.
Arguments move {_}.
Arguments write {_}.

Section Zmoves.

  Fact bs_move T1 T2 (t1 : T1) (t2 : T2) d : t1 ~b t2 -> move d t1 ~b move d t2.
  Proof. intros H l; apply (H (_::_)). Qed.

  Fact bs_moves T1 T2 (t1 : T1) (t2 : T2) l : t1 ~b t2 -> move⇈l t1 ~b move⇈l t2.
  Proof. intros H m; rewrite <- !move_many_app; auto. Qed.

  Hint Resolve bs_move : core.

  Fact bs_iter_move T1 T2 n d (t1 : T1) (t2 : T2) : t1 ~b t2 -> (move d)↑n t1 ~b (move d)↑n t2.
  Proof.
    revert t1 t2; induction n as [ | n IHn ]; auto; simpl; intros t1 t2 H.
    apply IHn; auto.
  Qed.

  Fixpoint moves2Z l :=
    match l with
      | nil    => zero
      | lft::l => Zpred (moves2Z l)
      | rt::l  => Zsucc (moves2Z l)
    end.

  Definition Z2moves z := 
    match z with
      | neg n => list_repeat (S n) lft
      | zero  => nil
      | pos n => list_repeat (S n) rt
    end.

  Fact moves2Z2moves : forall z, moves2Z (Z2moves z) = z.
  Proof.
    intros [ n | | n ]; simpl; auto.
    all: induction n as [ | n IHn ]; simpl; auto; rewrite IHn; auto.
  Qed.

  Variable (T : TapeSpec).

  Implicit Type t : T.

  Hint Resolve bisimilar_refl : core.

  Fact bs_moves_Z l (t : T) : move⇈l t ~b Ziter (move lft) (move rt) (moves2Z l) t.
  Proof.
    revert t; induction l as [ | [] l IHl ]; intros t; simpl.
    + apply bisimilar_refl.
    + apply bisimilar_trans with (1 := IHl _).
      destruct (moves2Z l) as [ | | [|n] ]; simpl; try apply bisimilar_refl.
      * apply right_left.
      * apply bs_iter_move, bs_move, right_left.
    + apply bisimilar_trans with (1 := IHl _).
      destruct (moves2Z l) as [ [|n] | | ]; simpl; try apply bisimilar_refl.
      * apply left_right.
      * apply bs_iter_move, bs_move, left_right.
  Qed.

  Fact bs_read_moves_Z l (t : T) : read (move⇈l t) = read (Ziter (move lft) (move rt) (moves2Z l) t).
  Proof. apply (bs_moves_Z _ _ nil). Qed.

End Zmoves.

Section bisimilar_operations.

  Variable (T1 T2 : TapeSpec).

  Fact bs_read (t1 : T1) (t2 : T2) : t1 ~b t2 -> read t1 = read t2.
  Proof. intros H; apply (H nil). Qed.

  Fact bs_Ziter (t1 : T1) (t2 : T2) : t1 ~b t2 <-> forall z, read (Ziter (move lft) (move rt) z t1) = read (Ziter (move lft) (move rt) z t2).
  Proof.
    split.
    + intros H z.
      apply bs_read.
      rewrite <- (moves2Z2moves z).
      generalize (Z2moves z); intros l; clear z.
      do 2 apply bisimilar_trans with (2 := bs_moves_Z _ l _), bisimilar_sym.
      apply bs_moves; auto.
    + intros H l; rewrite !bs_read_moves_Z; auto.
  Qed.

  Fact bs_write b (t1 : T1) (t2 : T2) : t1 ~b t2 -> write b t1 ~b write b t2.
  Proof.
    intros H l.
    generalize (bs_moves_Z _ l (write b t1) nil)
               (bs_moves_Z _ l (write b t2) nil); simpl; intros -> ->.
   destruct (moves2Z l) as [ n | | n ]; unfold Ziter.
    + rewrite !move_write.
      apply (bs_iter_move (S n) _ H nil).
    + now rewrite !read_write.
    + rewrite !move_write.
      apply (bs_iter_move (S n) _ H nil).
  Qed.

End bisimilar_operations.

Check bs_read.
Check bs_write.
Check bs_move.
Check bs_moves.
Check bs_iter_move.

Section SBTM_tape.

  Implicit Type (b : bool) (t : list bool * bool * list bool).

  Definition sbtm_mv d t :=
    match d with
     | lft =>
        match t with
        | (l :: ls, a, rs) => (ls, l, a :: rs)
        | (nil, a, rs) => (nil, false, a :: rs)
        end
     | rt =>
        match t with
        | (ls, a, r :: rs) => (a :: ls, r, rs)
        | (ls, a, nil) => (a :: ls, false, nil)
        end
    end.

  Definition sbtm_rd t := let '(_,b,_) := t in b.
  Definition sbtm_wr b t := let '(l,_,r) := t in (l,b,r).

  Fact sbtm_rd_mv_lft_nth n l b r : sbtm_rd ((sbtm_mv lft)↑(S n) (l,b,r)) = nth n l false.
  Proof.
    revert l b r.
    induction n as [ | n IHn ]; intros [ | x l ] b r; simpl nth; auto;
      rewrite iter_fix; simpl sbtm_mv at 2; rewrite IHn; auto.
    destruct n; auto.
  Qed.

  Fact sbtm_rd_mv_rt_nth n l b r : sbtm_rd ((sbtm_mv rt)↑(S n) (l,b,r)) = nth n r false.
  Proof.
    revert l b r.
    induction n as [ | n IHn ]; intros l b [ | x r ]; simpl nth; auto;
      rewrite iter_fix; simpl sbtm_mv at 2; rewrite IHn; auto.
    destruct n; auto.
  Qed.

  Infix "≈" := (@bisimilar _ _ sbtm_rd sbtm_mv _ sbtm_rd sbtm_mv) (at level 70).

  Local Fact sbtm_bisim n m l b r : (l,b,r) ≈ (l++list_repeat n false,b,r++list_repeat m false).
  Proof.
    intros ll; revert l b r n m; induction ll as [ | [] ll IH ]; intros l b r n m; auto.
   + rewrite !move_many_fix; simpl.
     destruct l as [ | x l ]; simpl.
     * destruct n as [ | n ]; simpl.
       - apply IH with (n := 0) (l := nil) (r := _::_).
       - apply IH with (n := _) (l := nil) (r := _::_).
     * apply IH with (r := _::_).
   + rewrite !move_many_fix; simpl.
     destruct r as [ | x r ]; simpl.
     * destruct m as [ | m ]; simpl.
       - apply IH with (m := 0) (r := nil) (l := _::_).
       - apply IH with (m := _) (r := nil) (l := _::_).
     * apply IH with (l := _::_).
  Qed.

  Local Fact sbtm_rd_mv_lft n l b r r' : sbtm_rd (iter (sbtm_mv lft) n (l,b,r)) = sbtm_rd (iter (sbtm_mv lft) n (l,b,r')).
  Proof.
    revert l b r r'; induction n as [ | n IHn ]; intros l b r r'; simpl; auto.
    destruct l; auto.
  Qed.

  Local Fact sbtm_rd_mv_lft_S n l b b' r r' : sbtm_rd (iter (sbtm_mv lft) (S n) (l,b,r)) = sbtm_rd (iter (sbtm_mv lft) (S n) (l,b',r')).
  Proof. simpl; destruct l; apply sbtm_rd_mv_lft. Qed.

  Local Fact sbtm_rd_mv_rt n l l' b r : sbtm_rd (iter (sbtm_mv rt) n (l,b,r)) = sbtm_rd (iter (sbtm_mv rt) n (l',b,r)).
  Proof.
    revert l l' b r; induction n as [ | n IHn ]; intros l l' b r; simpl; auto.
    destruct r; auto.
  Qed.

  Local Fact sbtm_rd_mv_rt_S n l l' b b' r : sbtm_rd (iter (sbtm_mv rt) (S n) (l,b,r)) = sbtm_rd (iter (sbtm_mv rt) (S n) (l',b',r)).
  Proof.  simpl; destruct r; apply sbtm_rd_mv_rt. Qed.

  Definition SBTM_tape : TapeSpec.
  Proof.
    exists _ sbtm_mv sbtm_rd sbtm_wr.
    + intros ([],?); simpl; auto.
    + intros ((l,b),r); simpl; apply bisimilar_refl.
    + intros ((l,b),r) n [] c; simpl sbtm_wr.
      * apply sbtm_rd_mv_lft_S.
      * apply sbtm_rd_mv_rt_S.
    + intros ([],?) ? ?; simpl; apply bisimilar_refl.
    + intros ((l,b),[ | x r ]); simpl.
      2: apply bisimilar_refl.
      apply bisimilar_sym.
      rewrite (app_nil_end l) at 2. 
      apply sbtm_bisim with (n := 0) (m := 1) (r := nil).
    + intros (([|x l],b),r); simpl.
      2: apply bisimilar_refl.
      apply bisimilar_sym.
      rewrite (app_nil_end r) at 2.
      apply sbtm_bisim with (m := 0) (n := 1) (l := nil).
  Defined.

End SBTM_tape.

Section Z_tape.

  Implicit Type (t : Z -> bool).

  Definition Ztape_mv d t z := t (match d with lft => Zpred | rt => Zsucc end z).
  Definition Ztape_rd t := t zero.
  Definition Ztape_wr b t z := 
    match z with
      | zero => b
      | _    => t z
    end.

  Infix "≈" := (@bisimilar _ _ Ztape_rd Ztape_mv _ Ztape_rd Ztape_mv) (at level 70).

  Fact ext_eq_bisim t t' : (forall z, t z = t' z) -> t ≈ t'.
  Proof.
    intros H l; revert t t' H; induction l as [ | d l IHl ]; intros t t' H.
    + apply H.
    + simpl; apply IHl; intros; apply H.
  Qed.

  Fact Ztape_read_iter_lft n t : Ztape_rd ((Ztape_mv lft)↑(S n) t) = t (neg n).
  Proof.
    revert t; induction n as [ | n IHn ]; intros t; auto.
    rewrite iter_fix, IHn; auto.
  Qed.

  Fact Ztape_read_iter_rt n t : Ztape_rd ((Ztape_mv rt)↑(S n) t) = t (pos n).
  Proof.
    revert t; induction n as [ | n IHn ]; intros t; auto.
    rewrite iter_fix, IHn; auto.
  Qed.

  Definition Z_tape : TapeSpec.
  Proof.
    exists _ Ztape_mv Ztape_rd Ztape_wr.
    + intros; reflexivity.
    + intros t l.
      apply ext_eq_bisim.
      intros []; simpl; auto.
    + intros t n [] b.
      * rewrite !Ztape_read_iter_lft; auto.
      * rewrite !Ztape_read_iter_rt; auto.
    + intros; apply ext_eq_bisim; intros []; auto.
    + intros; apply ext_eq_bisim; intros z.
      unfold Ztape_mv; rewrite Zsucc_pred; auto.
    + intros; apply ext_eq_bisim; intros z.
      unfold Ztape_mv; rewrite Zpred_succ; auto.
  Defined.

End Z_tape.

Section ZB_tape.

  Definition abs_le z m :=
    match z with
      | neg k => S k <= m
      | zero  =>   0 <= m
      | pos k => S k <= m
    end.

  Definition ZBtape := { t : Z -> bool | exists m, forall z, t z = false \/ abs_le z m }.

  Definition ZBtape_mv (d : dir) : ZBtape -> ZBtape.
  Proof.
    intros (t & Ht).
    exists (Ztape_mv d t).
    destruct Ht as (m & Hm).
    exists (S m).
    intros z.
    destruct d; unfold Ztape_mv.
    + specialize (Hm (Zpred z)).
      destruct z as [ n | | [|n] ]; simpl in *; try lia; destruct Hm; auto; lia.
    + specialize (Hm (Zsucc z)).
      destruct z as [ [] | | ]; simpl in *; try lia; destruct Hm; auto; lia.
  Defined.

  Fact ZBtape_mv_eq d t : proj1_sig (ZBtape_mv d t) = Ztape_mv d (proj1_sig t).
  Proof. destruct t; reflexivity. Qed.

  Definition ZBtape_rd (t : ZBtape) := Ztape_rd (proj1_sig t).

  Definition ZBtape_wr (b : bool) : ZBtape -> ZBtape.
  Proof.
    intros (t & Ht).
    exists (Ztape_wr b t).
    destruct Ht as (m & Hm).
    exists m.
    intros z; destruct (Hm z) as [ H | ]; auto.
    destruct z; simpl; auto; right; lia.
  Defined.

  Fact ZBtape_wr_eq b t : proj1_sig (ZBtape_wr b t) = Ztape_wr b (proj1_sig t).
  Proof. destruct t; reflexivity. Qed.

  Fact ZBtape_iter_eq n d t : proj1_sig ((ZBtape_mv d)↑n t) = (Ztape_mv d)↑n (proj1_sig t).
  Proof.
    revert t; induction n as [ | n IHn ]; simpl; auto; intros t; rewrite IHn, ZBtape_mv_eq; auto.
  Qed.

  Fact ZBtape_moves_eq l t : proj1_sig (ZBtape_mv⇈l t) = Ztape_mv⇈l (proj1_sig t).
  Proof.
    revert t; induction l as [ | d l IHl ]; intros t; simpl; auto.
    rewrite IHl, ZBtape_mv_eq; auto.
  Qed.

  Fact ZBtape_bisim t1 t2 : @bisimilar _ _ ZBtape_rd ZBtape_mv _ ZBtape_rd ZBtape_mv t1 t2
                        <-> @bisimilar _ _ Ztape_rd Ztape_mv   _ Ztape_rd Ztape_mv (proj1_sig t1) (proj1_sig t2).
  Proof.
    split; intros H l; specialize (H l); revert H; unfold ZBtape_rd;
    rewrite !ZBtape_moves_eq; auto.
  Qed.

  Definition ZB_tape : TapeSpec.
  Proof.
    exists _ ZBtape_mv ZBtape_rd ZBtape_wr.
    + intros t b; unfold ZBtape_rd.
      rewrite ZBtape_wr_eq; apply (@read_write Z_tape). 
    + intro t; apply ZBtape_bisim. 
      rewrite ZBtape_wr_eq.
      apply (@write_read Z_tape).
    + intros t n d b; unfold ZBtape_rd.
      rewrite !ZBtape_iter_eq, ZBtape_wr_eq.
      apply (@move_write Z_tape).
    + intros t b c; apply ZBtape_bisim.
      rewrite !ZBtape_wr_eq.
      apply (@write_write Z_tape).
    + intro; apply ZBtape_bisim.
      rewrite !ZBtape_mv_eq.
      apply (@left_right Z_tape).
    + intro; apply ZBtape_bisim.
      rewrite !ZBtape_mv_eq.
      apply (@right_left Z_tape).
  Defined.

End ZB_tape.

Check SBTM_tape.
Check Z_tape.
Check ZB_tape.

Fact fun_bounded_list X (f : nat -> X) d m : (forall n, f n = d \/ n < m) -> exists l, forall n, f n = nth n l d.
Proof.
 revert f; induction m as [ | m IHm ]; intros f Hm.
 + exists nil; intros n.
   destruct (Hm n) as [ -> | ]; try lia.
   destruct n; auto.
 + destruct IHm with (f := fun n => f (S n)) as (l & Hl).
   * intros n; destruct (Hm (S n)); auto; lia.
   * exists ((f 0)::l); intros [ | n ]; auto.
     apply Hl.
Qed.

(** ZB_tape and SBTM_tape are different from Coq's of view: 
    - one can *compute* a finite domain from SBTM_tape and not for ZB_tape where
      the domain bounds the space where the tape reads as "true" 
    But ZB_tape and SBTM_tape are bisimilar because bisimilarity
    holds in Prop
 *)  

Lemma ZB_tape_bisim_SBTM_tape : forall t : ZB_tape, exists t' : SBTM_tape, t ~b t'.
Proof.
  intros (t & m & Hm).
  destruct (@fun_bounded_list _ (fun n => t (pos n)) false (S m)) as (r & Hr).
  1:{ intros n; destruct (Hm (pos n)); auto. }
  destruct (@fun_bounded_list _ (fun n => t (neg n)) false (S m)) as (l & Hl).
  1:{ intros n; destruct (Hm (neg n)); auto. }
  exists (l,t zero,r); intros lm.
  simpl; unfold ZBtape_rd.
  rewrite ZBtape_moves_eq; simpl.
  change (read ((@move Z_tape)⇈lm t) = read ((@move SBTM_tape)⇈lm (l,t zero, r))).
  rewrite !bs_read_moves_Z.
  destruct (moves2Z lm) as [ n | | n ]; unfold Ziter; auto.
  + rewrite sbtm_rd_mv_lft_nth, Ztape_read_iter_lft; auto.
  + rewrite sbtm_rd_mv_rt_nth, Ztape_read_iter_rt; auto.
Qed.

Lemma SBTM_tape_bisim_ZB_tape : forall t : SBTM_tape, exists t' : ZB_tape, t ~b t'.
Proof.
  intros ((l,b),r).
  set (t z :=  match z with neg n => nth n l false | zero => b | pos n => nth n r false end).
  assert (Ht : exists m, forall z, t z = false \/ abs_le z m).
  1:{ exists (length l + length r); intros [ n | | n ]; simpl.
      + destruct (le_lt_dec (length l) n) as [ H | H ]; try lia.
        apply nth_overflow with (d := false) in H; auto.
      + lia.
      + destruct (le_lt_dec (length r) n) as [ H | H ]; try lia.
        apply nth_overflow with (d := false) in H; auto. }
  set (t' := exist _ t Ht : ZB_tape). 
  exists t'.
  apply bs_Ziter; intros [ n | | n ]; unfold Ziter; auto.
  + rewrite sbtm_rd_mv_lft_nth.
    unfold ZB_tape, read, move.
    unfold ZBtape_rd.
    generalize (ZBtape_iter_eq (S n) lft t'); simpl; intros ->.
    rewrite <- iter_fix, Ztape_read_iter_lft; auto.
  + rewrite sbtm_rd_mv_rt_nth.
    unfold ZB_tape, read, move.
    unfold ZBtape_rd.
    generalize (ZBtape_iter_eq (S n) rt t'); simpl; intros ->.
    rewrite <- iter_fix, Ztape_read_iter_rt; auto.
Qed.

(** Notice that no ZB_tape is bisimilar to (fun _ => true) *)

Lemma not_ZB_tape_bisim_Z_tape (t : ZB_tape) : ~ t ~b ((fun _ => true) : Z_tape).
Proof.
  intros H.
  destruct t as (t & m & Hm).
  specialize (H (list_repeat (S m) rt)).
  unfold ZB_tape, Z_tape, read, move, ZBtape_rd in H.
  rewrite ZBtape_moves_eq in H; simpl proj1_sig in H.
  rewrite !move_list_repeat in H; simpl in H.
  rewrite <- !iter_fix, !Ztape_read_iter_rt in H.
  destruct (Hm (pos m)) as [ D | D ].
  + now rewrite D in H.
  + simpl in D; lia.
Qed.

(** Notice that no SBTM_tape is bisimilar to (fun _ => true) *)

Lemma not_SBTM_tape_bisim_Z_tape (t : SBTM_tape) : ~ t ~b ((fun _ => true) : Z_tape).
Proof.
  intros H.
  destruct (SBTM_tape_bisim_ZB_tape t) as (t' & H').
  apply (@not_ZB_tape_bisim_Z_tape t'),
        bisimilar_trans with (2 := H), 
        bisimilar_sym; auto.
Qed.

Module TapeNotations.
  Infix "~b" := (@bisimilar_TS _ _).
  Infix "⇈" := move_many.
End TapeNotations.