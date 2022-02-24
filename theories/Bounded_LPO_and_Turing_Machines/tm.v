(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Bool.

Set Implicit Arguments.

Reserved Notation "x '~b' y" (at level 70, no associativity).
Reserved Notation "f '↑' n"  (at level 1, left associativity, format "f ↑ n").
Reserved Notation "m '⇈' l"  (at level 1, left associativity, format "m ⇈ l").

Reserved Notation "M '//' s '-1>' t" (at level 70, format "M  //  s  -1>  t").
Reserved Notation "M '//' s '-[' n ']->' t" (at level 70, format "M  //  s  -[ n ]->  t").
Reserved Notation "M '//' s '->>' t" (at level 70, format "M  //  s  ->>  t").
Reserved Notation "M '//' s '~~>' t" (at level 70, format "M  //  s  ~~>  t").

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

#[local] Infix "↑" := iter.

Fixpoint list_repeat X n (x : X) :=
  match n with 
    | 0 => nil
    | S n => x::list_repeat n x
  end.

Section Z.

  Inductive Z := neg : nat -> Z | zero : Z | pos : nat -> Z.

  Definition Zsucc z :=
    match z with 
      | neg 0     => zero
      | neg (S n) => neg n
      | zero      => pos 0
      | pos n     => pos (S n)
    end.

  Definition Zpred z :=
    match z with
      | pos 0     => zero
      | pos (S n) => pos n
      | zero      => neg 0
      | neg n     => neg (S n)
    end.

  Fact Zsucc_pred : forall z, Zsucc (Zpred z) = z.
  Proof. intros [ | | [] ]; auto. Qed.

  Fact Zpred_succ : forall z, Zpred (Zsucc z) = z.
  Proof. intros [ [] | | ]; auto. Qed.

  Definition Ziter X (f g : X -> X) z :=
    match z with
      | neg n => f↑(S n)
      | zero  => fun x => x
      | pos n => g↑(S n)
    end.

End Z.

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

End move_many.

#[local] Infix "⇈" := move_many.

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

Definition bisim (X T : Type) rd mv := @bisimilar X T rd mv T rd mv.

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

Implicit Type T : TapeSpec.

Definition bisim_TS T1 T2 := bisimilar (read T1) (move T1) (read T2) (move T2).

Infix "~b" := (@bisim_TS _ _) (at level 70).

Arguments read {_}.
Arguments move {_}.
Arguments write {_}.

Section Zmoves.

  Fixpoint moves2Z l :=
    match l with
      | nil    => zero
      | lft::l => Zpred (moves2Z l)
      | rt::l  => Zsucc (moves2Z l)
    end.

  Fact bs_move T1 T2 (t1 : T1) (t2 : T2) d : t1 ~b t2 -> move d t1 ~b move d t2.
  Proof. intros H l; apply (H (_::_)). Qed.

  Hint Resolve bs_move : core.

  Fact bs_moves_dir T1 T2 n d (t1 : T1) (t2 : T2) : t1 ~b t2 -> (move d)↑n t1 ~b (move d)↑n t2.
  Proof.
    revert t1 t2; induction n as [ | n IHn ]; auto; simpl; intros t1 t2 H.
    apply IHn; auto.
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
      * apply bs_moves_dir, bs_move, right_left.
    + apply bisimilar_trans with (1 := IHl _).
      destruct (moves2Z l) as [ [|n] | | ]; simpl; try apply bisimilar_refl.
      * apply left_right.
      * apply bs_moves_dir, bs_move, left_right.
  Qed.

  Fact bs_read_moves_Z l (t : T) : read (move⇈l t) = read (Ziter (move lft) (move rt) (moves2Z l) t).
  Proof. apply (bs_moves_Z _ _ nil). Qed.

End Zmoves.

Section bs.

  Variable (T1 T2 : TapeSpec).

  Fact bs_read (t1 : T1) (t2 : T2) : t1 ~b t2 -> read t1 = read t2.
  Proof. intros H; apply (H nil). Qed.

  Fact bs_write b (t1 : T1) (t2 : T2) : t1 ~b t2 -> write b t1 ~b write b t2.
  Proof.
    intros H l.
    generalize (bs_moves_Z _ l (write b t1) nil)
               (bs_moves_Z _ l (write b t2) nil); simpl; intros -> ->.
   destruct (moves2Z l) as [ n | | n ]; unfold Ziter.
    + rewrite !move_write.
      apply (bs_moves_dir (S n) _ H nil).
    + now rewrite !read_write.
    + rewrite !move_write.
      apply (bs_moves_dir (S n) _ H nil).
  Qed.

End bs.

Section TuringMachines.

  Record TuringMachine := {
    state : Type;
    trans : state -> bool -> option (state * bool * dir) 
  }.

  Variable T : TapeSpec.

  Implicit Type M : TuringMachine.

  Inductive TM_step M : (state M*T) -> (state M*T) -> Prop :=
    | in_TM_step s₁ t₁ s₂ b d : trans M s₁ (read t₁) = Some (s₂,b,d) 
                             -> M // (s₁,t₁) -1> (s₂,move d (write b t₁))
  where "M // s -1> t" := (TM_step M s t).

  Definition TM_steps M := rel_iter (TM_step M).

  Notation "M // c₁ -[ n ]-> c₂" := (TM_steps M n c₁ c₂).

  Fact TM_step_fun M : functional (TM_step M).
  Proof.
    intros c c1 c2 H; revert H c2; induction 1; inversion 1.
    rewrite H in H4; inversion H4; subst; auto.
  Qed.

  Fact TM_steps_fun M n : functional (TM_steps M n).
  Proof. apply rel_iter_fun, TM_step_fun. Qed.

  Definition TM_reach M c₁ c₂ := exists n, M // c₁ -[n]-> c₂.
  Definition TM_stop M c₁ := forall c₂, ~ M // c₁ -1> c₂.

  Fact TM_step_reif M c₁ : 
           { c₂ | M // c₁ -1> c₂ } 
         + { TM_stop M c₁ }.
  Proof.
    destruct c₁ as (s,t).
    case_eq (trans M s (read t)).
    + intros ((s',b),d) E; left.
      exists (s',move d(write b t)).
      constructor; auto.
    + intros E; right; intros (s',t') H.
      inversion H as [ ? ? ? ? ? H1 ].
      now rewrite E in H1.
  Qed.

  Fact TM_steps_reif M n c₁ : 
           { c₂ | M // c₁ -[n]-> c₂ } 
         + { c₂ : _ & { m | m < n /\ M // c₁ -[m]-> c₂ /\ TM_stop M c₂ } }.
  Proof. apply rel_iter_next, TM_step_reif. Qed.

  Fact TM_stop_no_further M m n c c₁ c₂ : M // c -[n]-> c₁ -> M // c -[m]-> c₂ -> TM_stop M c₂ -> n <= m.
  Proof. apply rel_iter_fun_no_further, TM_step_fun. Qed.

  Fact TM_stop_uniq M m n c c₁ c₂ : 
           M // c -[n]-> c₁ 
        -> M // c -[m]-> c₂
        -> TM_stop M c₁ 
        -> TM_stop M c₂ 
        -> n = m /\ c₁ = c₂.
  Proof. apply normal_form_fun_uniq, TM_step_fun. Qed.

  Fact TM_stop_dec M c : { TM_stop M c } + { ~ TM_stop M c }.
  Proof.
    destruct (TM_step_reif M c) as [ (c' & H) | H ]; auto; right.
    intros H'; apply H' in H; auto.
  Qed.

  Definition TM_output M c₁ c₂ := TM_reach M c₁ c₂ /\ TM_stop M c₂.

  Notation "M // c₁ ->> c₂" := (TM_reach M c₁ c₂).
  Notation "M // c₁ ~~> c₂" := (TM_output M c₁ c₂).

  Definition TM_halt M s t := exists c, M // (s,t) ~~> c.
  Definition TM_compute M s t t' := exists s', M // (s,t) ~~> (s',t').

  Fact TM_steps_stop_compute M n s t s' t' : M // (s,t) -[n]-> (s',t') -> TM_stop M (s',t') -> TM_compute M s t t'.
  Proof. exists s'; split; auto; exists n; auto. Qed.

  Theorem TM_output_reif M c : 
               ex (TM_output M c) 
            -> { c' : _ & { n | M // c -[n]-> c' /\ TM_stop M c' } }.
  Proof.
    intros H.  
    apply normalize_fun.
    + apply TM_step_reif.
    + apply TM_step_fun.
    + destruct H as (y & (n & H1) & H2).
      exists y, n; split; auto.
  Qed.

End TuringMachines.

Arguments TM_step {_}.
Arguments TM_steps {_}.
Arguments TM_reach {_}.
Arguments TM_stop {_}.
Arguments TM_output {_}.
Arguments TM_halt {_}.
Arguments TM_compute {_}.

#[local] Notation "M // s -1> t" := (TM_step M s t).
#[local] Notation "M // c₁ -[ n ]-> c₂" := (TM_steps M n c₁ c₂).
#[local] Notation "M // c₁ ->> c₂" := (TM_reach M c₁ c₂).
#[local] Notation "M // c₁ ~~> c₂" := (TM_output M c₁ c₂).

Definition TapeProblem := forall T, T -> Prop.

Definition TM_repr (P : TapeProblem) := 
  { M : _ & { s | forall T t, TM_halt M s t <-> P T t } }.

Definition TM_dec_on (P : TapeProblem) (T : TapeSpec) :=
  { M : _ & { s | (forall t : T, TM_halt M s t) 
               /\ (forall t t', TM_compute M s t t' -> read t' = true <-> P T t) } }.

Definition Coq_dec (P : Prop) := { P } + { ~ P }.

Fact TM_dec_on_Coq_dec P T : TM_dec_on P T -> forall t, Coq_dec (P T t).
Proof.
  intros (M & s & H1 & H2) t.
  destruct TM_output_reif with (1 := H1 t) as ((s',t') & n & H3 & H4).
  generalize (H2 _ _ (TM_steps_stop_compute _ _ _ H3 H4)).
  destruct (read t'); intros H; [ left | right ]; rewrite <- H; easy.
Qed.

Definition SEARCH d b : TapeProblem := fun _ t => exists n, b = read ((move d)↑n t).

Fact SEARCH_equiv d b T t :
     @SEARCH d b T t <-> exists n, b = read ((move d)↑n t) /\ forall m, b = read ((move d)↑m t) -> n <= m.
Proof. apply ex_iff_ex_min; intro; apply bool_dec. Qed.

Section TM_search.

  Variable (d : dir) (b : bool).

  Definition TM_search : TuringMachine.
  Proof.
    exists unit.
    intros _ c.
    refine(match bool_dec b c with
      | left H => None
      | right H => Some (tt,c,d)
    end).
  Defined.

  Notation M := TM_search.

  Variable (T : TapeSpec).

  Implicit Type t : T.

  Fact TM_search_step s t s' t' : 
         M // (s,t) -1> (s',t') <-> b <> read t /\ t' = move d (write (read t) t).
  Proof.
    split.
    + change t with (snd (s,t)) at 2 3 4.
      change t' with (snd (s',t')) at 2.
      generalize (s,t) (s',t'); clear s t s' t'.
      induction 1 as [ [] t [] b' d' H ]; simpl in H |- *.
      destruct (bool_dec b (read t)) as [ E | D ]; try easy; split; auto.
      inversion H; auto.
    + intros [ H1 -> ].
      destruct s; destruct s'.
      constructor; simpl.
      now destruct (bool_dec b (read t)).
  Qed.

  Fact TM_search_steps_inv n s t s' t' :
        M // (s,t) -[n]-> (s',t') -> (forall i, b = read ((move d)↑i t) -> n <= i) /\ t' ~b (move d)↑n t.
  Proof.
    unfold TM_steps.
    revert s t s' t'; induction n as [ | n IHn ]; intros s t s' t'; simpl.
    + inversion 1; subst s' t'; split.
      * intros; lia.
      * apply bisimilar_refl.
    + intros (([],t1) & H1 & H2).
      apply TM_search_step in H1 as [ H0 H1 ].
      apply IHn in H2 as [ H2 H3 ].
      split.
      * intros [ | i ] H; auto.
        1: destruct H0; auto.
        apply le_n_S, H2.
        rewrite H; subst t1; simpl.
        apply bs_read, bs_moves_dir, 
              bs_move, bisimilar_sym,
              write_read. 
      * apply bisimilar_trans with (1 := H3).
        apply bs_moves_dir; subst.
        apply bs_move, write_read.
  Qed.

  Fact TM_search_steps n s t :
        (forall i, b = read ((move d)↑i t) -> n <= i) -> exists c, M // (s,t) -[n]-> c.
  Proof.
    revert s t; induction n as [ | n IHn ]; intros s t H.
    + exists (s,t); red; simpl; auto.
    + destruct IHn with (s := tt) (t := move d (write (read t) t))
        as (c & Hc).
      * intros i Hi.
        apply le_S_n, H.
        rewrite Hi; simpl.
        apply bs_read, bs_moves_dir, bs_move, write_read.
      * exists c, (tt, move d (write (read t) t)); split; auto.
        constructor; simpl.
        destruct (bool_dec b (read t)) as [ E |  ]; auto.
        apply (H 0) in E; lia.
  Qed.

  Fact TM_search_stop s t : TM_stop M (s,t) <-> b = read t.
  Proof.
    split.
    + intros H.
      destruct (bool_dec b (read t)) as [ | D ]; auto; exfalso.
      apply (H (tt,move d (write (read t) t))).
      constructor; simpl.
      now destruct (bool_dec b (read t)).
    + intros E (s',t') H.
      apply TM_search_step in H as [ [] _ ]; auto.
  Qed.

  Lemma TM_search_halt s t :
        TM_halt M s t <-> exists n, b = read ((move d)↑n t).
  Proof.
    split.
    + intros ((s',t') & (n & Hn) & H').
      exists n.
      apply TM_search_stop in H' as ->.
      apply TM_search_steps_inv in Hn as [ _ H2 ].
      apply bs_read; auto.
    + intros H.
      apply minimize in H as (n & H1 & H2).
      2: intro; apply bool_dec.
      destruct TM_search_steps with (1 := H2) (s := s) as ((s',t') & H3).
      exists (s',t'); split.
      * exists n; auto.
      * apply TM_search_stop.
        apply TM_search_steps_inv in H3 as [ _ H' ].
        rewrite H1.
        now apply bs_read, bisimilar_sym.
  Qed.

End TM_search.

(* The (polymorphic) SEARCH problem is Turing represented *)

Theorem SEARCH_repr d b : TM_repr (SEARCH d b).
Proof.
  exists (TM_search d b), tt.
  intros T t; apply TM_search_halt.
Qed.

Section bisim_TM.

  Variables (T T' : TapeSpec) (M : TuringMachine).

  Let TM_step_bisim_rec (x₁ y₁ : state M * T) (x₂ : state M * T') : 
          fst x₁ = fst x₂ 
       -> snd x₁ ~b snd x₂ 
       -> M // x₁ -1> y₁ 
       -> exists y₂, fst y₁ = fst y₂ 
                  /\ snd y₁ ~b snd y₂ 
                  /\ M // x₂ -1> y₂.
  Proof.
    intros H1 H2 H3; revert H3 x₂ H1 H2.
    induction 1 as [ s1 t1 s2 b d H ]; intros (s3,t3) H1 H2; simpl in *; subst s3.
    exists (s2,move d (write b t3)); simpl; split; auto; split.
    + apply bs_move, bs_write; auto.
    + constructor; rewrite <- H.
      f_equal; symmetry; apply bs_read; auto.
  Qed.

  Lemma TM_step_bisim s₁ (t₁ : T) s₂ t₂ (t₁' : T') : 
          t₁ ~b t₁' 
       -> M // (s₁,t₁) -1> (s₂,t₂) 
       -> exists t₂', t₂ ~b t₂' 
                   /\ M // (s₁,t₁') -1> (s₂,t₂').
  Proof.
    intros H1 H2.
    apply (@TM_step_bisim_rec (s₁,t₁) (s₂,t₂) (s₁,t₁')) in H2 as ((?,t') & H3 & H4 & H5); simpl in *; subst; eauto.
  Qed.

  Lemma TM_steps_bisim n s₁ (t₁ : T) s₂ t₂ (t₁' : T') : 
          t₁ ~b t₁' 
       -> M // (s₁,t₁) -[n]-> (s₂,t₂) 
       -> exists t₂', t₂ ~b t₂' 
                   /\ M // (s₁,t₁') -[n]-> (s₂,t₂').
  Proof.
    unfold TM_steps.
    revert s₁ t₁ s₂ t₂ t₁'; induction n as [ | n IHn ]; intros s1 t1 s2 t2 t1'; simpl; intros H1 H2.
    + exists t1'; inversion H2; subst; auto.
    + destruct H2 as ((s3,t3) & H2 & H3).
      apply TM_step_bisim with (1 := H1) in H2 as (t3' & H4 & H5).
      apply IHn with (1 := H4) in H3 as (t2' & H6 & H7).
      exists t2'; split; auto.
      exists (s3,t3'); auto.
  Qed.

End bisim_TM.

Lemma TM_stop_bisim T T' M s (t : T) (t' : T') :
          t ~b t' -> TM_stop M (s,t) <-> TM_stop M (s,t').
Proof.
  intros H; split; intros H1 (s',t1) H2.
  + apply TM_step_bisim with (1 := bisimilar_sym H) in H2
      as (t2 & H3 & H4).
    apply H1 in H4; auto.
  + apply TM_step_bisim with (1 := H) in H2
      as (t2 & H3 & H4).
    apply H1 in H4; auto.
Qed.

Section TM_compute_bisim.

  Theorem TM_compute_bisim T T' M s (t : T) (o : T) (t' : T') :
       t ~b t' -> TM_compute M s t o -> exists o', TM_compute M s t' o' /\ o ~b o'.
  Proof.
    intros H (s' & (n & H1) & H2).
    apply TM_steps_bisim with (1 := H) in H1
      as (o' & H3 & H4).
    exists o'; split; auto.
    exists s'; split; auto.
    * exists n; auto.
    * revert H2; apply TM_stop_bisim, bisimilar_sym; auto.
  Qed.

End TM_compute_bisim.

Section TM_HALT_bisimilar.

  Let bs_TM_HALT_half T1 T2 M s (t1 : T1) (t2 : T2) : t1 ~b t2 -> TM_halt M s t1 -> TM_halt M s t2.
  Proof.
    intros E ((s',t') & (n & Hn) & H2).
    destruct TM_steps_bisim with (1 := E) (2 := Hn) as (t3 & H3 & H4).
    exists (s',t3); split.
    1: exists n; auto.
    revert H2; apply TM_stop_bisim, bisimilar_sym; auto.
  Qed.

  Theorem TM_HALT_bisimilar T1 T2 M s (t1 : T1) (t2 : T2) : 
          t1 ~b t2 -> TM_halt M s t1 <-> TM_halt M s t2.
  Proof.
    intros H; split; apply bs_TM_HALT_half; auto.
    apply bisimilar_sym; auto.
  Qed.

End TM_HALT_bisimilar.

Section SBTM.

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

  Infix "~b" := (bisim sbtm_rd sbtm_mv).

  Local Fact sbtm_bisim n m l b r : (l,b,r) ~b (l++list_repeat n false,b,r++list_repeat m false).
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

  Definition Tape_SBTM : TapeSpec.
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

End SBTM.

Section Ztape.

  Implicit Type (t : Z -> bool).

  Definition Ztape_mv d t z := t (match d with lft => Zpred | rt => Zsucc end z).
  Definition Ztape_rd t := t zero.
  Definition Ztape_wr b t z := 
    match z with
      | zero => b
      | _    => t z
    end.

  Infix "~b" := (bisim Ztape_rd Ztape_mv).

  Fact ext_eq_bisim t t' : (forall z, t z = t' z) -> t ~b t'.
  Proof.
    intros H l; revert t t' H; induction l as [ | d l IHl ]; intros t t' H.
    + apply H.
    + simpl; apply IHl; intros; apply H.
  Qed.

  Fact Ztape_read_iter_lft n t : Ztape_rd (iter (Ztape_mv lft) (S n) t) = t (neg n).
  Proof.
    revert t; induction n as [ | n IHn ]; intros t; auto.
    rewrite iter_fix, IHn; auto.
  Qed.

  Fact Ztape_read_iter_rt n t : Ztape_rd (iter (Ztape_mv rt) (S n) t) = t (pos n).
  Proof.
    revert t; induction n as [ | n IHn ]; intros t; auto.
    rewrite iter_fix, IHn; auto.
  Qed.

  Definition Tape_Z : TapeSpec.
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

End Ztape.

Section Ztape_bounded.

  Definition abs_le z m :=
    match z with
      | neg k => S k <= m
      | zero  =>   0 <= m
      | pos k => S k <= m
    end.

  Definition ZB_tape := { t : Z -> bool | exists m, forall z, t z = false \/ abs_le z m }.

  Definition ZBtape_mv (d : dir) : ZB_tape -> ZB_tape.
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

  Definition ZBtape_rd (t : ZB_tape) := Ztape_rd (proj1_sig t).

  Definition ZBtape_wr (b : bool) : ZB_tape -> ZB_tape.
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

  Fact ZBtape_bisim t1 t2 : bisim ZBtape_rd ZBtape_mv t1 t2
                        <-> bisim Ztape_rd Ztape_mv (proj1_sig t1) (proj1_sig t2).
  Proof.
    split; intros H l; specialize (H l); revert H; unfold ZBtape_rd;
    rewrite !ZBtape_moves_eq; auto.
  Qed.

  Definition Tape_ZB : TapeSpec.
  Proof.
    exists _ ZBtape_mv ZBtape_rd ZBtape_wr.
    + intros t b; unfold ZBtape_rd.
      rewrite ZBtape_wr_eq; apply (@read_write Tape_Z). 
    + intro t; apply ZBtape_bisim. 
      rewrite ZBtape_wr_eq.
      apply (@write_read Tape_Z).
    + intros t n d b; unfold ZBtape_rd.
      rewrite !ZBtape_iter_eq, ZBtape_wr_eq.
      apply (@move_write Tape_Z).
    + intros t b c; apply ZBtape_bisim.
      rewrite !ZBtape_wr_eq.
      apply (@write_write Tape_Z).
    + intro; apply ZBtape_bisim.
      rewrite !ZBtape_mv_eq.
      apply (@left_right Tape_Z).
    + intro; apply ZBtape_bisim.
      rewrite !ZBtape_mv_eq.
      apply (@right_left Tape_Z).
  Defined.

End Ztape_bounded.

(** This is LPO *)

Definition LPO := forall f : nat -> bool, { n | f n = true } + { forall n, f n = false }.

(** This is bounded LPO *)

Definition BLPO := forall f : nat -> bool, (exists m, forall n, m <= n -> f n = false)
                                        -> { n | f n = true } + { forall n, f n = false }.

Section XM_LPO.

  (** * LPO entails BLPO (trivial)
      * LPO is consistent because it follows from strong XM *)

  Fact LPO_BLPO : LPO -> BLPO.
  Proof. intros H f _; apply H. Qed.

  Hypothesis XM : forall P : Prop, P + ~ P.

  Fact strong_XM_LPO : LPO.
  Proof. 
    intros f.
    destruct (XM (exists n, f n = true)) as [ H | H ].
    + apply minimize in H as (n & ? & _).
      * left; eauto.
      * intro; apply bool_dec.
    + right; intros n.
      case_eq (f n); auto; intros E.
      destruct H; eauto.
  Qed.

End XM_LPO.

Definition lift_Z (f : nat -> bool) z :=
  match z with
    | pos n => f n
    | _     => false
  end.

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

Section SEARCH_LPO.

  Hint Resolve bool_dec : core.

  Theorem Coq_dec_SEARCH_SBTM t : Coq_dec (SEARCH rt true Tape_SBTM t).
  Proof.
    revert t; intros ((l,b),r); unfold SEARCH.
    destruct b as [].
    1:{ left; exists 0; auto. }
    destruct in_dec with (l := r) (a := true)
      as [ H1 | H1 ]; auto.
    1:{ left.
        destruct In_nth with (1 := H1) (d := false)
          as (n & H2 & H3).
        exists (S n).
        rewrite sbtm_rd_mv_rt_nth; auto. }
    right.
    intros ([ |n ] & Hn); apply H1; try easy.
    rewrite sbtm_rd_mv_rt_nth in Hn.
    rewrite Hn.
    destruct (nth_in_or_default n r false) as [ | E ]; auto.
    now rewrite E in Hn.
  Qed. 

  Theorem Coq_dec_SEARCH_Z_entails_LPO : (forall t, Coq_dec (SEARCH rt true Tape_Z t)) -> LPO.
  Proof.
    intros H f.
    destruct (H (lift_Z f)) as [ H1 | H1 ]; [ left | right ].
    + apply minimize in H1 as ([ | n ] & Hn & _).
      * easy.
      * exists n; rewrite Hn, Ztape_read_iter_rt; auto.
      * intros; apply bool_dec.
    + intros n; case_eq (f n); auto; intros Hn; exfalso.
      apply H1; exists (S n); rewrite Ztape_read_iter_rt; auto.
  Qed.

  Theorem Coq_dec_SEARCH_ZB_BLPO : (forall t, Coq_dec (SEARCH rt true Tape_ZB t)) -> BLPO.
  Proof.
    intros H f Hf.
    assert ({ t' : Tape_ZB | proj1_sig t' = lift_Z f}) as (t' & H').
    1: { refine (exist _ (exist _ (lift_Z f) _) eq_refl).
         destruct Hf as (m & Hm).
         exists m; intros [ | | n ]; auto; simpl.
         destruct (le_lt_dec m n); auto. }
    destruct (H t') as [ H1 | H1 ]; [ left | right ].
    + apply minimize in H1 as (n & Hn & _).
      * unfold Tape_ZB in Hn; simpl in Hn; unfold ZBtape_rd in Hn.
        rewrite ZBtape_iter_eq, H' in Hn.
        destruct n as [ | n ].
        - easy.
        - rewrite Ztape_read_iter_rt in Hn.
          exists n; auto.
      * intros; apply bool_dec.
    + intros n; case_eq (f n); auto; intros Hn; exfalso.
      apply H1; exists (S n).
      unfold Tape_ZB, read, move, ZBtape_rd.
      generalize (f_equal (Ztape_rd) (ZBtape_iter_eq (S n) rt t')).
      rewrite H', Ztape_read_iter_rt; simpl.
      rewrite Hn; intros <-; auto.
  Qed.

  Fact Tape_ZB_SBTM : forall t : tape Tape_ZB, exists t' : tape Tape_SBTM, t ~b t'.
  Proof.
     intros (t & m & Hm).
     destruct (@fun_bounded_list _ (fun n => t (pos n)) false (S m)) as (r & Hr).
     1:{ intros n; destruct (Hm (pos n)); auto. }
     destruct (@fun_bounded_list _ (fun n => t (neg n)) false (S m)) as (l & Hl).
     1:{ intros n; destruct (Hm (neg n)); auto. }
     exists (l,t zero,r); intros lm.
     simpl; unfold ZBtape_rd.
     rewrite ZBtape_moves_eq; simpl.
     change (read ((@move Tape_Z)⇈lm t) = read ((@move Tape_SBTM)⇈lm (l,t zero, r))).
     rewrite !bs_read_moves_Z.
     destruct (moves2Z lm) as [ n | | n ]; unfold Ziter; auto.
     + rewrite sbtm_rd_mv_lft_nth, Ztape_read_iter_lft; auto.
     + rewrite sbtm_rd_mv_rt_nth, Ztape_read_iter_rt; auto.
  Qed.

  Theorem SEARCH_TM : TM_dec_on (SEARCH rt true) Tape_SBTM -> TM_dec_on (SEARCH rt true) Tape_ZB.
  Proof.
    intros (M & s & H1 & H2).
    exists M, s; split; auto.
    + intros t.
      destruct (Tape_ZB_SBTM t) as (t1 & Ht1).
      generalize (H1 t1).
      apply TM_HALT_bisimilar; auto.
    + intros t t' H.
      destruct (Tape_ZB_SBTM t) as (t1 & Ht1).
      destruct TM_compute_bisim with (1 := Ht1) (2 := H)
        as (t1' & H3 & H4).
      apply H2 in H3.
      apply bs_read in H4 as ->.
      rewrite H3; symmetry.
      split; intros (n & Hn); exists n; revert Hn; intros ->; apply bs_read, bs_moves_dir; auto.
      apply bisimilar_sym; auto.
  Qed.

  (** If (P := SEARCH rt true Tape_SBTM) can be computed by a Turing machine
      then we have BLPO. Assuming BLPO is not derivable w/o further axioms, 
      this means that we have 
        - P is Coq decidable
        - one cannot build a Turing machine for deciding P (w/o further axioms)

      What are the consequence wrt Church thesis ?
    *) 

  Hint Resolve Coq_dec_SEARCH_ZB_BLPO TM_dec_on_Coq_dec SEARCH_TM : core.

  Corollary SEARCH_SBTM_BLPO : TM_dec_on (SEARCH rt true) Tape_SBTM -> BLPO.
  Proof. auto. Qed. 

End SEARCH_LPO.

Check Coq_dec_SEARCH_SBTM.
Print Assumptions Coq_dec_SEARCH_SBTM.

Check SEARCH_SBTM_BLPO.
Print Assumptions SEARCH_SBTM_BLPO.
 


  