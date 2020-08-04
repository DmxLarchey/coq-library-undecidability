Require Import ZArith Lia List.

Set Implicit Arguments.

Section length_eq_ind.

  Variable (X : Type) (P : list X -> list X -> Prop)
           (H0 : P nil nil) (H1 : forall x y l m, P l m -> P (x::l) (y::m)).

  Theorem length_eq_ind l m : length l = length m -> P l m.
  Proof.
    revert m; induction l as [ | x l IHl ]; intros [ | y m ]; try discriminate; auto.
  Qed.

End length_eq_ind.


Fact list_snoc {X} (l : list X) : { x & { m | l = m++x::nil } } + { l = nil }.
Proof.
  rewrite <- (rev_involutive l).
  destruct (rev l) as [ | x m ].
  + right; auto.
  + left; exists x, (rev m); auto.
Qed.

Fact list_decomp_0 {X} (ll : list X) n :
           { l : _ & { m | ll = l++m /\ length l = n } }
         + { length ll < n }.
Proof.
  revert n; induction ll as [ | x ll IHll ]; intros [ | n ].
  + left; exists nil, nil; auto.
  + right; simpl; lia.
  + left; exists nil, (x::ll); simpl; auto.
  + destruct (IHll n) as [ (l & m & ? & ?) | H ].
    * left; exists (x::l), m; simpl; subst; auto.
    * right; simpl; lia.
Qed.

Fact list_decomp_1 {X} (ll : list X) n : 0 < n ->
           { l : _ & { x : _ & { m | ll = l++x::m /\ S (length l) = n } } }
         + { S (length ll) = n }
         + { 2+length ll <= n }.
Proof.
  intros H.
  destruct (list_decomp_0 ll n) as [ (l & m & H1 & H2) | H1 ].
  + destruct (list_snoc l) as [ (x & l' & ->) | C ].
    * left; left; subst; exists l', x, m; rewrite app_ass, app_length; simpl.
      split; auto; lia.
    * exfalso; subst; simpl in *; lia.
  + destruct (eq_nat_dec n (S (length ll))).
    * left; right; lia.
    * right; lia.
Qed.

Reserved Notation "f ↑ n" (at level 1, format "f ↑ n").
Reserved Notation "x ↟ n" (at level 1, format "x ↟ n").

Section iter.

  Variable (X : Type).

  Definition repeat (x : X) := fix loop n :=
    match n with 
      | 0 => nil
      | S n => x::loop n
    end.

  Notation "x ↟ n" := (repeat x n).

  Fact repeat_plus x n m : x↟(n+m) = x↟n ++ x↟m.
  Proof. induction n; simpl; f_equal; auto. Qed.

  Fact repeat_S x n : x↟(S n) = x↟n ++ x :: nil.
  Proof. replace (S n) with (n+1) by lia; now rewrite repeat_plus. Qed.
  
  Fact repeat_length x n : length (x↟n) = n.
  Proof. induction n; simpl; lia. Qed.

  Variable (f : X -> X).

  Fixpoint iter n x :=
    match n with
      | 0   => x
      | S n => iter n (f x)
    end.

  Fact iter_succ n x : iter (S n) x = iter n (f x).
  Proof. auto. Qed.

  Fact iter_plus n m x : iter n (iter m x) = iter (m+n) x.
  Proof. revert x; induction m; simpl; auto. Qed.

  Fact iter_S n x : iter (S n) x = f (iter n x).
  Proof.
    replace (S n) with (n+1) by lia.
    rewrite <- iter_plus; auto.
  Qed.

End iter.

Notation "f ↑ n" := (@iter _ f n). 
Notation "x ↟ n" := (@repeat _ x n).

Fact repeat_option_choose {X} (l : list (option X)) :
           { n : _ & { x : _ & { m | l = None↟n ++ Some x :: m } } }
         + { l = None↟(length l) }. 
Proof.
  induction l as [ | [x|] l IHl ].
  + right; auto.
  + left; exists 0, x, l; auto.
  + destruct IHl as [ (n & y & m & ->) | -> ].
    * left; exists (S n), y, m; auto.
    * right; simpl; rewrite repeat_length; auto.
Qed.

Open Scope Z_scope.

Print Z.

Section quotient.

  Variable (X : Type).

  Inductive q_tape :=    (* for quotient tape *)
    | qt_emp : q_tape
    | qt_lft : q_tape -> q_tape
    | qt_rt  : q_tape -> q_tape
    | qt_wr  : q_tape -> X -> q_tape.

  (* negative are on the lft of the head *)

  Fixpoint qt_rdZ t i :=
    match t with
      | qt_emp    => None
      | qt_lft t  => qt_rdZ t (i-1)
      | qt_rt  t  => qt_rdZ t (i+1)
      | qt_wr t x => match i with 
                       | Z0 => Some x
                       | _  => qt_rdZ t i
                     end
    end.

  Definition qt_eq s t := forall i, qt_rdZ s i = qt_rdZ t i.

  Infix "~qt" := qt_eq (at level 70).

  Fact qt_eq_refl t : t ~qt t.
  Proof. red; auto. Qed.

  Fact qt_eq_sym s t : s ~qt t -> t ~qt s.
  Proof. red; auto. Qed.

  Fact qt_eq_trans r s t : r ~qt s -> s ~qt t -> r ~qt t.
  Proof. unfold qt_eq; intros H1 H2 ?; rewrite H1; auto. Qed.

End quotient.

Infix "~qt" := (@qt_eq _) (at level 70).
Arguments qt_emp {X}.

Section iterZ.

  Variable (X : Type) (l : X -> X) (r : X -> X) 
           (Hlr : forall x, l (r x) = x) (Hrl : forall x, r (l x) = x).

  Fixpoint iterZ i x :=
    match i with
      | Z0     => x
      | Zpos n => iter r (Pos.to_nat n) x
      | Zneg n => iter l (Pos.to_nat n) x
    end.

  Fact iterZ_0 x : iterZ 0 x = x.
  Proof. auto. Qed.

  Fact iterZ_r x : iterZ 1 x = r x.
  Proof. auto. Qed.

  Fact iterZ_l x : iterZ (-1) x = l x.
  Proof. auto. Qed.

  Fact iterZ_plus i j x : iterZ i (iterZ j x) = iterZ (j+i) x.
  Proof.
    (* Not that easy *)
  Admitted.

  Fact iterZ_abs_r i x : 0 <= i -> iterZ i x = iter r (Z.abs_nat i) x.
  Proof.
  Admitted.

  Fact iterZ_abs_l i x : i <= 0 -> iterZ i x = iter l (Z.abs_nat i) x.
  Proof.
  Admitted.

End iterZ.

Section tapes.

  (** Some ideas for axiomatized tapes *)

  Variable Σ : Type.

  (** tape where reads and writes can occur at any position (Z) relative
      to the current position (Z) *) 

  Record tape_Z : Type := {
    tpZ    :> Type;
    tpZ_rd : tpZ -> Z -> option Σ;
    tpZ_wr : tpZ -> Z -> Σ -> tpZ;
    tpZ_mv : tpZ -> Z -> tpZ;
    tpZ_rd_mv : forall t i j, tpZ_rd (tpZ_mv t i) j = tpZ_rd t (j-i);
    tpZ_wr_mv : forall t i j a, tpZ_wr (tpZ_mv t i) j a = tpZ_mv (tpZ_wr t (j-i) a) i;
    tpZ_mv_mv : forall t i j, tpZ_mv (tpZ_mv t i) j = tpZ_mv t (i+j);
    tpZ_rd_wr_eq : forall t i j a, i = j -> tpZ_rd (tpZ_wr t i a) j = Some a;
    tpZ_rd_wr_neq : forall t i j a, i <> j -> tpZ_rd (tpZ_wr t i a) j = tpZ_rd t j;
 (*   tpZ_nil : tpZ;
    tpZ_nil_spec : forall i, tpZ_rd tpZ_nil i = None;
    tpZ_ext : forall t t', (forall i, tpZ_rd t i = tpZ_rd t' i) -> t = t';           (* Extensionnality *)
    tpZ_fin : forall t, exists n, forall i, n < Z.abs i -> tpZ_rd t i = None;       (* Tape is logically finite *) *)
  }.

  Section tape_Z_props.

    Variable T : tape_Z.

    Implicit Type t : tpZ T.

    Fact tpZ_mv_wr t i j a : tpZ_mv _ (tpZ_wr _ t i a) j = tpZ_wr _ (tpZ_mv _ t j) (i+j) a.
    Proof. rewrite tpZ_wr_mv; do 2 f_equal; ring. Qed.

  End tape_Z_props.

  (** tape where reads/writes occur at the current position *)

  Record tape_0 : Type := {
    tp0    :> Type;
    tp0_rd0 : tp0 -> option Σ;
    tp0_wr0 : tp0 -> Σ -> tp0;
    tp0_lft : tp0 -> tp0;                        (* -1 *)
    tp0_rt  : tp0 -> tp0;                        (* +1 *)
    tp0_lr  : forall t, tp0_lft (tp0_rt t) = t;
    tp0_rl  : forall t, tp0_rt (tp0_lft t) = t;
    tp0_rd_wr : forall t a, tp0_rd0 (tp0_wr0 t a) = Some a;
    tp0_rd_lwr : forall t n a, (0 < n)%nat -> tp0_rd0 (iter tp0_lft n (tp0_wr0 t a)) 
                                            = tp0_rd0 (iter tp0_lft n t);
    tp0_rd_rwr : forall t n a, (0 < n)%nat -> tp0_rd0 (iter tp0_rt  n (tp0_wr0 t a)) 
                                            = tp0_rd0 (iter tp0_rt  n t);
  }.

  Section tape_0_props.

    (* Building a tape_Z with a tape_0 *)

    Variable T : tape_0.

    Implicit Type t : tp0 T.

    Definition tp0_mv t i := iterZ (tp0_lft _) (tp0_rt _) i t.

    Definition tp0_rd t i := tp0_rd0 _ (tp0_mv t (-i)).
    Definition tp0_wr t i a := tp0_mv (tp0_wr0 _ (tp0_mv t (-i)) a) i.

    Hint Resolve tp0_lr tp0_rl : core.

    Definition tp0_tp : tape_Z.
    Proof.
      exists (tp0 T) tp0_rd tp0_wr tp0_mv.
      + intros t i j; unfold tp0_rd, tp0_mv.
        rewrite iterZ_plus; do 2 f_equal; auto; lia.
      + intros t i j a; unfold tp0_wr, tp0_mv.
        rewrite !iterZ_plus; auto.
        f_equal; try lia.
        do 2 f_equal; lia.
      + intros t i j; unfold tp0_mv.
        rewrite iterZ_plus; auto.
      + intros t i j a <-.
        unfold tp0_rd, tp0_wr, tp0_mv.
        rewrite iterZ_plus; auto.
        replace (i+-i) with 0 by ring.
        rewrite iterZ_0.
        rewrite tp0_rd_wr; auto.
      + intros t i j a H.
        unfold tp0_rd, tp0_wr, tp0_mv.
        rewrite iterZ_plus; auto.
        destruct (Z_dec i j) as [ [ D | D ] | ]; try lia.
        * rewrite iterZ_abs_l; auto; try lia.
          rewrite tp0_rd_lwr; try lia.
          rewrite <- iterZ_abs_l with (r := tp0_rt _); auto; try lia.
          rewrite iterZ_plus; auto; do 2 f_equal; ring.
        * rewrite iterZ_abs_r; auto; try lia.
          rewrite tp0_rd_rwr; try lia.
          rewrite <- iterZ_abs_r with (l := tp0_lft _); auto; try lia.
          rewrite iterZ_plus; auto; do 2 f_equal; ring.
    Qed.

  End tape_0_props.

  (** tapes with blank cells: 
       - a,b,c for regular symbols in Σ
       - ?,x for either blank or reg. in option Σ
       - _ for blank in option Σ *)

  (* it_one x represents 
       a) either empty 
             _ _ [_] _ _    as  (it_one None)
       b) or exactly one non blank under the head
             _ _ [a] _ _    as (it_one (Some a))

     it_lft represents tapes which are entirely left of the head
          _ _ a ? ? ? [x] _ _   as (it_lft a [?;?;?] x)

     it_rt represents tapes which are entirely right of the head
          _ _ [x] ? ? ? b _ _   as (it_rt x [?;?;?] b)

     it_both represents tapes which are both left and right of the head
          _ a ? ? [x] ? ? b _   as (it_both a l x r b)

   *)

  Unset Elimination Schemes.

  Inductive i_tape : Type :=   (* for infinite tape *)
    | it_one  : option Σ -> i_tape
    | it_lft  : Σ -> list (option Σ) -> option Σ -> i_tape
    | it_rt   : option Σ -> list (option Σ) -> Σ -> i_tape
    | it_both : Σ -> list (option Σ) -> option Σ -> list (option Σ) -> Σ -> i_tape.

  Set Elimination Schemes.

  (* Moving left *)

  Definition mv_lft (t : i_tape) :=
    match t with
      | it_one None                     => it_one None                     (*  _ _ [_] _ _ ~~> _ [_] _ _ _ *)
      | it_one (Some a)                 => it_rt None nil a                (*  _ _ [a] _ _ ~~> _ [_] a _ _ *)

      | it_lft a nil         None       => it_one (Some a)                 (*  _ a [_] _ _ ~~> _ [a] _ _ _ *)
      | it_lft a nil         (Some b)   => it_rt (Some a) nil b            (*  _ a [b] _ _ ~~> _ [a] b _ _ *)
      | it_lft a (None::l)   None       => it_lft a l None                 (*  a _ [_] _ _ ~~> a [_] _ _ _ *)
      | it_lft a (x::l)   (Some b)      => it_both a l x nil b             (*  a x [b] _ _ ~~> a [x] b _ _ *)
      | it_lft a (Some b::l) None       => it_lft a l (Some b)             (*  a b [_] _ _ ~~> a [b] _ _ _ *)

      | it_rt x l a                     => it_rt None (x::l) a             (*  _ _ [x] ? a ~~> _ [_] x ? a *)

      | it_both a nil x r b             => it_rt (Some a) (x::r) b         (*  _ a [x] ? b ~~> _ [a] x ? b *)
      | it_both a (x::l) y r b          => it_both a l x (y::r) b          (*  a x [y] ? b ~~> a [x] y ? b *)
    end.

  (* Moving right *)

  Definition mv_rt (t : i_tape) :=
    match t with
      | it_one None                     => it_one None                     (*  _ _ [_] _ _ ~~> _ _ _ [_] _ *)
      | it_one (Some a)                 => it_lft a nil None               (*  _ _ [a] _ _ ~~> _ _ a [_] _ *)

      | it_lft a l x                    => it_lft a (x::l) None            (*  a ? [x] _ _ ~~> a ? x [_] _ *)

      | it_rt None     nil     a        => it_one (Some a)                 (*  _ _ [_] a _ ~~> _ _ _ [a] _ *)
      | it_rt (Some a) nil     b        => it_lft a nil (Some b)           (*  _ _ [a] b _ ~~> _ _ a [b] _ *)
      | it_rt None     (None::l) b      => it_rt None l b                  (*  _ _ [_] _ b ~~> _ _ _ [_] b *)
      | it_rt (Some a) (x::l) b         => it_both a nil x l b             (*  _ _ [a] x b ~~> _ _ a [x] b *)
      | it_rt None     (Some a::l) b    => it_rt (Some a) l b              (*  _ _ [_] a b ~~> _ _ _ [a] b *)
 
      | it_both a l x nil b             => it_lft a (x::l) (Some b)        (*  a ? [x] b _ ~~> a ? x [b] _ *)
      | it_both a l x (y::r) b          => it_both a (x::l) y r b          (*  a ? [x] y b ~~> a ? x [y] b *)
    end.

  Definition rd (t : i_tape) :=
    match t with
      | it_one x          => x
      | it_lft _ _ x      => x
      | it_rt x _ _       => x
      | it_both _ _ x _ _ => x
    end.

  Definition wr (t : i_tape) c :=
    match t with
      | it_one _          => it_one (Some c)
      | it_lft a l _      => it_lft a l (Some c)
      | it_rt _ l b       => it_rt (Some c) l b
      | it_both a l _ r b => it_both a l (Some c) r b
    end.

  (* Left/right moves are strict inverse to each other *)

  Fact mv_lft_rt t : mv_lft (mv_rt t) = t.
  Proof. now destruct t as [ [] | ? [ | [] ] [] | [] [ | [] ] ? | ? [] [] [] ? ]. Qed.

  Fact mv_rt_lft t : mv_rt (mv_lft t) = t.
  Proof. now destruct t as [ [] | ? [ | [] ] [] | [] [ | [] ] ? | ? [] [] [] ? ]. Qed.

  Open Scope nat_scope.

  Section itape_rect.

    Variable (P : i_tape -> Type)
             (HP_nil  : P (it_one None))
             (HP_wr : forall c t, P t -> P (wr t c))
             (HP_lft : forall t, P t -> P (mv_lft t))
             (HP_rt : forall t, P t -> P (mv_rt t)).

    Let P_one x : P (it_one x).
    Proof.
      destruct x as [c|]; auto.
      apply HP_wr with (1 := HP_nil).
    Qed.

    Let P_lft a l x : P (it_lft a l x).
    Proof.
      revert x; induction l as [ | y l IHl ]; intros [c|].
      + apply HP_wr with (t := it_lft a nil None).
        apply HP_rt with (1 := P_one (Some a)).
      + apply HP_rt with (1 := P_one (Some a)).
      + apply HP_wr with (t := it_lft a (y::l) None).
        apply HP_rt with (t := it_lft a l y); auto.
      + apply HP_rt with (t := it_lft a l y); auto.
    Qed.

    Let P_rt x r b : P (it_rt x r b).
    Proof.
      revert x; induction r as [ | y r IHr ]; intros [c|].
      + apply HP_wr with (t := it_rt None nil b).
        apply HP_lft with (1 := P_one (Some b)).
      + apply HP_lft with (1 := P_one (Some b)).
      + apply HP_wr with (t := it_rt None (y::r) b).
        apply HP_lft with (t := it_rt y r b); auto.
      + apply HP_lft with (t := it_rt y r b); auto.
    Qed.

    Let P_both a l x r b : P (it_both a l x r b).
    Proof.
      revert a x r; induction l as [ | y l IHl ]; intros a x r.
      + apply HP_rt with (t := it_rt (Some a) (x::r) b); auto.
      + apply HP_rt with (t := it_both a l y (x::r) b); auto.
    Qed.

    (* Any itape can be build with the nil, wr, lft and rt constructors *)

    Theorem i_tape_rect t : P t.
    Proof. destruct t; auto. Qed.

  End itape_rect.

  Fact rd_wr t c : rd (wr t c) = Some c.
  Proof. now destruct t as [ [] | ? [ | [] ] [] | [] [ | [] ] ? | ? [] [] [] ? ]. Qed.

  Fact iter_lft_it_rt_0 r b n : mv_lft↑n (it_rt None r b) = it_rt None (None↟n++r) b.
  Proof.
    revert r; induction n as [ | n IHn ]; simpl; auto; intros r.
    rewrite IHn; f_equal.
    change (None::None↟n++r) with (None↟(S n)++r).
    rewrite repeat_S, app_ass; auto.
  Qed.

  Fact iter_rt_it_lft_0 a l n : mv_rt↑n (it_lft a l None) = it_lft a (None↟n++l) None.
  Proof.
    revert l; induction n as [ | n IHn ]; simpl; auto; intros l.
    rewrite IHn; f_equal.
    change (None::repeat None n++l) with (repeat None (S n)++l).
    rewrite repeat_S, app_ass; auto.
  Qed.

  Fact iter_lft_it_rt_1 x r b n : mv_lft↑(S n) (it_rt x r b) = it_rt None (None↟n++x::r) b.
  Proof. simpl iter at 1; now rewrite iter_lft_it_rt_0. Qed.

  Fact iter_rt_it_lft_1 a l x n : mv_rt↑(S n) (it_lft a l x) = it_lft a (None↟n++x::l) None.
  Proof. simpl iter at 1; now rewrite iter_rt_it_lft_0. Qed.

  Fact iter_lft_it_one_0 n : mv_lft↑n (it_one None) = it_one None.
  Proof. induction n; simpl; f_equal; auto. Qed.

  Fact iter_rt_it_one_0 n : mv_rt↑n (it_one None) = it_one None.
  Proof. induction n; simpl; f_equal; auto. Qed.

  Fact iter_lft_it_one_1 b n : mv_lft↑(S n) (it_one (Some b)) = it_rt None (None↟n) b.
  Proof. simpl iter at 1; now rewrite iter_lft_it_rt_0, <- app_nil_end. Qed.

  Fact iter_rt_it_one_1 a n : mv_rt↑(S n) (it_one (Some a)) = it_lft a (None↟n) None.
  Proof. simpl iter at 1; now rewrite iter_rt_it_lft_0, <- app_nil_end. Qed.

  Fact iter_lft_it_both_0 a l y m x r b n : 
          S (length l) = n 
       -> mv_lft↑n (it_both a (l++y::m) x r b) = it_both a m y (rev l++x::r) b.
  Proof.
    revert l y m x r; induction n as [ | n IHn ]; intros l y m x r; try discriminate; intros H.
    injection H; clear H; intros H.
    destruct l as [ | z l ].
    + simpl in H; subst n; simpl; auto.
    + simpl in H.
      simpl iter.
      rewrite IHn with (1 := H); f_equal.
      simpl rev; rewrite app_ass; auto.
  Qed.

  Fact iter_rt_it_both_0 a l x r y m b n : 
          S (length r) = n 
       -> mv_rt↑n (it_both a l x (r++y::m) b) = it_both a (rev r++x::l) y m b.
  Proof.
    revert l y m x r; induction n as [ | n IHn ]; intros l y m x r; try discriminate; intros H.
    injection H; clear H; intros H.
    destruct r as [ | z r ].
    + simpl in H; subst n; simpl; auto.
    + simpl in H.
      simpl iter.
      rewrite IHn with (1 := H); f_equal.
      simpl rev; rewrite app_ass; auto.
  Qed.

  Fact iter_lft_it_both_1 a l x r b n :
         S (length l) = n
       -> mv_lft↑n (it_both a l x r b) = it_rt (Some a) (rev l++x::r) b.
  Proof.
    intros H.
    destruct (list_snoc l) as [ (y & m & ->) | -> ].
    + rewrite app_length in H; simpl in H.
      replace n with ((S (length m)) + 1) at 1.
      rewrite <- iter_plus, iter_lft_it_both_0 with (1 := eq_refl).
      simpl; f_equal; rewrite rev_app_distr, app_ass; auto.
    + simpl in H; subst n; simpl; auto.
  Qed.

  Fact iter_rt_it_both_1 a l x r b n :
         S (length r) = n
       -> mv_rt↑n (it_both a l x r b) = it_lft a (rev r++x::l) (Some b).
  Proof.
    intros H.
    destruct (list_snoc r) as [ (y & m & ->) | -> ].
    + rewrite app_length in H; simpl in H.
      replace n with ((S (length m)) + 1) at 1.
      rewrite <- iter_plus, iter_rt_it_both_0 with (1 := eq_refl).
      simpl; f_equal; rewrite rev_app_distr, app_ass; auto.
    + simpl in H; subst n; simpl; auto.
  Qed.

  Fact iter_lft_it_both_2 a l x r b n :
          2+length l <= n
       -> mv_lft↑n (it_both a l x r b)
        = it_rt None (None↟(n-2-length l)++Some a::rev l++x::r) b.
  Proof.
    intros Hn.
    replace n with (1+length l+(1+(n-2-length l))) by lia.
    rewrite <- iter_plus, iter_lft_it_both_1 with (1 := eq_refl), <- iter_plus.
    simpl; rewrite iter_lft_it_rt_0; do 3 f_equal; lia.
  Qed.

  Fact iter_rt_it_both_2 a l x r b n :
          2+length r <= n
       -> mv_rt↑n (it_both a l x r b)
        = it_lft a (None↟(n-2-length r)++Some b::rev r++x::l) None.
  Proof.
    intros Hn.
    replace n with (1+length r+(1+(n-2-length r))) by lia.
    rewrite <- iter_plus, iter_rt_it_both_1 with (1 := eq_refl), <- iter_plus.
    simpl; rewrite iter_rt_it_lft_0; do 3 f_equal; lia.
  Qed.

  Fact iter_lft_it_lft_0 a x m n : 
          mv_lft↑(S n) (it_lft a (None↟n++x::m) None) = it_lft a m x.
  Proof.
    induction n as [ | n IHn ].
    + destruct x; auto.
    + rewrite iter_succ; auto.
  Qed.

  Fact iter_rt_it_rt_0 b x m n : 
          mv_rt↑(S n) (it_rt None (None↟n++x::m) b) = it_rt x m b.
  Proof.
    induction n as [ | n IHn ].
    + destruct x; auto.
    + rewrite iter_succ; auto.
  Qed.

  Fact iter_lft_it_lft_0' a n : 
          mv_lft↑(S n) (it_lft a (None↟n) None) = it_one (Some a).
  Proof.
    induction n as [ | n IHn ].
    + simpl; auto.
    + rewrite iter_succ; auto.
  Qed.

  Fact iter_rt_it_rt_0' b n : 
         mv_rt↑(S n) (it_rt None (None↟n) b) = it_one (Some b).
  Proof.
    induction n as [ | n IHn ].
    + simpl; auto.
    + rewrite iter_succ; auto.
  Qed.

  Fact iter_lft_it_lft_1 a l x m b n : 
          S (length l) = n 
       -> mv_lft↑n (it_lft a (l++x::m) (Some b)) = it_both a m x (rev l) b.
  Proof.
    intros <-.
    simpl iter.
    destruct l as [ | y l ]; simpl.
    + destruct x; auto.
    + replace (match y with |Some _ | _ => it_both a (l ++ x :: m) y nil b end)
      with (it_both a (l ++ x :: m) y nil b) by (destruct y; auto).
      rewrite <- iter_lft_it_both_0 with (r := nil) (1 := eq_refl); auto.
  Qed.

  Fact iter_rt_it_rt_1 a r x m b n : 
          S (length r) = n 
       -> mv_rt↑n (it_rt (Some a) (r++x::m) b) = it_both a (rev r) x m b.
  Proof.
    intros <-.
    simpl iter.
    destruct r as [ | y r ].
    + simpl; auto.
    + match goal with |- _↑_ ?e = _ => change e with (it_both a nil y (r++x::m) b) end.
      apply iter_rt_it_both_0; auto.
  Qed.

  Fact iter_lft_it_lft_2 a l b n : 
          S (length l) = n 
       -> mv_lft↑n (it_lft a l (Some b)) = it_rt (Some a) (rev l) b.
  Proof.
    intros H.
    destruct (list_snoc l) as [ (y & m & ->) | -> ].
    + rewrite app_length in H; simpl in H.
      replace n with ((S (length m)) + 1) at 1.
      rewrite <- iter_plus, iter_lft_it_lft_1 with (1 := eq_refl).
      simpl; f_equal; rewrite rev_app_distr; auto.
    + simpl in H; subst n; simpl; auto.
  Qed.

  Fact iter_rt_it_rt_2 a r b n : 
          S (length r) = n 
       -> mv_rt↑n (it_rt (Some a) r b) = it_lft a (rev r) (Some b).
  Proof.
    intros H.
    destruct (list_snoc r) as [ (y & m & ->) | -> ].
    + rewrite app_length in H; simpl in H.
      replace n with ((S (length m)) + 1) at 1.
      rewrite <- iter_plus, iter_rt_it_rt_1 with (1 := eq_refl).
      simpl; f_equal; rewrite rev_app_distr; auto.
    + simpl in H; subst n; simpl; auto.
  Qed.

  Fact iter_lft_it_lft_3 a l b n : 
          2+length l <= n 
       -> mv_lft↑n (it_lft a l (Some b)) = it_rt None (None↟(n-2-length l)++Some a::rev l) b.
  Proof.
    intros Hn.
    replace n with (1+length l+(1+(n-2-length l))) by lia.
    rewrite <- iter_plus, iter_lft_it_lft_2 with (1 := eq_refl), <- iter_plus.
    simpl; rewrite iter_lft_it_rt_0; do 3 f_equal; lia.
  Qed.

  Fact iter_rt_it_rt_3 a r b n : 
          2+length r <= n 
       -> mv_rt↑n (it_rt (Some a) r b) = it_lft a (None↟(n-2-length r)++Some b::rev r) None.
  Proof.
    intros Hn.
    replace n with (1+length r+(1+(n-2-length r))) by lia.
    rewrite <- iter_plus, iter_rt_it_rt_2 with (1 := eq_refl), <- iter_plus.
    simpl; rewrite iter_rt_it_lft_0; do 3 f_equal; lia.
  Qed.

  Fact rd_lft_one n x : rd (mv_lft↑(S n) (it_one x)) = None.
  Proof.
    destruct x as [ x | ].
    + rewrite iter_lft_it_one_1; auto.
    + rewrite iter_lft_it_one_0; auto.
  Qed.

  Fact rd_lft_rt n x r b : rd (mv_lft↑(S n) (it_rt x r b)) = None.
  Proof.
    destruct x as [ x | ].
    + rewrite iter_lft_it_rt_1; auto.
    + rewrite iter_lft_it_rt_0; auto.
  Qed.

  Fact rd_rt_one n x : rd (mv_rt↑(S n) (it_one x)) = None.
  Proof.
    destruct x as [ x | ].
    + rewrite iter_rt_it_one_1; auto.
    + rewrite iter_rt_it_one_0; auto.
  Qed.

  Fact rd_rt_lft n a l x : rd (mv_rt↑(S n) (it_lft a l x)) = None.
  Proof.
    destruct x as [ x | ].
    + rewrite iter_rt_it_lft_1; auto.
    + rewrite iter_rt_it_lft_0; auto.
  Qed.

  Fact rd_lft_eq_rt_one n x r b :
        rd (mv_lft↑n (it_rt x r b)) = rd (mv_lft↑n (it_one x)).
  Proof.
    destruct n as [ | n ]; auto.
    rewrite iter_lft_it_rt_1; auto.
    destruct x as [ x | ]. 
    + rewrite iter_lft_it_one_1; auto.
    + rewrite iter_lft_it_one_0; auto.
  Qed.

  Fact rd_rt_eq_lft_one n a l x :
        rd (mv_rt↑n (it_lft a l x)) = rd (mv_rt↑n (it_one x)).
  Proof.
    destruct n as [ | n ]; auto.
    rewrite iter_rt_it_lft_1; auto.
    destruct x as [ x | ]. 
    + rewrite iter_rt_it_one_1; auto.
    + rewrite iter_rt_it_one_0; auto.
  Qed.

  Fact rd_lft_eq_both_both n a l x r1 r2 b1 b2 :
        rd (mv_lft↑n (it_both a l x r1 b1)) = rd (mv_lft↑n (it_both a l x r2 b2)).
  Proof.
    destruct n as [ | n ]; auto.
    destruct (@list_decomp_1 _ l (S n))
      as [ [ (l' & y & m & -> & H2) | H1 ] | H1 ]; try lia.
    + rewrite !iter_lft_it_both_0; auto.
    + rewrite !iter_lft_it_both_1; auto.
    + rewrite !iter_lft_it_both_2; auto.
  Qed.

  Fact rd_rt_eq_both_both n a1 a2 l1 l2 x r b :
        rd (mv_rt↑n (it_both a1 l1 x r b)) = rd (mv_rt↑n (it_both a2 l2 x r b)).
  Proof.
    destruct n as [ | n ]; auto.
    destruct (@list_decomp_1 _ r (S n))
      as [ [ (r' & y & m & -> & H2) | H1 ] | H1 ]; try lia.
    + rewrite !iter_rt_it_both_0; auto.
    + rewrite !iter_rt_it_both_1; auto.
    + rewrite !iter_rt_it_both_2; auto.
  Qed.

  Fact rd_lft_eq_rt_rt n x r1 r2 b1 b2 :
        rd (mv_lft↑n (it_rt x r1 b1)) = rd (mv_lft↑n (it_rt x r2 b2)).
  Proof.
    destruct n as [ | n ]; auto.
    rewrite !iter_lft_it_rt_1; auto.
  Qed.

  Fact rd_rt_eq_lft_lft n x l1 l2 a1 a2 :
        rd (mv_rt↑n (it_lft a1 l1 x)) = rd (mv_rt↑n (it_lft a2 l2 x)).
  Proof.
    destruct n as [ | n ]; auto.
    rewrite !iter_rt_it_lft_1; auto.
  Qed.

  Fact rd_lft_eq_both_lft_Some n a l x r b :
        rd (mv_lft↑n (it_both a l (Some x) r b)) = rd (mv_lft↑n (it_lft a l (Some x))).
  Proof.
    destruct n as [ | n ]; auto.
    destruct l as [ | y l ]; simpl.
    + apply rd_lft_eq_rt_rt.
    + destruct y; apply rd_lft_eq_both_both.
  Qed.

  Fact rd_rt_eq_both_rt_Some n a l x r b :
        rd (mv_rt↑n (it_both a l (Some x) r b)) = rd (mv_rt↑n (it_rt (Some x) r b)).
  Proof.
    destruct n as [ | n ]; auto.
    destruct r as [ | y r ]; simpl.
    + apply rd_rt_eq_lft_lft.
    + destruct y; apply rd_rt_eq_both_both.
  Qed.

  Fact rd_lft_eq_both_lft n a l x r b :
        rd (mv_lft↑n (it_both a l x r b)) = rd (mv_lft↑n (it_lft a l x)).
  Proof.
    destruct n as [ | n ]; auto.
    destruct x as [ x | ].
    + apply rd_lft_eq_both_lft_Some.
    + destruct (repeat_option_choose l) as [ (k & x & m & ->) | -> ].
      * destruct (le_lt_dec k n) as [ H | H ].
        - replace (S n) with (S k + (S n - S k)) by lia.
          rewrite <- !iter_plus.
          rewrite iter_lft_it_both_0 by now rewrite repeat_length.
          rewrite iter_lft_it_lft_0.
          apply rd_lft_eq_both_lft_Some.
        - replace k with (n+(1+(k-S n))) by lia.
          rewrite !repeat_plus, !app_ass. 
          simpl repeat; simpl app.
          rewrite iter_lft_it_both_0, iter_lft_it_lft_0; auto.
          now rewrite repeat_length.
      * generalize (length l); clear l; intros k.
        destruct (le_lt_dec k n) as [ H | H ].
        - replace (S n) with (S k + (S n - S k)) by lia.
          rewrite <- !iter_plus.
          rewrite iter_lft_it_both_1 by now rewrite repeat_length.
          rewrite iter_lft_it_lft_0'.
          apply rd_lft_eq_rt_one.
        - replace k with (n+(1+(k-S n))) by lia.
          rewrite !repeat_plus.
          simpl repeat; simpl app.
          rewrite iter_lft_it_both_0, iter_lft_it_lft_0; auto.
          now rewrite repeat_length.
  Qed.

  Fact rd_rt_eq_both_rt n a l x r b :
        rd (mv_rt↑n (it_both a l x r b)) = rd (mv_rt↑n (it_rt x r b)).
  Proof.
    destruct n as [ | n ]; auto.
    destruct x as [ x | ].
    + apply rd_rt_eq_both_rt_Some.
    + destruct (repeat_option_choose r) as [ (k & x & m & ->) | -> ].
      * destruct (le_lt_dec k n) as [ H | H ].
        - replace (S n) with (S k + (S n - S k)) by lia.
          rewrite <- !iter_plus.
          rewrite iter_rt_it_both_0 by now rewrite repeat_length.
          rewrite iter_rt_it_rt_0.
          apply rd_rt_eq_both_rt_Some.
        - replace k with (n+(1+(k-S n))) by lia.
          rewrite !repeat_plus, !app_ass. 
          simpl repeat; simpl app.
          rewrite iter_rt_it_both_0, iter_rt_it_rt_0; auto.
          now rewrite repeat_length.
      * generalize (length r); clear r; intros k.
        destruct (le_lt_dec k n) as [ H | H ].
        - replace (S n) with (S k + (S n - S k)) by lia.
          rewrite <- !iter_plus.
          rewrite iter_rt_it_both_1 by now rewrite repeat_length.
          rewrite iter_rt_it_rt_0'.
          apply rd_rt_eq_lft_one.
        - replace k with (n+(1+(k-S n))) by lia.
          rewrite !repeat_plus.
          simpl repeat; simpl app.
          rewrite iter_rt_it_both_0, iter_rt_it_rt_0; auto.
          now rewrite repeat_length.
  Qed.

  Fact rd_lft_lft a l x : rd (mv_lft↑(S (length l)) (it_lft a l x)) = Some a.
  Proof.
    destruct x as [ x | ].
    + rewrite iter_lft_it_lft_2 with (1 := eq_refl); auto.
    + destruct (repeat_option_choose l) as [ (n & x & m & ->) | -> ].
      * rewrite app_length, repeat_length; simpl length.
        replace (S (n+S (length m))) with (S n + S (length m)) by lia.
        rewrite <- iter_plus.
        rewrite iter_lft_it_lft_0.
        rewrite iter_lft_it_lft_2 with (1 := eq_refl); auto.
      * rewrite repeat_length, iter_lft_it_lft_0'; auto.
  Qed.

  Fact rd_lft_nxt a y l x n : rd (mv_lft↑(S n) (it_lft a (y::l) x))
                            = rd (mv_lft↑n (it_lft a l y)).
  Proof.
    change (S n) with (1+n); rewrite <- iter_plus.
    destruct x; destruct y; simpl; auto; apply rd_lft_eq_both_lft.
  Qed.

  Fact rd_rt_nxt x y r b n : rd (mv_rt↑(S n) (it_rt x (y::r) b))
                           = rd (mv_rt↑n (it_rt y r b)).
  Proof.
    change (S n) with (1+n); rewrite <- iter_plus.
    destruct x; destruct y; simpl; auto; apply rd_rt_eq_both_rt.
  Qed.

  Fact rd_lft_out a l x n : 2+length l <= n -> rd (mv_lft↑n (it_lft a l x)) = None.
  Proof.
    intros H.
    destruct x as [ x | ].
    + rewrite iter_lft_it_lft_3 with (1 := H); auto.
    + destruct (repeat_option_choose l) as [ (k & x & m & ->) | -> ].
      * rewrite app_length, repeat_length in H; simpl length in H.
        replace n with (S k + (n - S k)) by lia.
        rewrite <- iter_plus.
        rewrite iter_lft_it_lft_0.
        rewrite iter_lft_it_lft_3; auto; lia.
      * replace n with ((S (length l)) + S (n-2-length l)) by lia.
        rewrite <- iter_plus.
        rewrite iter_lft_it_lft_0'; simpl.
        rewrite iter_lft_it_rt_0; auto.
  Qed.

  Fact rd_rt_out x r b n : 2+length r <= n -> rd (mv_rt↑n (it_rt x r b)) = None.
  Proof.
    intros H.
    destruct x as [ x | ].
    + rewrite iter_rt_it_rt_3 with (1 := H); auto.
    + destruct (repeat_option_choose r) as [ (k & x & m & ->) | -> ].
      * rewrite app_length, repeat_length in H; simpl length in H.
        replace n with (S k + (n - S k)) by lia.
        rewrite <- iter_plus.
        rewrite iter_rt_it_rt_0.
        rewrite iter_rt_it_rt_3; auto; lia.
      * replace n with ((S (length r)) + S (n-2-length r)) by lia.
        rewrite <- iter_plus.
        rewrite iter_rt_it_rt_0'; simpl.
        rewrite iter_rt_it_lft_0; auto.
  Qed.

  Fact rd_rt_rt x r b : rd (mv_rt↑(S (length r)) (it_rt x r b)) = Some b.
  Proof.
    destruct x as [ x | ].
    + rewrite iter_rt_it_rt_2 with (1 := eq_refl); auto.
    + destruct (repeat_option_choose r) as [ (n & x & m & ->) | -> ].
      * rewrite app_length, repeat_length; simpl length.
        replace (S (n+S (length m))) with (S n + S (length m)) by lia.
        rewrite <- iter_plus.
        rewrite iter_rt_it_rt_0.
        rewrite iter_rt_it_rt_2 with (1 := eq_refl); auto.
      * rewrite repeat_length, iter_rt_it_rt_0'; auto.
  Qed.

  Fact rd_lft_both a l x r b : rd (mv_lft↑(S (length l)) (it_both a l x r b)) = Some a.
  Proof. rewrite iter_lft_it_both_1; auto. Qed.

  Fact rd_rt_both a l x r b : rd (mv_rt↑(S (length r)) (it_both a l x r b)) = Some b.
  Proof. rewrite iter_rt_it_both_1; auto. Qed.

  (* These are the two essential results *)

  Theorem rd_lwr t n c : 0 < n -> rd (mv_lft↑n (wr t c)) = rd (mv_lft↑n t).
  Proof.
    intros Hn.
    destruct t as [ x | a ll x | x ll b | a ll x r b ].
    + simpl wr; destruct n as [ | n ]; try lia.
      rewrite iter_lft_it_one_1.
      destruct x as [ x | ].
      * rewrite iter_lft_it_one_1; auto.
      * rewrite iter_lft_it_one_0; auto.
    + simpl.
      destruct x as [ x | ].
      * destruct (list_decomp_1 ll) with (1 := Hn)
          as [ [ (l & y & m & -> & H2) | H1 ] | H1 ].
        - rewrite !iter_lft_it_lft_1 with (1 := H2); auto.
        - rewrite !iter_lft_it_lft_2; auto.
        - rewrite !iter_lft_it_lft_3; auto.
      * destruct (repeat_option_choose ll) as [ (n1 & y & m & ->) | H1 ].
        - destruct n as [ | n ]; try lia.
          destruct (lt_eq_lt_dec n n1) as [ [ H1 | <- ] | H1 ].
          ++ replace n1 with (n + (S (n1 - S n))) by lia.
             rewrite repeat_plus; simpl repeat. 
             rewrite app_ass; simpl app.
             rewrite iter_lft_it_lft_1; [ | rewrite repeat_length; auto ].
             rewrite iter_lft_it_lft_0; auto.
          ++ rewrite iter_lft_it_lft_1; [ | rewrite repeat_length; auto ].
             rewrite iter_lft_it_lft_0; auto.
          ++ replace (S n) with (S n1 + (S (n-S n1))) by lia.
             rewrite <- !iter_plus.
             rewrite iter_lft_it_lft_1; [ | rewrite repeat_length; auto ].
             rewrite iter_lft_it_lft_0; auto.
             generalize (n - S n1); clear n Hn H1; intros n.
             destruct (list_decomp_1 m) with (n := S n)
               as [ [ (l & z & m' & -> & H2) | H1 ] | H1 ]; try lia.
             ** rewrite iter_lft_it_both_0; auto.
                rewrite iter_lft_it_lft_1; auto.
             ** rewrite iter_lft_it_both_1; auto.
                rewrite iter_lft_it_lft_2; auto.
             ** rewrite iter_lft_it_both_2; auto.
                rewrite iter_lft_it_lft_3; auto.
        - rewrite H1; generalize (length ll); clear ll H1.
          intros n1.
          destruct n as [ | n ]; try lia.
          destruct (lt_eq_lt_dec n n1) as [ [ H1 | <- ] | H1 ].
          ++ replace n1 with (n + (S (n1 - S n))) by lia.
             rewrite repeat_plus; simpl repeat. 
             rewrite iter_lft_it_lft_1; [ | rewrite repeat_length; auto ].
             rewrite iter_lft_it_lft_0; auto.
          ++ rewrite iter_lft_it_lft_2; [ | rewrite repeat_length; auto ].
             rewrite iter_lft_it_lft_0'; auto.
          ++ replace (S n) with (S n1 + (S (n-S n1))) by lia.
             rewrite <- !iter_plus.
             rewrite iter_lft_it_lft_2; [ | rewrite repeat_length; auto ].
             rewrite iter_lft_it_lft_0'; auto.
             rewrite iter_lft_it_rt_1.
             rewrite iter_lft_it_one_1; auto.
    + simpl; destruct n as [ | n ]; try lia.
      rewrite !iter_lft_it_rt_1; auto.
    + simpl.
      destruct (list_decomp_1 ll) with (1 := Hn)
          as [ [ (l & y & m & -> & H2) | H1 ] | H1 ].
      - rewrite !iter_lft_it_both_0 with (1 := H2); auto.
      - rewrite !iter_lft_it_both_1; auto.
      - rewrite !iter_lft_it_both_2; auto.
  Qed.

  (* And the second one *)

  Theorem rd_rwr t n c : 0 < n -> rd (mv_rt↑n (wr t c)) = rd (mv_rt↑n t).
  Proof.
    intros Hn.
    destruct t as [ x | a ll x | x ll b | a l x rr b ].
    + simpl wr; destruct n as [ | n ]; try lia.
      rewrite iter_rt_it_one_1.
      destruct x as [ x | ].
      * rewrite iter_rt_it_one_1; auto.
      * rewrite iter_rt_it_one_0; auto.
    + simpl; destruct n as [ | n ]; try lia.
      rewrite !iter_rt_it_lft_1; auto.
    + simpl.
      destruct x as [ x | ].
      * destruct (list_decomp_1 ll) with (1 := Hn)
          as [ [ (r & y & m & -> & H2) | H1 ] | H1 ].
        - rewrite !iter_rt_it_rt_1 with (1 := H2); auto.
        - rewrite !iter_rt_it_rt_2; auto.
        - rewrite !iter_rt_it_rt_3; auto.
      * destruct (repeat_option_choose ll) as [ (n1 & y & m & ->) | H1 ].
        - destruct n as [ | n ]; try lia.
          destruct (lt_eq_lt_dec n n1) as [ [ H1 | <- ] | H1 ].
          ++ replace n1 with (n + (S (n1 - S n))) by lia.
             rewrite repeat_plus; simpl repeat. 
             rewrite app_ass; simpl app.
             rewrite iter_rt_it_rt_1; [ | rewrite repeat_length; auto ].
             rewrite iter_rt_it_rt_0; auto.
          ++ rewrite iter_rt_it_rt_1; [ | rewrite repeat_length; auto ].
             rewrite iter_rt_it_rt_0; auto.
          ++ replace (S n) with (S n1 + (S (n-S n1))) by lia.
             rewrite <- !iter_plus.
             rewrite iter_rt_it_rt_1; [ | rewrite repeat_length; auto ].
             rewrite iter_rt_it_rt_0; auto.
             generalize (n - S n1); clear n Hn H1; intros n.
             destruct (list_decomp_1 m) with (n := S n)
               as [ [ (r & z & m' & -> & H2) | H1 ] | H1 ]; try lia.
             ** rewrite iter_rt_it_both_0; auto.
                rewrite iter_rt_it_rt_1; auto.
             ** rewrite iter_rt_it_both_1; auto.
                rewrite iter_rt_it_rt_2; auto.
             ** rewrite iter_rt_it_both_2; auto.
                rewrite iter_rt_it_rt_3; auto.
        - rewrite H1; generalize (length ll); clear ll H1.
          intros n1.
          destruct n as [ | n ]; try lia.
          destruct (lt_eq_lt_dec n n1) as [ [ H1 | <- ] | H1 ].
          ++ replace n1 with (n + (S (n1 - S n))) by lia.
             rewrite repeat_plus; simpl repeat. 
             rewrite iter_rt_it_rt_1; [ | rewrite repeat_length; auto ].
             rewrite iter_rt_it_rt_0; auto.
          ++ rewrite iter_rt_it_rt_2; [ | rewrite repeat_length; auto ].
             rewrite iter_rt_it_rt_0'; auto.
          ++ replace (S n) with (S n1 + (S (n-S n1))) by lia.
             rewrite <- !iter_plus.
             rewrite iter_rt_it_rt_2; [ | rewrite repeat_length; auto ].
             rewrite iter_rt_it_rt_0'; auto.
             rewrite iter_rt_it_lft_1.
             rewrite iter_rt_it_one_1; auto.
    + simpl.
      destruct (list_decomp_1 rr) with (1 := Hn)
          as [ [ (r & y & m & -> & H2) | H1 ] | H1 ].
      - rewrite !iter_rt_it_both_0 with (1 := H2); auto.
      - rewrite !iter_rt_it_both_1; auto.
      - rewrite !iter_rt_it_both_2; auto.
  Qed.

  Fact rd_lft_inj a1 a2 l1 l2 x1 x2 :
        (forall n, rd (mv_lft↑n (it_lft a1 l1 x1)) = rd (mv_lft↑n (it_lft a2 l2 x2)))
     -> l1 = l2.
  Proof.
    intros H1.
    destruct (lt_eq_lt_dec (length l1) (length l2)) as [ [ H2 | H2 ] | H2 ].
    1: { generalize (H1 (S (length l2))).
         rewrite rd_lft_lft, rd_lft_out; try lia; easy. }
    2: { generalize (H1 (S (length l1))).
         rewrite rd_lft_lft, rd_lft_out; try lia; easy. }
    revert x1 x2 H1; pattern l1, l2.
    revert H2; apply length_eq_ind; auto.
    intros x y l m IH x1 x2 H; f_equal.
    + generalize (H 1); clear H.
      revert x1 x x2 y; intros [] [] [] []; simpl; auto.
    + apply (IH x y); intros n.
      generalize (H (S n)).
      rewrite !rd_lft_nxt; auto.
  Qed.

  Fact rd_rt_inj b1 b2 r1 r2 x1 x2 :
        (forall n, rd (mv_rt↑n (it_rt x1 r1 b1)) = rd (mv_rt↑n (it_rt x2 r2 b2)))
     -> r1 = r2.
  Proof.
    intros H1.
    destruct (lt_eq_lt_dec (length r1) (length r2)) as [ [ H2 | H2 ] | H2 ].
    1: { generalize (H1 (S (length r2))).
         rewrite rd_rt_rt, rd_rt_out; try lia; easy. }
    2: { generalize (H1 (S (length r1))).
         rewrite rd_rt_rt, rd_rt_out; try lia; easy. }
    revert x1 x2 H1; pattern r1, r2.
    revert H2; apply length_eq_ind; auto.
    intros x y l m IH x1 x2 H; f_equal.
    + generalize (H 1); clear H.
      revert x1 x x2 y; intros [] [] [] []; simpl; auto.
    + apply (IH x y); intros n.
      generalize (H (S n)).
      rewrite !rd_rt_nxt; auto.
  Qed.

  Fact rd_both_inj a1 a2 l1 l2 x1 x2 r1 r2 b1 b2 :
        (forall n, rd (mv_lft↑n (it_both a1 l1 x1 r1 b1)) = rd (mv_lft↑n (it_both a2 l2 x2 r2 b2)))
     -> (forall n, rd (mv_rt↑n (it_both a1 l1 x1 r1 b1)) = rd (mv_rt↑n (it_both a2 l2 x2 r2 b2)))
     -> l1 = l2 /\ r1 = r2.
  Proof.
    intros H1 H2; split.
    + apply rd_lft_inj with a1 a2 x1 x2.
      intros n; generalize (H1 n).
      now rewrite !rd_lft_eq_both_lft.
    + apply rd_rt_inj with b1 b2 x1 x2.
      intros n; generalize (H2 n).
      now rewrite !rd_rt_eq_both_rt.
  Qed.

  Theorem rd_uniq s t :
        (forall n, rd (iter mv_lft n s) = rd (iter mv_lft n t))
     -> (forall n, rd (iter mv_rt n s) = rd (iter mv_rt n t))
     -> s = t.
  Proof.
    intros H1 H2.
    destruct s; destruct t.

    + f_equal; apply (H1 0).
    + generalize (H1 (S (length l))).
      now rewrite rd_lft_lft, rd_lft_one.
    + generalize (H2 (S (length l))).
      now rewrite rd_rt_rt, rd_rt_one.
    + generalize (H1 (S (length l))).
      now rewrite rd_lft_both, rd_lft_one.

    + generalize (H1 (S (length l))).
      now rewrite rd_lft_lft, rd_lft_one.
    + assert (l = l0) as H3; [ | subst l0 ].
      { apply rd_lft_inj with (1 := H1). }
      f_equal; auto.
      * generalize (H1 (S (length l))).
        rewrite !rd_lft_lft; inversion 1; auto.
      * apply (H1 0).
    + generalize (H1 (S (length l))).
      now rewrite rd_lft_lft, rd_lft_rt.
    + generalize (H2 (S (length l1))).
      now rewrite rd_rt_lft, rd_rt_both.

    + generalize (H2 (S (length l))).
      now rewrite rd_rt_rt, rd_rt_one.
    + generalize (H2 (S (length l))).
      now rewrite rd_rt_rt, rd_rt_lft.
    + assert (l = l0) as H3; [ | subst l0 ].
      { apply rd_rt_inj with (1 := H2). }
      f_equal; auto.
      * apply (H1 0).
      * generalize (H2 (S (length l))).
        rewrite !rd_rt_rt; inversion 1; auto.
    + generalize (H1 (S (length l0))).
      now rewrite rd_lft_rt, rd_lft_both.

    + generalize (H2 (S (length l0))).
      now rewrite rd_rt_both, rd_rt_one.
    + generalize (H2 (S (length l0))).
      now rewrite rd_rt_both, rd_rt_lft.
    + generalize (H1 (S (length l))).
      now rewrite rd_lft_both, rd_lft_rt.
    + assert (l = l1 /\ l0 = l2) as E.
      { apply rd_both_inj with (1 := H1); auto. }
      destruct E as (-> & ->).
      f_equal.
      * generalize (H1 (S (length l1))).
        rewrite !rd_lft_both; inversion 1; auto.
      * apply (H1 0).
      * generalize (H2 (S (length l2))).
        rewrite !rd_rt_both; inversion 1; auto.
  Qed.
 
  Fixpoint qt_it (t : q_tape Σ) :=
    match t with
      | qt_emp    => it_one None
      | qt_lft t  => mv_lft (qt_it t)
      | qt_rt  t  => mv_rt (qt_it t)
      | qt_wr t x => wr (qt_it t) x
    end.

  Definition it_qt_full (t : i_tape) : { s | qt_it s = t }.
  Proof.
    induction t as [ | x t (s & Hs) | t (s & Hs) | t (s & Hs) ].
    + exists qt_emp; auto.
    + exists (qt_wr s x); subst; auto.
    + exists (qt_lft s); subst; auto.
    + exists (qt_rt s); subst; auto.
  Qed.

  Definition it_qt t := proj1_sig (it_qt_full t).
  
  Fact it_qt_spec t : qt_it (it_qt t) = t.
  Proof. apply (proj2_sig (it_qt_full t)). Qed.

  Fact qt_it_rd t n : rd (mv_lft↑n (qt_it t)) = qt_rdZ t (-Z.of_nat n)
                   /\ rd (mv_rt↑n (qt_it t)) = qt_rdZ t (Z.of_nat n).
  Proof.
    revert n.
    induction t as [ | t IHt | t IHt | t IHt x ]; intros n.
    + rewrite iter_lft_it_one_0; split; auto.
      rewrite iter_rt_it_one_0; split; auto.
    + generalize (proj1 (IHt (S n))); simpl; intros ->; split.
      * f_equal; lia.
      * destruct n as [ | n ]; simpl iter.
        - apply (IHt 1).
        - rewrite mv_rt_lft. 
          generalize (proj2 (IHt n)); intros ->; f_equal; lia.
    + split.
      * destruct n as [ | n ]; simpl iter.
        - apply (IHt 1).
        - rewrite mv_lft_rt.
          generalize (proj1 (IHt n)); intros ->. 
          Opaque Z.of_nat.
          cbn; f_equal; lia.
      * generalize (proj2 (IHt (S n))); simpl; intros ->; f_equal; lia.
    + destruct n as [ | n ].
      * simpl iter; simpl qt_it; rewrite rd_wr.
        Transparent Z.of_nat. 
        simpl; auto.
      * simpl qt_it.
        rewrite rd_lwr; try lia.
        rewrite rd_rwr; try lia.
        apply IHt.
  Qed.

  Fact qt_it_eq s t : qt_it s = qt_it t -> s ~qt t.
  Proof.
    intros H i.
    destruct (Z.le_ge_cases i 0) as [ H1 | H1 ].
    + destruct (Z_of_nat_complete (-i)) as (n & Hn); try lia.
      replace i with (- Z.of_nat n) by lia.
      rewrite <- !(proj1 (qt_it_rd _ _)), H; auto.
    + destruct (Z_of_nat_complete i) as (n & ->); auto.
      rewrite <- !(proj2 (qt_it_rd _ _)), H; auto.
  Qed.

  Fact qt_it_spec t : t ~qt it_qt (qt_it t).
  Proof. apply qt_it_eq; now rewrite it_qt_spec. Qed.

  Check it_qt_spec.
  Check qt_it_spec.

  (* This gives us the quotient, it is an infinite and non-discrete quotient *)

  Theorem quotient s t : s ~qt t <-> qt_it s = qt_it t.
  Proof.
    split.
    2: apply qt_it_eq.
    intros H1.
    apply rd_uniq; intros n.
    + rewrite !(proj1 (qt_it_rd _ _)); auto.
    + rewrite !(proj2 (qt_it_rd _ _)); auto.
  Qed.

End tapes.

Check quotient.
Print Assumptions quotient.

  (* We should be able to compute the normal form of any iter lft ... *)

  

  (* a (l++(Some x)::repeat None 

  Fact iter_lft_it_lft a l m x n : S (length m) = n -> iter mv_lft n (it_lft a (l++m) x

    destruct t as [ [] | ? [ | [] ] [] | [] [ | [] ] ? | ? [] [] [] ? ].

      tp0_rd_lwr : forall t n a, (0 < n)%nat -> tp0_rd0 (iter tp0_lft n (tp0_wr0 t a)) 
                                            = tp0_rd0 (iter tp0_lft n t);
    tp0_rd_rwr : forall t n a, (0 < n)%nat -> tp0_rd0 (iter tp0_rt  n (tp0_wr0 t a)) 
                                            = tp0_rd0 (iter tp0_rt  n t); *)
  

  (* I think one can also show that equivalent tapes are identical with that definition *)

End tapes.