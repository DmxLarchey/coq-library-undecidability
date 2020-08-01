Require Import ZArith Lia List.

Set Implicit Arguments.

Section iter.

  Variable (X : Type) (f : X -> X).

  Fixpoint iter n x :=
    match n with
      | 0   => x
      | S n => iter n (f x)
    end.

  Fact iter_plus n m x : iter n (iter m x) = iter (m+n) x.
  Proof. revert x; induction m; simpl; auto. Qed.

  Fact iter_S n x : iter (S n) x = f (iter n x).
  Proof.
    replace (S n) with (n+1) by lia.
    rewrite <- iter_plus; auto.
  Qed.

End iter.

Open Scope Z_scope.

Print Z.

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

  Inductive itape : Type :=
    | it_one  : option Σ -> itape
    | it_lft  : Σ -> list (option Σ) -> option Σ -> itape
    | it_rt   : option Σ -> list (option Σ) -> Σ -> itape
    | it_both : Σ -> list (option Σ) -> option Σ -> list (option Σ) -> Σ -> itape.

  Set Elimination Schemes.

  (* Moving left *)

  Definition mv_lft (t : itape) :=
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

  Definition mv_rt (t : itape) :=
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

  Definition rd (t : itape) :=
    match t with
      | it_one x          => x
      | it_lft _ _ x      => x
      | it_rt x _ _       => x
      | it_both _ _ x _ _ => x
    end.

  Definition wr (t : itape) c :=
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

  Section itape_ind.

    Variable (P : itape -> Prop)
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

    Theorem itape_ind t : P t.
    Proof. destruct t; auto. Qed.

  End itape_ind.

  Check itape_ind.

  Fact rd_wr t c : rd (wr t c) = Some c.
  Proof. now destruct t as [ [] | ? [ | [] ] [] | [] [ | [] ] ? | ? [] [] [] ? ]. Qed.

  Fixpoint repeat {X} (x : X) n :=
    match n with 
      | 0 => nil
      | S n => x::repeat x n
    end.

  Fact repeat_plus {X} (x : X) n m : repeat x (n+m) = repeat x n ++ repeat x m.
  Proof. induction n; simpl; f_equal; auto. Qed.

  Fact repeat_S {X} (x : X) n : repeat x (S n) = repeat x n ++ x :: nil.
  Proof. replace (S n) with (n+1) by lia; now rewrite repeat_plus. Qed. 

  Fact iter_lft_it_rt_0 r b n : iter mv_lft n (it_rt None r b) = it_rt None (repeat None n++r) b.
  Proof.
    revert r; induction n as [ | n IHn ]; simpl; auto; intros r.
    rewrite IHn; f_equal.
    change (None::repeat None n++r) with (repeat None (S n)++r).
    rewrite repeat_S, app_ass; auto.
  Qed.

  Fact iter_lft_it_rt_1 x r b n : iter mv_lft (S n) (it_rt x r b) = it_rt None (repeat None n++x::r) b.
  Proof.
    simpl iter at 1.
    now rewrite iter_lft_it_rt_0.
  Qed.

  Fact iter_lft_one_0 n : iter mv_lft n (it_one None) = it_one None.
  Proof. induction n; simpl; f_equal; auto. Qed.

  Fact iter_lft_it_one_1 b n : iter mv_lft (S n) (it_one (Some b)) = it_rt None (repeat None n) b.
  Proof.
    simpl iter at 1.
    now rewrite iter_lft_it_rt_0, <- app_nil_end.
  Qed.

  Fact iter_lft_it_both_0 a l y m x r b n : 
          S (length l) = n 
       -> iter mv_lft n (it_both a (l++y::m) x r b)
        = it_both a m y (rev l++x::r) b.
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

  Fact iter_lft_it_both_1 a l x r b n :
         S (length l) = n
       -> iter mv_lft n (it_both a l x r b)
        = it_rt (Some a) (rev l++x::r) b.
  Proof.
  Admitted.

  Fact iter_lft_it_both_2 a l x r b n :
          2+length l <= n
       -> iter mv_lft n (it_both a l x r b)
        = it_rt None (repeat None (n - 2 - length l)++Some a::rev l++x::r) b.
  Proof.
  Admitted.

  Fact iter_lft_it_lft a l x m b n : 
          S (length l) = n 
       -> iter mv_lft n (it_lft a (l++x::m) (Some b))
        = it_both a m x (rev l) b.
  Proof.
    intros <-.
    simpl iter.
    destruct l as [ | y l ]; simpl.
    + destruct x; auto.
    + replace (match y with |Some _ | _ => it_both a (l ++ x :: m) y nil b end)
      with (it_both a (l ++ x :: m) y nil b) by (destruct y; auto).
      rewrite <- iter_lft_it_both_0 with (r := nil) (1 := eq_refl); auto.
  Qed.

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