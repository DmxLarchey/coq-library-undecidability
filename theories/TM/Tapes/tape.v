Require Import ZArith Lia List.

Set Implicit Arguments.

Section list_utils.

  Variable (X : Type).

  Implicit Types (l ll : list X).

  Fact list_snoc l : { x & { m | l = m++x::nil } } + { l = nil }.
  Proof.
    rewrite <- (rev_involutive l).
    destruct (rev l) as [ | x m ].
    + right; auto.
    + left; exists x, (rev m); auto.
  Qed.

  Fact list_decomp_0 ll n :
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

  Fact list_decomp_1 ll n : 0 < n ->
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

  Variables (P : list X -> list X -> Prop)
            (H0 : P nil nil) (H1 : forall x y l m, P l m -> P (x::l) (y::m)).

  Theorem length_eq_ind l m : length l = length m -> P l m.
  Proof.
    revert m; induction l as [ | x l IHl ]; intros [ | y m ]; try discriminate; auto.
  Qed.

End list_utils.

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

  Fact iter_plus n m x : iter (m+n) x = iter n (iter m x).
  Proof. revert x; induction m; simpl; auto. Qed.

  Fact iter_S n x : iter (S n) x = f (iter n x).
  Proof.
    replace (S n) with (n+1) by lia.
    rewrite iter_plus; auto.
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

Reserved Notation "x '~i' y" (at level 70, no associativity).

Section quotient_tapes.

  Variable (X : Type).

  Inductive q_tape :=    (* for quotient tape *)
    | qt_emp : q_tape
    | qt_lft : q_tape -> q_tape
    | qt_rt  : q_tape -> q_tape
    | qt_wr  : q_tape -> X -> q_tape.

  Notation E := qt_emp.
  Notation L := qt_lft.
  Notation R := qt_rt.
  Notation W := qt_wr.

  (* Syntactic equivalance *) 

  Inductive qt_syn_eq : q_tape -> q_tape -> Prop :=
    | in_qt_seq_0 : E ~i E
    | in_qt_seq_1 s t : s ~i t -> L s ~i L t
    | in_qt_seq_2 s t : s ~i t -> R s ~i R t
    | in_qt_seq_3 x s t : s ~i t -> W s x ~i W t x
    | in_qt_seq_4 s t : s ~i t -> t ~i s
    | in_qt_seq_5 r s t : r ~i s -> s ~i t -> r ~i t
    | in_qt_seq_6 t : L (R t) ~i t
    | in_qt_seq_7 t : R (L t) ~i t
    | in_qt_seq_8 x y t : W (W t y) x ~i W t x
    | in_qt_seq_9 n x y t : W (L↑(S n) (W (R↑(S n) t) x)) y
                         ~i L↑(S n) (W (R↑(S n) (W t y)) x)
    | in_qt_seq_a n x y t : W (R↑(S n) (W (L↑(S n) t) x)) y
                         ~i R↑(S n) (W (L↑(S n) (W t y)) x)
    | in_qt_seq_b : L E ~i E
    | in_qt_seq_c : R E ~i E
  where "x ~i y" := (qt_syn_eq x y).

  Fact qt_seq_refl t : t ~i t.
  Proof. induction t; constructor; auto. Qed.

  Definition qt_seq_sym := in_qt_seq_4.
  Definition qt_seq_trans := in_qt_seq_5.

  (* negative are on the lft of the head *)

  Fixpoint qt_rdZ t i :=
    match t with
      | E     => None
      | L t   => qt_rdZ t (i-1)%Z
      | R t   => qt_rdZ t (i+1)%Z
      | W t x => match i with 
                       | Z0 => Some x
                       | _  => qt_rdZ t i
                     end
    end.

  Fact qt_rdZ_wr_not0 t x i : i <> 0%Z -> qt_rdZ (W t x) i = qt_rdZ t i.
  Proof. destruct i; simpl; auto; intros []; auto. Qed.

  Fact qt_rqZ_Ln n t i : qt_rdZ (L↑n t) i = qt_rdZ t (i - Z.of_nat n)%Z.
  Proof.
    revert t; induction n as [ | n IHn ]; intros t; simpl.
    + f_equal; lia.
    + rewrite IHn; simpl; f_equal; lia.
  Qed.

  Fact qt_rqZ_Rn n t i : qt_rdZ (R↑n t) i = qt_rdZ t (i + Z.of_nat n)%Z.
  Proof.
    revert t; induction n as [ | n IHn ]; intros t; simpl.
    + f_equal; lia.
    + rewrite IHn; simpl; f_equal; lia.
  Qed.

  Definition qt_sem_eq s t := forall i, qt_rdZ s i = qt_rdZ t i.

  Infix "~qt" := qt_sem_eq (at level 70).

  Fact qt_sem_eq_refl t : t ~qt t.
  Proof. red; auto. Qed.

  Fact qt_sem_eq_sym s t : s ~qt t -> t ~qt s.
  Proof. red; auto. Qed.

  Fact qt_sem_eq_trans r s t : r ~qt s -> s ~qt t -> r ~qt t.
  Proof. unfold qt_sem_eq; intros H1 H2 ?; rewrite H1; auto. Qed.

  Theorem qt_syn_sem_eq s t : s ~i t -> s ~qt t.
  Proof.
    induction 1 as 
      [ | | | | | r s t H1 IH1 H2 IH2 | | | | n x y t | n x y t | | ]; try firstorder.
    + intros []; simpl; auto.
    + red in IH1; intro; rewrite IH1; auto.
    + intro; simpl; f_equal; lia.
    + intro; simpl; f_equal; lia.
    + intros []; simpl; auto.
    + intros []; rewrite qt_rqZ_Ln.
      * rewrite qt_rdZ_wr_not0 with (i := (0 - _)%Z); try lia.
        rewrite qt_rqZ_Rn.
        replace (0-Z.of_nat (S n)+Z.of_nat (S n))%Z with 0%Z by lia.
        simpl; auto.
      * destruct (Z.eq_dec (Z.pos p) (Z.of_nat (S n))) as [ H | H ].
        - replace (Z.pos p - Z.of_nat (S n))%Z with 0%Z by lia.
          rewrite qt_rdZ_wr_not0; try lia.
          rewrite qt_rqZ_Ln.
          simpl qt_rdZ at 2.
          replace (Z.pos p - Z.of_nat (S n))%Z with 0%Z by lia; auto.
        - repeat (rewrite qt_rdZ_wr_not0; try lia).
          rewrite qt_rqZ_Ln, qt_rqZ_Rn.
          repeat (rewrite qt_rdZ_wr_not0; try lia).
          rewrite qt_rqZ_Rn; auto.
      * repeat (rewrite qt_rdZ_wr_not0; try lia).
        rewrite qt_rqZ_Ln, qt_rqZ_Rn.
        repeat (rewrite qt_rdZ_wr_not0; try lia).
        rewrite qt_rqZ_Rn; auto.
    + intros []; rewrite qt_rqZ_Rn.
      * rewrite qt_rdZ_wr_not0 with (i := (0 + _)%Z); try lia.
        rewrite qt_rqZ_Ln.
        replace (0+Z.of_nat (S n)-Z.of_nat (S n))%Z with 0%Z by lia.
        simpl; auto.
      * repeat (rewrite qt_rdZ_wr_not0; try lia).
        rewrite qt_rqZ_Ln, qt_rqZ_Rn.
        repeat (rewrite qt_rdZ_wr_not0; try lia).
        rewrite qt_rqZ_Ln; auto.
      * destruct (Z.eq_dec (- Z.neg p)%Z (Z.of_nat (S n))) as [ H | H ].
        - replace (Z.neg p + Z.of_nat (S n))%Z with 0%Z by lia.
          rewrite qt_rdZ_wr_not0; try lia.
          rewrite qt_rqZ_Rn.
          simpl qt_rdZ at 2.
          replace (Z.neg p + Z.of_nat (S n))%Z with 0%Z by lia; auto.
        - repeat (rewrite qt_rdZ_wr_not0; try lia).
          rewrite qt_rqZ_Ln, qt_rqZ_Rn.
          repeat (rewrite qt_rdZ_wr_not0; try lia).
          rewrite qt_rqZ_Ln; auto.
  Qed.

  Fact E_eq t : E ~qt t -> E ~i t.
  Proof.
    induction t as [ | t IHt | t IHt | t y ].
    + constructor.
    + intros H.
      apply qt_seq_trans with (L E).
      - apply qt_seq_sym, in_qt_seq_b.
      - apply in_qt_seq_1, IHt.
        intros i.
        specialize (H (i+1)%Z).
        simpl in H |- *.
        rewrite  H; f_equal; lia.
    + intros H.
      apply qt_seq_trans with (R E).
      - apply qt_seq_sym, in_qt_seq_c.
      - apply in_qt_seq_2, IHt.
        intros i.
        specialize (H (i-1)%Z).
        simpl in H |- *.
        rewrite  H; f_equal; lia.
    + intros H; specialize (H 0%Z); now simpl in H.
  Qed.

  Theorem qt_sem_syn_eq s t : s ~qt t -> s ~i t.
  Proof.
    revert t; induction s as [ | s IHs | s IHs | s IHs x ]; intros t.
    + apply E_eq.
    + intros H1. 
      assert (s ~i R t) as H2.
      { apply IHs.
        intros i; simpl.
        rewrite <- H1; simpl; f_equal; lia. }
      apply in_qt_seq_1 in H2.
      apply qt_seq_trans with (1 := H2).
      apply in_qt_seq_6.
    + intros H1. 
      assert (s ~i L t) as H2.
      { apply IHs.
        intros i; simpl.
        rewrite <- H1; simpl; f_equal; lia. }
      apply in_qt_seq_2 in H2.
      apply qt_seq_trans with (1 := H2).
      apply in_qt_seq_7.
    + intros H1.
      
      admit.
  Admitted.

  (* Showing the converse if more difficult ? *)

End quotient_tapes.


Infix "~it" := (@qt_syn_eq _) (at level 70).
Infix "~qt" := (@qt_sem_eq _) (at level 70).
Arguments qt_emp {X}.

Notation "⌊ l ⌋" := (length l) (at level 1, format "⌊ l ⌋").

Section infinite_tapes.

  (* Tapes with empty/blank cells: 
       - a,b,c for regular symbols in Σ
       - ?,x for either blank or regular symbol in (option Σ)
       - _ for blank in option Σ 

     ⟨x⟩ represents 
       a) either empty 
             _ _ ⟨_⟩ _ _    as  ⟨None⟩
       b) or exactly one non blank under the head
             _ _ ⟨a⟩ _ _    as ⟨Some a⟩

     ⟦a⊢l⟨x⟩ represents tapes which are entirely left of the head
          _ _ a ...l... ⟨x⟩ _ _

     ⟨x⟩r⊣b⟧ represents tapes which are entirely right of the head
          _ _ ⟨x⟩ ...r... b _ _

     ⟦a⊢l⟨x⟩r⊣b⟧ represents tapes which are both left and right of the head
          _ a ...l... ⟨x⟩ ...r... b _   as (it_both a l x r b)

   *)

  Variable Σ : Type.

  Unset Elimination Schemes.

  Inductive i_tape : Type :=   (* for infinite tape *)
    | it_one   : option Σ -> i_tape
    | it_left  : Σ -> list (option Σ) -> option Σ -> i_tape
    | it_right : option Σ -> list (option Σ) -> Σ -> i_tape
    | it_both  : Σ -> list (option Σ) -> option Σ -> list (option Σ) -> Σ -> i_tape.

  Set Elimination Schemes.

  (* Notation ⟦ .. ⊢ .. ⟨..⟩ .. ⊣ .. ⟧, where ⟨..⟩ symbolise the position of the head *)

  Notation "⟨ x ⟩" := (it_one x) (at level 65, format "⟨ x ⟩").
  Notation "'⟦' a '⊢' l '⟨' x '⟩'" := (it_left a l x) (at level 65, format "⟦ a ⊢ l ⟨ x ⟩").
  Notation "'⟨' x '⟩' r '⊣' b '⟧'" := (it_right x r b) (at level 65, format "⟨ x ⟩ r ⊣ b ⟧").
  Notation "'⟦' a '⊢' l '⟨' x '⟩' r '⊣' b '⟧'" := (it_both a l x r b) (at level 65, format "⟦ a ⊢ l ⟨ x ⟩ r ⊣ b ⟧").

  (* in ⟦a⊢l⟨x⟩ and ⟨x⟩r⊣b⟧ and ⟦a⊢l⟨x⟩r⊣b⟧, the list l and r have special parse only notations:
      1)  m ⋉ l ⊳ x  is x::l++m (ie read from right to left)
      2)  x ⊲ r ⋊ m  is x::r++m (ie read from left to right) *)

  Notation "x ⊲ l" := (x::l) (at level 60, right associativity, only parsing).
  Notation "l ⋊ m" := (l++m) (at level 60, right associativity, only parsing).

  Notation "l ⊳ x" := (x::l) (at level 61, left associativity, only parsing).
  Notation "l ⋉ m" := (m++l) (at level 61, left associativity, only parsing).

  (* Moving the head one step left *)
  Definition it_lft (t : i_tape) :=
    match t with
      | ⟨None⟩            => ⟨None⟩          (*  _ _ [_] _ _ ~~> _ [_] _ _ _ *)
      | ⟨Some b⟩          => ⟨None⟩nil⊣b⟧    (*  _ _ [b] _ _ ~~> _ [_] b _ _ *)

      | ⟦a⊢nil⟨None⟩      => ⟨Some a⟩        (*  _ a [_] _ _ ~~> _ [a] _ _ _ *)
      | ⟦a⊢l⊳x⟨None⟩      => ⟦a⊢l⟨x⟩         (*  a x [_] _ _ ~~> a [x] _ _ _ *)
      | ⟦a⊢nil⟨Some b⟩    => ⟨Some a⟩nil⊣b⟧  (*  _ a [b] _ _ ~~> _ [a] b _ _ *)
      | ⟦a⊢l⊳x⟨Some b⟩    => ⟦a⊢l⟨x⟩nil⊣b⟧   (*  a x [b] _ _ ~~> a [x] b _ _ *)

      | ⟨x⟩r⊣b⟧           => ⟨None⟩x⊲r⊣b⟧    (*  _ _ [x] ? b ~~> _ [_] x ? b *)

      | ⟦a⊢nil⟨x⟩r⊣b⟧     => ⟨Some a⟩x⊲r⊣b⟧  (*  _ a [x] ? b ~~> _ [a] x ? b *)
      | ⟦a⊢l⊳x⟨y⟩r⊣b⟧     => ⟦a⊢l⟨x⟩y⊲r⊣b⟧   (*  a x [y] ? b ~~> a [x] y ? b *)
    end.

  (* Moving the head one step right *)
  Definition it_rt (t : i_tape) :=
    match t with
      | ⟨None⟩            => ⟨None⟩          (*  _ _ [_] _ _ ~~> _ _ _ [_] _ *)
      | ⟨Some a⟩          => ⟦a⊢nil⟨None⟩    (*  _ _ [a] _ _ ~~> _ _ a [_] _ *)

      | ⟦a⊢l⟨x⟩           => ⟦a⊢l⊳x⟨None⟩    (*  a ? [x] _ _ ~~> a ? x [_] _ *)

      | ⟨None⟩nil⊣b⟧      => ⟨Some b⟩        (*  _ _ [_] b _ ~~> _ _ _ [b] _ *)
      | ⟨None⟩x⊲l⊣b⟧      => ⟨x⟩l⊣b⟧         (*  _ _ [_] x b ~~> _ _ _ [x] b *)
      | ⟨Some a⟩nil⊣b⟧    => ⟦a⊢nil⟨Some b⟩  (*  _ _ [a] b _ ~~> _ _ a [b] _ *)
      | ⟨Some a⟩x⊲r⊣b⟧    => ⟦a⊢nil⟨x⟩r⊣b⟧   (*  _ _ [a] x b ~~> _ _ a [x] b *)

      | ⟦a⊢l⟨x⟩nil⊣b⟧     => ⟦a⊢l⊳x⟨Some b⟩  (*  a ? [x] b _ ~~> a ? x [b] _ *)
      | ⟦a⊢l⟨x⟩y⊲r⊣b⟧     => ⟦a⊢l⊳x⟨y⟩r⊣b⟧   (*  a ? [x] y b ~~> a ? x [y] b *)
    end.

  Definition it_nil := ⟨None⟩.

  (* Reading under the head *)

  Definition it_rd (t : i_tape) :=
    match t with
      |     ⟨x⟩     => x
      | ⟦_⊢_⟨x⟩     => x
      |     ⟨x⟩_⊣_⟧ => x
      | ⟦_⊢_⟨x⟩_⊣_⟧ => x
    end.

  (* Writing under the head *)

  Definition it_wr (t : i_tape) c :=
    match t with
      |     ⟨_⟩     => ⟨Some c⟩
      | ⟦a⊢l⟨_⟩     => ⟦a⊢l⟨Some c⟩
      |     ⟨_⟩r⊣b⟧ => ⟨Some c⟩r⊣b⟧
      | ⟦a⊢l⟨_⟩r⊣b⟧ => ⟦a⊢l⟨Some c⟩r⊣b⟧
    end.

  Notation L := it_lft.
  Notation R := it_rt.
  Notation WR := it_wr.
  Notation RD := it_rd.

  (* Left/right moves are strict inverse to each other *)

  Fact it_lft_rt t : L (R t) = t.
  Proof. now destruct t as [ [] | ? [ | [] ] [] | [] [ | [] ] ? | ? [] [] [] ? ]. Qed.

  Fact it_rt_lft t : R (L t) = t.
  Proof. now destruct t as [ [] | ? [ | [] ] [] | [] [ | [] ] ? | ? [] [] [] ? ]. Qed.

  Fact it_rd_wr t c : RD (WR t c) = Some c.
  Proof. now destruct t as [ [] | ? [ | [] ] [] | [] [ | [] ] ? | ? [] [] [] ? ]. Qed.

  Section i_tape_rect.

    (* i_tapes are finitely generated by it_nil it_lft it_rt and it_wr *)

    Variable (P : i_tape -> Type)
             (HP_nil  : P it_nil)
             (HP_wr : forall c t, P t -> P (WR t c))
             (HP_lft : forall t, P t -> P (L t))
             (HP_rt : forall t, P t -> P (R t)).

    Let P_one x : P (it_one x).
    Proof.
      destruct x as [c|]; auto.
      apply HP_wr with (1 := HP_nil).
    Qed.

    Let P_left a l x : P (it_left a l x).
    Proof.
      revert x; induction l as [ | y l IHl ]; intros [c|].
      + apply HP_wr with (t := it_left a nil None).
        apply HP_rt with (1 := P_one (Some a)).
      + apply HP_rt with (1 := P_one (Some a)).
      + apply HP_wr with (t := it_left a (y::l) None).
        apply HP_rt with (t := it_left a l y); auto.
      + apply HP_rt with (t := it_left a l y); auto.
    Qed.

    Let P_right x r b : P (it_right x r b).
    Proof.
      revert x; induction r as [ | y r IHr ]; intros [c|].
      + apply HP_wr with (t := it_right None nil b).
        apply HP_lft with (1 := P_one (Some b)).
      + apply HP_lft with (1 := P_one (Some b)).
      + apply HP_wr with (t := it_right None (y::r) b).
        apply HP_lft with (t := it_right y r b); auto.
      + apply HP_lft with (t := it_right y r b); auto.
    Qed.

    Let P_both a l x r b : P (it_both a l x r b).
    Proof.
      revert a x r; induction l as [ | y l IHl ]; intros a x r.
      + apply HP_rt with (t := it_right (Some a) (x::r) b); auto.
      + apply HP_rt with (t := it_both a l y (x::r) b); auto.
    Qed.

    Theorem i_tape_rect t : P t.
    Proof. destruct t; auto. Qed.

  End i_tape_rect.

  (** Elementary identities for successive left moves of the head *)

  Fact it_n_lft_right_0 r b n : L↑n (⟨None⟩r⊣b⟧) = ⟨None⟩None↟n⋊r⊣b⟧.
  Proof.
    revert r; induction n as [ | n IHn ]; simpl; auto; intros r.
    rewrite IHn; f_equal.
    change (None ⊲ None↟n ⋊ r) with (None↟(S n) ⋊ r).
    rewrite repeat_S, app_ass; auto.
  Qed.

  Fact it_Sn_lft_right_1 x r b n : L↑(S n) (⟨x⟩r⊣b⟧) = ⟨None⟩None↟n⋊x⊲r⊣b⟧.
  Proof. simpl iter at 1; now rewrite it_n_lft_right_0. Qed.

  Fact it_n_lft_one_0 n : L↑n (⟨None⟩) = ⟨None⟩.
  Proof. induction n; simpl; f_equal; auto. Qed.

  Fact it_Sn_lft_one_1 b n : L↑(S n) (⟨Some b⟩) = ⟨None⟩None↟n⊣b⟧.
  Proof. simpl iter at 1; now rewrite it_n_lft_right_0, <- app_nil_end. Qed.

  Fact it_Sl_lft_both_0 a l y m x r b : L↑(S ⌊l⌋) (⟦a⊢m⊳y⋉l⟨x⟩r⊣b⟧) = ⟦a⊢m⟨y⟩rev l⋊x⊲r⊣b⟧.
  Proof.
    revert y m x r; induction l as [ | z l IHl ]; intros y m x r; auto.
    simpl length; rewrite iter_succ; simpl it_lft.
    rewrite IHl; f_equal.
    simpl rev; rewrite app_ass; auto.
  Qed.

  Fact it_Sl_lft_both_1 a l x r b : L↑(S ⌊l⌋) (⟦a⊢l⟨x⟩r⊣b⟧) = ⟨Some a⟩rev l⋊x⊲r⊣b⟧.
  Proof.
    destruct (list_snoc l) as [ (y & m & ->) | -> ]; auto.
    rewrite app_length; simpl length.
    replace (S (⌊m⌋ + 1)) with ((S ⌊m⌋) + 1) by lia.
    rewrite iter_plus, it_Sl_lft_both_0.
    simpl; f_equal; rewrite rev_app_distr, app_ass; auto.
  Qed.

  Fact it_n_lft_both_2 a l x r b n :
          2+⌊l⌋ <= n
       -> L↑n (⟦a⊢l⟨x⟩r⊣b⟧) = ⟨None⟩None↟(n-2-⌊l⌋)⋊Some a⊲rev l⋊x⊲r⊣b⟧.
  Proof.
    intro; replace n with (S ⌊l⌋+(1+(n-2-⌊l⌋))) by lia.
    rewrite iter_plus, it_Sl_lft_both_1, iter_plus; simpl.
    rewrite it_n_lft_right_0; do 3 f_equal; lia.
  Qed.

  Fact it_Sn_lft_left_0 a n : L↑(S n) (⟦a⊢None↟n⟨None⟩) = ⟨Some a⟩.
  Proof. induction n; [ simpl | rewrite iter_succ ]; auto. Qed.

  Fact it_Sn_lft_left_1 a x l n : L↑(S n) (⟦a⊢l⊳x⋉None↟n⟨None⟩) = ⟦a⊢l⟨x⟩.
  Proof. induction n; [ destruct x | rewrite iter_succ ]; auto. Qed.

  Fact it_Sl_lft_left_2 a l x r b : L↑(S ⌊r⌋) (⟦a⊢l⊳x⋉r⟨Some b⟩) = ⟦a⊢l⟨x⟩rev r⊣b⟧.
  Proof.
    simpl iter.
    destruct r as [ | y r ]; simpl.
    + destruct x; auto.
    + replace (match y with |Some _ | _ => ⟦a⊢r⋊x⊲l⟨y⟩nil⊣b⟧ end)
      with (⟦a⊢r⋊x⊲l⟨y⟩nil⊣b⟧) by (destruct y; auto).
      rewrite <- it_Sl_lft_both_0 with (r := nil); auto.
  Qed.

  Fact it_Sl_lft_left_3 a l b : L↑(S ⌊l⌋) (⟦a⊢l⟨Some b⟩) = ⟨Some a⟩rev l⊣b⟧.
  Proof.
    destruct (list_snoc l) as [ (y & m & ->) | -> ]; auto.
    rewrite app_length; simpl length.
    replace (S (⌊m⌋ + 1)) with ((S ⌊m⌋) + 1) by lia.
    rewrite iter_plus, it_Sl_lft_left_2.
    simpl; f_equal; rewrite rev_app_distr; auto.
  Qed.

  Fact it_n_lft_left_4 a l b n : 
          2+⌊l⌋ <= n 
       -> L↑n (⟦a⊢l⟨Some b⟩) = ⟨None⟩None↟(n-2-⌊l⌋)⋊Some a⊲rev l⊣b⟧.
  Proof.
    intro.
    replace n with ((S ⌊l⌋)+(S (n-2-⌊l⌋))) by lia.
    rewrite iter_plus, it_Sl_lft_left_3, iter_succ. 
    simpl it_lft; rewrite it_n_lft_right_0.
    do 3 f_equal; lia.
  Qed.

  (** Elementary identities for successive right moves of the head *)

  Fact it_n_rt_left_0 a l n : R↑n (⟦a⊢l⟨None⟩)= ⟦a⊢l⋉None↟n⟨None⟩.
  Proof.
    revert l; induction n as [ | n IHn ]; simpl; auto; intros l.
    rewrite IHn; f_equal.
    change (l ⋉ repeat None n ⊳ None) with (l ⋉ repeat None (S n)).
    rewrite repeat_S, app_ass; auto.
  Qed.

  Fact it_Sn_rt_left_1 a l x n : R↑(S n) (⟦a⊢l⟨x⟩) = ⟦a⊢l⊳x⋉None↟n⟨None⟩.
  Proof. simpl iter at 1; now rewrite it_n_rt_left_0. Qed.
 
  Fact it_n_rt_one_0 n : R↑n (⟨None⟩) = ⟨None⟩.
  Proof. induction n; simpl; f_equal; auto. Qed.

  Fact it_Sn_rt_one_1 a n : R↑(S n) (⟨Some a⟩) = ⟦a⊢None↟n⟨None⟩.
  Proof. simpl iter at 1; now rewrite it_n_rt_left_0, <- app_nil_end. Qed.

  Fact it_Sl_rt_both_0 a l x r y m b : R↑(S ⌊r⌋) (⟦a⊢l⟨x⟩r⋊y⊲m⊣b⟧) = ⟦a⊢l⊳x⋉rev r⟨y⟩m⊣b⟧.
  Proof.
    revert y m x l; induction r as [ | z r IHr ]; intros y m x l; auto.
    simpl length; rewrite iter_succ; simpl it_rt.
    rewrite IHr; f_equal.
    simpl rev; rewrite app_ass; auto.
  Qed.

  Fact it_Sl_rt_both_1 a l x r b : R↑(S ⌊r⌋) (⟦a⊢l⟨x⟩r⊣b⟧) = ⟦a⊢l⊳x⋉rev r⟨Some b⟩.
  Proof.
    destruct (list_snoc r) as [ (y & m & ->) | -> ]; auto.
    rewrite app_length; simpl length.
    replace (S (⌊m⌋ + 1)) with ((S ⌊m⌋) + 1) by lia.
    rewrite iter_plus, it_Sl_rt_both_0.
    simpl; f_equal; rewrite rev_app_distr, app_ass; auto.
  Qed.

  Fact it_n_rt_both_2 a l x r b n :
          2+⌊r⌋ <= n
       -> R↑n (⟦a⊢l⟨x⟩r⊣b⟧) = ⟦a⊢l⊳x⋉rev r⊳Some b⋉None↟(n-2-⌊r⌋)⟨None⟩.
  Proof.
    intro; replace n with (S ⌊r⌋+(1+(n-2-⌊r⌋))) by lia.
    rewrite iter_plus, it_Sl_rt_both_1, iter_plus; simpl.
    rewrite it_n_rt_left_0; do 3 f_equal; lia.
  Qed.

  Fact it_Sn_rt_right_0 b n : R↑(S n) (⟨None⟩None↟n⊣b⟧) = ⟨Some b⟩.
  Proof. induction n; [ simpl | rewrite iter_succ ]; auto. Qed.

  Fact it_Sn_rt_right_1 b x r n : R↑(S n) (⟨None⟩None↟n⋊x⊲r⊣b⟧) = ⟨x⟩r⊣b⟧.
  Proof. induction n; [ destruct x | rewrite iter_succ ]; auto. Qed.

  Fact it_Sl_rt_right_2 a l x r b : R↑(S ⌊l⌋) (⟨Some a⟩l⋊x⊲r⊣b⟧) = ⟦a⊢rev l⟨x⟩r⊣b⟧.
  Proof.
    rewrite iter_succ.
    destruct l as [ | y l ]; auto.
    simpl it_rt; simpl length.
    apply it_Sl_rt_both_0.
  Qed.

  Fact it_Sl_rt_right_3 a r b : R↑(S ⌊r⌋) (⟨Some a⟩r⊣b⟧) = ⟦a⊢rev r⟨Some b⟩.
  Proof.
    destruct (list_snoc r) as [ (y & m & ->) | -> ]; auto.
    rewrite app_length; simpl length.
    replace (S (⌊m⌋ + 1)) with ((S ⌊m⌋) + 1) by lia.
    rewrite iter_plus, it_Sl_rt_right_2.
    simpl; f_equal; rewrite rev_app_distr; auto.
  Qed.

  Fact it_n_rt_right_4 a r b n : 
         2+⌊r⌋ <= n 
       -> R↑n (⟨Some a⟩r⊣b⟧) = ⟦a⊢rev r⊳Some b⋉None↟(n-2-⌊r⌋)⟨None⟩.
  Proof.
    intro.
    replace n with ((S ⌊r⌋)+(S (n-2-⌊r⌋))) by lia.
    rewrite iter_plus, it_Sl_rt_right_3, iter_succ. 
    simpl it_rt; rewrite it_n_rt_left_0.
    do 3 f_equal; lia.
  Qed.

  (** Successive left moves then read *)

  Fact it_rd_Sn_lft_one n x : RD (L↑(S n) (⟨x⟩)) = None.
  Proof.
    destruct x.
    + rewrite it_Sn_lft_one_1; auto.
    + rewrite it_n_lft_one_0; auto.
  Qed.

  Fact it_rd_Sn_lft_right n x r b : RD (L↑(S n) (⟨x⟩r⊣b⟧)) = None.
  Proof.
    destruct x.
    + rewrite it_Sn_lft_right_1; auto.
    + rewrite it_n_lft_right_0; auto.
  Qed.

  (** Successive right moves then read *)

  Fact it_rd_Sn_rt_one n x : RD (R↑(S n) (⟨x⟩)) = None.
  Proof.
    destruct x.
    + rewrite it_Sn_rt_one_1; auto.
    + rewrite it_n_rt_one_0; auto.
  Qed.

  Fact it_rd_Sn_rt_left n a l x : RD (R↑(S n) (⟦a⊢l⟨x⟩)) = None.
  Proof.
    destruct x.
    + rewrite it_Sn_rt_left_1; auto.
    + rewrite it_n_rt_left_0; auto.
  Qed.

  (** Identies with read *)

  (* every cells of the left of the head are 2 by 2 identical in
        ⟨x⟩r⊣b⟧ and ⟨x⟩ *)

  Fact it_rd_n_lft_eq_right_one n x r b : RD (L↑n (⟨x⟩r⊣b⟧)) = RD (L↑n (⟨x⟩)).
  Proof.
    destruct n as [ | n ]; auto.
    now rewrite it_rd_Sn_lft_right, it_rd_Sn_lft_one.
  Qed.

  Fact it_rd_n_rt_eq_left_one n a l x : RD (R↑n (⟦a⊢l⟨x⟩)) = RD (R↑n (⟨x⟩)).
  Proof.
    destruct n as [ | n ]; auto.
    now rewrite it_rd_Sn_rt_left, it_rd_Sn_rt_one.
  Qed.

  Fact it_rd_n_lft_eq_both_both n a l x r1 r2 b1 b2 :
          RD (L↑n (⟦a⊢l⟨x⟩r1⊣b1⟧)) = RD (L↑n (⟦a⊢l⟨x⟩r2⊣b2⟧)).
  Proof.
    destruct n as [ | n ]; auto.
    destruct (@list_decomp_1 _ l (S n))
      as [ [ (l' & y & m & -> & <-) | <- ] | H1 ]; try lia.
    + rewrite !it_Sl_lft_both_0; auto.
    + rewrite !it_Sl_lft_both_1; auto.
    + rewrite !it_n_lft_both_2; auto.
  Qed.

  Fact it_rd_n_rt_eq_both_both n a1 a2 l1 l2 x r b :
          RD (R↑n (⟦a1⊢l1⟨x⟩r⊣b⟧)) = RD (R↑n (⟦a2⊢l2⟨x⟩r⊣b⟧)).
  Proof.
    destruct n as [ | n ]; auto.
    destruct (@list_decomp_1 _ r (S n))
      as [ [ (r' & y & m & -> & <-) | <- ] | H1 ]; try lia.
    + rewrite !it_Sl_rt_both_0; auto.
    + rewrite !it_Sl_rt_both_1; auto.
    + rewrite !it_n_rt_both_2; auto.
  Qed.

  Fact it_rd_n_lft_eq_right_right n x r1 r2 b1 b2 :
          RD (L↑n (⟨x⟩r1⊣b1⟧)) = RD (L↑n (⟨x⟩r2⊣b2⟧)).
  Proof. destruct n; auto; rewrite !it_Sn_lft_right_1; auto. Qed.

  Fact it_rd_n_rt_eq_left_left n x l1 l2 a1 a2 :
          RD (R↑n (⟦a1⊢l1⟨x⟩)) = RD (R↑n (⟦a2⊢l2⟨x⟩)). 
  Proof. destruct n; auto; rewrite !it_Sn_rt_left_1; auto. Qed.

  Fact it_rd_n_lft_eq_both_left_Some n a l x r b :
          RD (L↑n (⟦a⊢l⟨Some x⟩r⊣b⟧)) = RD (L↑n (⟦a⊢l⟨Some x⟩)).
  Proof.
    destruct n as [ | n ]; auto.
    destruct l as [ | y l ]; simpl.
    + apply it_rd_n_lft_eq_right_right.
    + destruct y; apply it_rd_n_lft_eq_both_both.
  Qed.

  Fact it_rd_n_rt_eq_both_right_Some n a l x r b :
          RD (R↑n (⟦a⊢l⟨Some x⟩r⊣b⟧)) = RD (R↑n (⟨Some x⟩r⊣b⟧)).
  Proof.
    destruct n as [ | n ]; auto.
    destruct r as [ | y r ]; simpl.
    + apply it_rd_n_rt_eq_left_left.
    + destruct y; apply it_rd_n_rt_eq_both_both.
  Qed.

  (** Two harder lemmas *)

  Lemma it_rd_n_lft_eq_both_left n a l x r b :
           RD (L↑n (⟦a⊢l⟨x⟩r⊣b⟧)) = RD (L↑n (⟦a⊢l⟨x⟩)).
  Proof.
    destruct x as [ x | ]; [ apply it_rd_n_lft_eq_both_left_Some | ].
    destruct n as [ | n ]; auto.
    destruct (repeat_option_choose l) as [ (k & x & m & ->) | -> ].
    + destruct (le_lt_dec k n) as [ H | H ].
      * replace (S n) with (S ⌊(@None Σ)↟k⌋ + (S n - S k)) by (rewrite repeat_length; lia).
        rewrite !iter_plus.
        rewrite it_Sl_lft_both_0.
        rewrite repeat_length, it_Sn_lft_left_1.
        apply it_rd_n_lft_eq_both_left_Some.
      * replace k with (n+(S (k-S n))) by lia.
        rewrite !repeat_plus, !app_ass. 
        simpl repeat; simpl app.
        replace (S n) with (S ⌊(@None Σ)↟n⌋) at 1 by (rewrite repeat_length; lia).
        rewrite it_Sl_lft_both_0, it_Sn_lft_left_1; auto.
    + generalize ⌊l⌋; clear l; intros k.
      destruct (le_lt_dec k n) as [ H | H ].
      - replace (S n) with (S ⌊(@None Σ)↟k⌋ + (S n - S k)) by (rewrite repeat_length; lia).
        rewrite !iter_plus.
        rewrite it_Sl_lft_both_1, repeat_length, it_Sn_lft_left_0.
        apply it_rd_n_lft_eq_right_one.
      - replace k with (n+(1+(k-S n))) by lia.
        rewrite !repeat_plus.
        simpl repeat; simpl app.
        replace (S n) with (S ⌊(@None Σ)↟n⌋) at 1 by (rewrite repeat_length; lia).
        now rewrite it_Sl_lft_both_0, it_Sn_lft_left_1.
  Qed.

  Lemma it_rd_n_rt_eq_both_right n a l x r b :
           RD (R↑n (⟦a⊢l⟨x⟩r⊣b⟧)) = RD (R↑n (⟨x⟩r⊣b⟧)).
  Proof.
    destruct x as [ x | ]; [ apply it_rd_n_rt_eq_both_right_Some | ].
    destruct n as [ | n ]; auto.
    destruct (repeat_option_choose r) as [ (k & x & m & ->) | -> ].
    + destruct (le_lt_dec k n) as [ H | H ].
      * replace (S n) with (S ⌊(@None Σ)↟k⌋ + (S n - S k)) by (rewrite repeat_length; lia).
        rewrite !iter_plus.
        rewrite it_Sl_rt_both_0.
        rewrite repeat_length, it_Sn_rt_right_1.
        apply it_rd_n_rt_eq_both_right_Some.
      * replace k with (n+(S (k-S n))) by lia.
        rewrite !repeat_plus, !app_ass. 
        simpl repeat; simpl app.
        replace (S n) with (S ⌊(@None Σ)↟n⌋) at 1 by (rewrite repeat_length; lia).
        rewrite it_Sl_rt_both_0, it_Sn_rt_right_1; auto.
    + generalize ⌊r⌋; clear r; intros k.
      destruct (le_lt_dec k n) as [ H | H ].
      - replace (S n) with (S ⌊(@None Σ)↟k⌋ + (S n - S k)) by (rewrite repeat_length; lia).
        rewrite !iter_plus.
        rewrite it_Sl_rt_both_1, repeat_length, it_Sn_rt_right_0.
        apply it_rd_n_rt_eq_left_one.
      - replace k with (n+(1+(k-S n))) by lia.
        rewrite !repeat_plus.
        simpl repeat; simpl app.
        replace (S n) with (S ⌊(@None Σ)↟n⌋) at 1 by (rewrite repeat_length; lia).
        now rewrite it_Sl_rt_both_0, it_Sn_rt_right_1.
  Qed.

  Fact it_rd_Sl_lft_left a l x : RD (L↑(S ⌊l⌋) (⟦a⊢l⟨x⟩)) = Some a.
  Proof. now rewrite <- it_rd_n_lft_eq_both_left with (r := nil) (b := a), it_Sl_lft_both_1. Qed.

  Fact it_rd_Sl_rt_right x r b : RD (R↑(S ⌊r⌋) (⟨x⟩r⊣b⟧)) = Some b.
  Proof. now rewrite <- it_rd_n_rt_eq_both_right with (l := nil) (a := b), it_Sl_rt_both_1. Qed.

  Fact it_rd_Sn_n_lft_left a y l x n : RD (L↑(S n) (⟦a⊢l⊳y⟨x⟩)) = RD (L↑n (⟦a⊢l⟨y⟩)).
  Proof.
    rewrite iter_succ; simpl it_lft.
    destruct x; destruct y; simpl; auto; apply it_rd_n_lft_eq_both_left.
  Qed.

  Fact it_rd_Sn_n_rt_right x y r b n : RD (R↑(S n) (⟨x⟩y⊲r⊣b⟧)) = RD (R↑n (⟨y⟩r⊣b⟧)).
  Proof.
    rewrite iter_succ; simpl it_lft.
    destruct x; destruct y; simpl; auto; apply it_rd_n_rt_eq_both_right.
  Qed.

  Fact it_rd_n_lft_out a l x n : 2+⌊l⌋ <= n -> RD (L↑n (⟦a⊢l⟨x⟩)) = None.
  Proof. intro; now rewrite <- it_rd_n_lft_eq_both_left with (r := nil) (b := a), it_n_lft_both_2. Qed.

  Fact it_rd_n_rt_out x r b n : 2+⌊r⌋ <= n -> RD (R↑n (⟨x⟩r⊣b⟧)) = None.
  Proof. intro; now rewrite <- it_rd_n_rt_eq_both_right with (l := nil) (a := b), it_n_rt_both_2. Qed.

  Fact it_rd_Sl_lft_both a l x r b : RD (L↑(S ⌊l⌋) (⟦a⊢l⟨x⟩r⊣b⟧)) = Some a.
  Proof. rewrite it_Sl_lft_both_1; auto. Qed.

  Fact it_rd_Sl_rt_both a l x r b : RD (R↑(S ⌊r⌋) (⟦a⊢l⟨x⟩r⊣b⟧)) = Some b.
  Proof. rewrite it_Sl_rt_both_1; auto. Qed.

  (* These are the two essential results 

     The proofs are now much nicer
   *)

  Theorem it_rd_Sn_lft_wr t n c : RD (L↑(S n) (WR t c)) = RD (L↑(S n) t).
  Proof.
    destruct t as [ x | a ll x | x ll b | a ll x r b ]; simpl it_wr.
    + now rewrite !it_rd_Sn_lft_one.
    + destruct ll as [ | y l ]; rewrite !iter_succ.
      * simpl it_lft; destruct x.
        - apply it_rd_n_lft_eq_right_right.
        - apply it_rd_n_lft_eq_right_one.
      * simpl it_lft; destruct x.
        - destruct y; apply it_rd_n_lft_eq_both_both.
        - destruct y; apply it_rd_n_lft_eq_both_left. 
    + now rewrite !it_rd_Sn_lft_right.
    + destruct ll; simpl.
      * apply it_rd_n_lft_eq_right_right.
      * apply it_rd_n_lft_eq_both_both.
  Qed.

  Theorem it_rd_Sn_rt_wr t n c : RD (R↑(S n) (WR t c)) = RD (R↑(S n) t).
  Proof.
    destruct t as [ x | a ll x | x rr b | a l x rr b ]; simpl it_wr.
    + now rewrite !it_rd_Sn_rt_one.
    + now rewrite !it_rd_Sn_rt_left.
    + destruct rr as [ | y r ]; rewrite !iter_succ.
      * simpl it_rt; destruct x.
        - apply it_rd_n_rt_eq_left_left.
        - apply it_rd_n_rt_eq_left_one.
      * simpl it_rt; destruct x.
        - destruct y; apply it_rd_n_rt_eq_both_both.
        - destruct y; apply it_rd_n_rt_eq_both_right.
    + destruct rr; simpl.
      * apply it_rd_n_rt_eq_left_left.
      * apply it_rd_n_rt_eq_both_both.
  Qed.

  (** injectivity of read *)

  Fact it_rd_lft_inj_left a1 a2 l1 l2 x1 x2 :
        (forall n, RD (L↑n (⟦a1⊢l1⟨x1⟩)) = RD (L↑n (⟦a2⊢l2⟨x2⟩)))
     -> l1 = l2.
  Proof.
    intros H.
    destruct (lt_eq_lt_dec ⌊l1⌋ ⌊l2⌋) as [ [ H2 | H2 ] | H2 ].
    1: generalize (H (S ⌊l2⌋)).
    3: generalize (H (S ⌊l1⌋)).
    all: try (rewrite it_rd_Sl_lft_left, it_rd_n_lft_out; ( lia || easy )).
    revert x1 x2 H; pattern l1, l2.
    revert H2; apply length_eq_ind; auto.
    intros x y l m IH x1 x2 H; f_equal.
    + generalize (H 1); clear H.
      revert x1 x x2 y; intros [] [] [] []; simpl; auto.
    + apply (IH x y); intros n.
      generalize (H (S n)).
      rewrite !it_rd_Sn_n_lft_left; auto.
  Qed.

  Fact it_rd_rt_inj_right x1 x2 r1 r2 b1 b2 :
        (forall n, RD (R↑n (⟨x1⟩r1⊣b1⟧)) = RD (R↑n (⟨x2⟩r2⊣b2⟧)))
     -> r1 = r2.
  Proof.
    intros H.
    destruct (lt_eq_lt_dec ⌊r1⌋ ⌊r2⌋) as [ [ H2 | H2 ] | H2 ].
    1: generalize (H (S ⌊r2⌋)).
    3: generalize (H (S ⌊r1⌋)).
    all: try (rewrite it_rd_Sl_rt_right, it_rd_n_rt_out; ( lia || easy )).
    revert x1 x2 H; pattern r1, r2.
    revert H2; apply length_eq_ind; auto.
    intros x y r m IH x1 x2 H; f_equal.
    + generalize (H 1); clear H.
      revert x1 x x2 y; intros [] [] [] []; simpl; auto.
    + apply (IH x y); intros n.
      generalize (H (S n)).
      rewrite !it_rd_Sn_n_rt_right; auto.
  Qed.

  Fact it_rd_lft_rt_inj_both a1 a2 l1 l2 x1 x2 r1 r2 b1 b2 :
        (forall n, RD (L↑n (⟦a1⊢l1⟨x1⟩r1⊣b1⟧)) = RD (L↑n (⟦a2⊢l2⟨x2⟩r2⊣b2⟧)))
     -> (forall n, RD (R↑n (⟦a1⊢l1⟨x1⟩r1⊣b1⟧)) = RD (R↑n (⟦a2⊢l2⟨x2⟩r2⊣b2⟧)))
     -> l1 = l2 /\ r1 = r2.
  Proof.
    intros H1 H2; split.
    + apply it_rd_lft_inj_left with a1 a2 x1 x2.
      intros n; generalize (H1 n).
      now rewrite !it_rd_n_lft_eq_both_left.
    + apply it_rd_rt_inj_right with x1 x2 b1 b2.
      intros n; generalize (H2 n).
      now rewrite !it_rd_n_rt_eq_both_right.
  Qed.

  Theorem it_rd_injective s t :
        (forall n, RD (L↑n s) = RD (L↑n t))
     -> (forall n, RD (R↑n s) = RD (R↑n t))
     -> s = t.
  Proof.
    intros H1 H2.
    destruct s as [ x1 | a1 l1 x1 | x1 r1 b1 | a1 l1 x1 r1 b1 ]; 
    destruct t as [ x2 | a2 l2 x2 | x2 r2 b2 | a2 l2 x2 r2 b2 ]. 

    + f_equal; apply (H1 0).
    + generalize (H1 (S ⌊l2⌋)).
      now rewrite it_rd_Sl_lft_left, it_rd_Sn_lft_one.
    + generalize (H2 (S ⌊r2⌋)).
      now rewrite it_rd_Sl_rt_right, it_rd_Sn_rt_one.
    + generalize (H1 (S ⌊l2⌋)).
      now rewrite it_rd_Sl_lft_both, it_rd_Sn_lft_one.

    + generalize (H1 (S ⌊l1⌋)).
      now rewrite it_rd_Sl_lft_left, it_rd_Sn_lft_one.
    + assert (l1 = l2) as H3; [ | subst l2 ].
      { apply it_rd_lft_inj_left with (1 := H1). }
      f_equal; auto.
      * generalize (H1 (S ⌊l1⌋)).
        rewrite !it_rd_Sl_lft_left; inversion 1; auto.
      * apply (H1 0).
    + generalize (H2 (S ⌊r2⌋)).
      now rewrite it_rd_Sl_rt_right, it_rd_Sn_rt_left.
    + generalize (H2 (S ⌊r2⌋)).
      now rewrite it_rd_Sl_rt_both, it_rd_Sn_rt_left.

    + generalize (H2 (S ⌊r1⌋)).
      now rewrite it_rd_Sl_rt_right, it_rd_Sn_rt_one.
    + generalize (H2 (S ⌊r1⌋)).
      now rewrite it_rd_Sl_rt_right, it_rd_Sn_rt_left.
    + assert (r1 = r2) as H3; [ | subst r2 ].
      { apply it_rd_rt_inj_right with (1 := H2). }
      f_equal; auto.
      * apply (H1 0).
      * generalize (H2 (S ⌊r1⌋)).
        rewrite !it_rd_Sl_rt_right; inversion 1; auto.
    + generalize (H1 (S ⌊l2⌋)).
      now rewrite it_rd_Sl_lft_both, it_rd_Sn_lft_right.

    + generalize (H1 (S ⌊l1⌋)).
      now rewrite it_rd_Sl_lft_both, it_rd_Sn_lft_one.
    + generalize (H2 (S ⌊r1⌋)).
      now rewrite it_rd_Sl_rt_both, it_rd_Sn_rt_left.
    + generalize (H1 (S ⌊l1⌋)).
      now rewrite it_rd_Sl_lft_both, it_rd_Sn_lft_right.
    + assert (l1 = l2 /\ r1 = r2) as E.
      { apply it_rd_lft_rt_inj_both with (1 := H1); auto. }
      destruct E as (<- & <-).
      f_equal.
      * generalize (H1 (S ⌊l1⌋)).
        rewrite !it_rd_Sl_lft_both; inversion 1; auto.
      * apply (H1 0).
      * generalize (H2 (S ⌊r1⌋)).
        rewrite !it_rd_Sl_rt_both; inversion 1; auto.
  Qed.

  (* Now we build the quotient *)
 
  Fixpoint qt_it (t : q_tape Σ) :=
    match t with
      | qt_emp    => it_nil
      | qt_lft t  => L (qt_it t)
      | qt_rt  t  => R (qt_it t)
      | qt_wr t x => WR (qt_it t) x
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
  
  Fact it_qt_class t : qt_it (it_qt t) = t.
  Proof. apply (proj2_sig (it_qt_full t)). Qed.

  (** Reading in t is the same as reading on qt_it t *)

  Lemma qt_it_rd t n : RD (L↑n (qt_it t)) = qt_rdZ t (-Z.of_nat n)
                    /\ RD (R↑n (qt_it t)) = qt_rdZ t (Z.of_nat n).
  Proof.
    revert n.
    induction t as [ | t IHt | t IHt | t IHt x ]; intros n.
    + split. 
      * rewrite it_n_lft_one_0; auto.
      * rewrite it_n_rt_one_0; auto.
    + generalize (proj1 (IHt (S n))); simpl; intros ->; split.
      * f_equal; lia.
      * destruct n as [ | n ].
        - apply (IHt 1).
        - simpl iter; rewrite it_rt_lft. 
          generalize (proj2 (IHt n)); intros ->; f_equal; lia.
    + split.
      * destruct n as [ | n ]; simpl iter.
        - apply (IHt 1).
        - rewrite it_lft_rt.
          generalize (proj1 (IHt n)); intros ->. 
          Opaque Z.of_nat.
          cbn; f_equal; lia.
      * generalize (proj2 (IHt (S n))); simpl; intros ->; f_equal; lia.
    + destruct n as [ | n ].
      * simpl iter; simpl qt_it; rewrite it_rd_wr.
        Transparent Z.of_nat. 
        simpl; auto.
      * simpl qt_it.
        rewrite it_rd_Sn_lft_wr; try lia.
        rewrite it_rd_Sn_rt_wr; try lia.
        apply IHt.
  Qed.

  (* This gives us the quotient, it is an infinite and non-discrete quotient *)

  Theorem it_qt_repr s t : s ~qt t <-> qt_it s = qt_it t.
  Proof.
    split.
    + intros H1.
      apply it_rd_injective; intros n.
      * rewrite !(proj1 (qt_it_rd _ _)); auto.
      * rewrite !(proj2 (qt_it_rd _ _)); auto.
    + intros H i.
      destruct (Z.le_ge_cases i 0) as [ H1 | H1 ].
      * destruct (Z_of_nat_complete (-i)) as (n & Hn); try lia.
        replace i with (- Z.of_nat n)%Z by lia.
        rewrite <- !(proj1 (qt_it_rd _ _)), H; auto.
      * destruct (Z_of_nat_complete i) as (n & ->); auto.
        rewrite <- !(proj2 (qt_it_rd _ _)), H; auto.
  Qed.

  Corollary qt_it_spec t : t ~qt it_qt (qt_it t).
  Proof. apply it_qt_repr; now rewrite it_qt_class. Qed.

  Theorem qt_it_equiv s t : qt_it s = qt_it t -> s ~it t.
  Proof.
    
    
    induction 1.


End infinite_tapes.

Check it_qt_class.
Check it_qt_repr.

Print Assumptions it_qt_repr.


  (* We should be able to compute the normal form of any iter lft ... *)

  (* I think one can also show that equivalent tapes are identical with that definition *)


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

