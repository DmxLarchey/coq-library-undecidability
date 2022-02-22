Require Import List Arith Lia.

Set Implicit Arguments.

Inductive dir := lft | rt.

Section move_many.

  Variables (T : Type) (mv : dir -> T -> T).

  Fixpoint move_many l t :=
    match l with
      | nil  => t
      | d::l => (move_many l (mv d t))
    end.

  Fact move_many_fix d l t : move_many (d::l) t = move_many l (mv d t).
  Proof. reflexivity. Qed.

End move_many.

Definition bisimilar X T₁ r₁ m₁ T₂ r₂ m₂ :=
   fun t₁ t₂ => forall l, r₁ (@move_many T₁ m₁ l t₁) = r₂ (@move_many T₂ m₂ l t₂) :> X.

Fact bisimilar_refl X T r m t : @bisimilar X T r m _ r m t t.
Proof. intro; reflexivity. Qed.

Fact bisimilar_sym X T₁ r₁ m₁ T₂ r₂ m₂ t₁ t₂ : @bisimilar X T₁ r₁ m₁ T₂ r₂ m₂ t₁ t₂ -> bisimilar r₂ m₂ r₁ m₁ t₂ t₁.
Proof. intros H l; symmetry; apply H. Qed.

Fact bisimilar_trans X T₁ r₁ m₁ T₂ r₂ m₂ T₃ r₃ m₃ t₁ t₂ t₃ : 
       @bisimilar X T₁ r₁ m₁ T₂ r₂ m₂ t₁ t₂ 
    -> @bisimilar _ _  r₂ m₂ T₃ r₃ m₃ t₂ t₃
    ->  bisimilar r₁ m₁ r₃ m₃ t₁ t₃.
Proof. intros H1 H2 l; rewrite H1; auto. Qed.

Section bisim.

  Variable (X T : Type) (rd : T -> X) (mv : dir -> T -> T).

  Definition bisim := @bisimilar X T rd mv T rd mv.

  Infix "~b" := bisim (at level 70).

  Fact bisim_refl t : t ~b t.
  Proof. intros l; auto. Qed.

  Fact bisim_sym r t : r ~b t -> t ~b r.
  Proof. intros H l; symmetry; auto. Qed.

  Fact bisim_trans r s t : r ~b s -> s ~b t -> r ~b t.
  Proof. intros H1 ? l; rewrite H1; trivial. Qed.

End bisim.

Section iter.

  Variable (X : Type) (f : X -> X).

  Fixpoint iter n :=
    match n with
      | 0   => fun x => x
      | S n => fun x => iter n (f x)
    end.

  Fact iter_fix n x : iter (S n) x = iter n (f x).
  Proof. trivial. Qed.

  Fact iter_plus n m x : iter (n+m) x = iter m (iter n x).
  Proof. revert x; induction n; simpl; auto. Qed.

  Fact iter_S n x : iter (S n) x = f (iter n x).
  Proof.
    replace (S n) with (n+1) by lia.
    rewrite iter_plus; auto.
  Qed.

End iter.

Reserved Notation "x '~b' y" (at level 70).

Record tape_spec := {
  tape :> Type;
  move : dir -> tape -> tape;
  read : tape -> bool;
  write : bool -> tape -> tape;
  read_write : forall t b, read (write b t) = b;
  write_read : forall t, (bisim read move) (write (read t) t) t;
  move_write : forall t n d b, read (iter (move d) (S n) (write b t)) = read (iter (move d) (S n) t);
  write_write : forall t b c, (bisim read move) (write b (write c t)) (write b t);
  left_right : forall t, (bisim read move) (move lft (move rt t)) t;
  right_left : forall t, (bisim read move) (move rt (move lft t)) t;
}.

Definition bs T1 T2 := bisimilar (@read T1) (@move T1) (@read T2) (@move T2).

Infix "~b" := (@bs _ _) (at level 70).

Arguments read {_}.
Arguments move {_}.
Arguments write {_}.

Section Zmoves.

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

  Fixpoint moves2Z l :=
    match l with
      | nil    => zero
      | lft::l => Zpred (moves2Z l)
      | rt::l  => Zsucc (moves2Z l)
    end.


  Definition Ziter X (f g : X -> X) z :=
    match z with
      | neg n => iter f (S n)
      | zero  => fun x => x
      | pos n => iter g (S n)
    end.

  Fact bs_move (T1 T2 : tape_spec) (t1 : T1) (t2 : T2) d : t1 ~b t2 -> move d t1 ~b move d t2.
  Proof. intros H l; apply (H (_::_)). Qed.

  Hint Resolve bs_move : core.

  Fact bs_moves_dir (T1 T2 : tape_spec) n d (t1 : T1) (t2 : T2) : t1 ~b t2 -> iter (move d) n t1 ~b iter (move d) n t2.
  Proof.
    revert t1 t2; induction n as [ | n IHn ]; auto; simpl; intros t1 t2 H.
    apply IHn; auto.
  Qed.

  Variable (T : tape_spec).

  Implicit Type t : T.

  Hint Resolve bisim_refl : core.

  Fact bs_moves_Z l (t : T) : move_many move l t ~b Ziter (move lft) (move rt) (moves2Z l) t.
  Proof.
    revert t; induction l as [ | [] l IHl ]; intros t; simpl.
    + apply bisim_refl.
    + apply bisim_trans with (1 := IHl _).
      destruct (moves2Z l) as [ | | [|n] ]; simpl; try apply bisim_refl.
      * apply right_left.
      * apply bs_moves_dir, bs_move, right_left.
    + apply bisim_trans with (1 := IHl _).
      destruct (moves2Z l) as [ [|n] | | ]; simpl; try apply bisim_refl.
      * apply left_right.
      * apply bs_moves_dir, bs_move, left_right.
  Qed.

End Zmoves.

Section bs.

  Variable (T1 T2 : tape_spec).

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

Record TM := Build_TM {
  state : Type;
  (* transition table *)
  trans : state -> bool -> option (state * bool * dir) 
}.

Fixpoint rel_iter X (R : X -> X -> Prop) n :=
  match n with 
    | 0   => eq
    | S n => fun x y => exists z, R x z /\ rel_iter R n z y
  end.

Inductive TM_step {T : tape_spec} (M : TM) : (state M*T) -> (state M*T) -> Prop :=
  | in_TM_step s₁ t₁ s₂ b d : trans M s₁ (read t₁) = Some (s₂,b,d) -> TM_step M (s₁,t₁) (s₂,move d (write b t₁)).

Definition TM_steps {T} M := rel_iter (@TM_step T M).

Section bs_TM.

  Variable (M : TM) (T T' : tape_spec).

  Let TM_step_bisim_rec (x₁ y₁ : state M * T) (x₂ : state M * T') : 
    fst x₁ = fst x₂ -> snd x₁ ~b snd x₂ -> TM_step M x₁ y₁ -> exists y₂, fst y₁ = fst y₂ /\ snd y₁ ~b snd y₂ /\ TM_step M x₂ y₂.
  Proof.
    intros H1 H2 H3; revert H3 x₂ H1 H2.
    induction 1 as [ s1 t1 s2 b d H ]; intros (s3,t3) H1 H2; simpl in *; subst s3.
    exists (s2,move d (write b t3)); simpl; split; auto; split.
    + apply bs_move, bs_write; auto.
    + constructor; rewrite <- H.
      f_equal; symmetry; apply bs_read; auto.
  Qed.

  Lemma TM_step_bisim s₁ (t₁ : T) s₂ t₂ (t₁' : T') : 
     t₁ ~b t₁' -> TM_step M (s₁,t₁) (s₂,t₂) -> exists t₂', t₂ ~b t₂' /\ TM_step M (s₁,t₁') (s₂,t₂').
  Proof.
    intros H1 H2.
    apply (@TM_step_bisim_rec (s₁,t₁) (s₂,t₂) (s₁,t₁')) in H2 as ((?,t') & H3 & H4 & H5); simpl in *; subst; eauto.
  Qed.

  Theorem TM_steps_bisim n s₁ (t₁ : T) s₂ t₂ (t₁' : T') : 
     t₁ ~b t₁' -> TM_steps M n (s₁,t₁) (s₂,t₂) -> exists t₂', t₂ ~b t₂' /\ TM_steps M n (s₁,t₁') (s₂,t₂').
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

End bs_TM.

Section TM_HALT_bisimilar.

  Definition TM_HALT {T : tape_spec} (M : TM) (s : state M) (t : T) :=
    exists o n, TM_steps M n (s,t) o /\ forall x, ~ TM_step M o x.

  Let bs_TM_HALT_half (T1 T2 : tape_spec) M s (t1 : T1) (t2 : T2) : t1 ~b t2 -> TM_HALT M s t1 -> TM_HALT M s t2.
  Proof.
    intros E ((s',t') & n & H1 & H2).
    destruct TM_steps_bisim with (1 := E) (2 := H1) as (t3 & H3 & H4).
    exists (s',t3), n;split; auto.
    intros (s4,t4) H.
    apply bisimilar_sym in H3.
    destruct TM_step_bisim with (1 := H3) (2 := H) as (t5 & H5 & H6).
    apply H2 in H6; auto.
  Qed.

  Theorem TM_HALT_bisimilar (T1 T2 : tape_spec) M s (t1 : T1) (t2 : T2) : t1 ~b t2 -> TM_HALT M s t1 <-> TM_HALT M s t2.
  Proof.
    intros H; split; apply bs_TM_HALT_half; auto.
    apply bisimilar_sym; auto.
  Qed.

End TM_HALT_bisimilar.

Fixpoint list_repeat X n (x : X) :=
  match n with 
    | 0 => nil
    | S n => x::list_repeat n x
  end.

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

  Definition Tape_SBTM : tape_spec.
  Proof.
    exists _ sbtm_mv sbtm_rd sbtm_wr.
    + intros ([],?); simpl; auto.
    + intros ((l,b),r); simpl; apply bisim_refl.
    + intros ((l,b),r) n [] c; simpl sbtm_wr.
      * apply sbtm_rd_mv_lft_S.
      * apply sbtm_rd_mv_rt_S.
    + intros ([],?) ? ?; simpl; apply bisim_refl.
    + intros ((l,b),[ | x r ]); simpl.
      2: apply bisim_refl.
      apply bisim_sym.
      rewrite (app_nil_end l) at 2. 
      apply sbtm_bisim with (n := 0) (m := 1) (r := nil).
    + intros (([|x l],b),r); simpl.
      2: apply bisim_refl.
      apply bisim_sym.
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

  Definition Tape_Z : tape_spec.
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
  Qed.

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
  Qed.

  Definition ZBtape_rd (t : ZB_tape) := Ztape_rd (proj1_sig t).

  Definition ZBtape_wr (b : bool) : ZB_tape -> ZB_tape.
  Proof.
    intros (t & Ht).
    exists (Ztape_wr b t).
    destruct Ht as (m & Hm).
    exists m.
    intros z; destruct (Hm z) as [ H | ]; auto.
    destruct z; simpl; auto; right; lia.
  Qed.

  Definition Tape_ZB : tape_spec.
  Proof.
    exists _ ZBtape_mv ZBtape_rd ZBtape_wr.
  Admitted.

End Ztape_bounded.


  