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
  Require Import rel_utils nat_utils Z_utils tapes.

Import NatUtilsNotations TapeNotations.

Set Implicit Arguments.

Implicit Type T : TapeSpec.

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
        apply bs_read, bs_iter_move, 
              bs_move, bisimilar_sym,
              write_read. 
      * apply bisimilar_trans with (1 := H3).
        apply bs_iter_move; subst.
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
        apply bs_read, bs_iter_move, bs_move, write_read.
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


Section SEARCH_LPO.

  Hint Resolve bool_dec : core.

  Theorem Coq_dec_SEARCH_SBTM t : Coq_dec (SEARCH rt true SBTM_tape t).
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

  Theorem Coq_dec_SEARCH_Z_entails_LPO : (forall t, Coq_dec (SEARCH rt true Z_tape t)) -> LPO.
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

  Theorem Coq_dec_SEARCH_ZB_BLPO : (forall t, Coq_dec (SEARCH rt true ZB_tape t)) -> BLPO.
  Proof.
    intros H f Hf.
    assert ({ t' : ZB_tape | proj1_sig t' = lift_Z f}) as (t' & H').
    1: { refine (exist _ (exist _ (lift_Z f) _) eq_refl).
         destruct Hf as (m & Hm).
         exists m; intros [ | | n ]; auto; simpl.
         destruct (le_lt_dec m n); auto. }
    destruct (H t') as [ H1 | H1 ]; [ left | right ].
    + apply minimize in H1 as (n & Hn & _).
      * unfold ZB_tape in Hn; simpl in Hn; unfold ZBtape_rd in Hn.
        rewrite ZBtape_iter_eq, H' in Hn.
        destruct n as [ | n ].
        - easy.
        - rewrite Ztape_read_iter_rt in Hn.
          exists n; auto.
      * intros; apply bool_dec.
    + intros n; case_eq (f n); auto; intros Hn; exfalso.
      apply H1; exists (S n).
      unfold ZB_tape, read, move, ZBtape_rd.
      generalize (f_equal (Ztape_rd) (ZBtape_iter_eq (S n) rt t')).
      rewrite H', Ztape_read_iter_rt; simpl.
      rewrite Hn; intros <-; auto.
  Qed.

  Theorem SEARCH_TM : TM_dec_on (SEARCH rt true) SBTM_tape -> TM_dec_on (SEARCH rt true) ZB_tape.
  Proof.
    intros (M & s & H1 & H2).
    exists M, s; split; auto.
    + intros t.
      destruct (ZB_tape_bisim_SBTM_tape t) as (t1 & Ht1).
      generalize (H1 t1).
      apply TM_HALT_bisimilar; auto.
    + intros t t' H.
      destruct (ZB_tape_bisim_SBTM_tape t) as (t1 & Ht1).
      destruct TM_compute_bisim with (1 := Ht1) (2 := H)
        as (t1' & H3 & H4).
      apply H2 in H3.
      apply bs_read in H4 as ->.
      rewrite H3; symmetry.
      split; intros (n & Hn); exists n; revert Hn; intros ->; apply bs_read, bs_iter_move; auto.
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

  Corollary SEARCH_SBTM_BLPO : TM_dec_on (SEARCH rt true) SBTM_tape -> BLPO.
  Proof. auto. Qed. 

End SEARCH_LPO.

Check Coq_dec_SEARCH_SBTM.
Print Assumptions Coq_dec_SEARCH_SBTM.

Check SEARCH_SBTM_BLPO.
Print Assumptions SEARCH_SBTM_BLPO.
 


  