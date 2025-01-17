Require Import Undecidability.SOL.SOL.
Require Import Undecidability.Shared.Dec.
From Undecidability.Shared.Libs.PSL Require Import Vectors.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Stdlib Require Import EqdepFacts Eqdep_dec Lia.

Unset Implicit Arguments.

Module VectorForall.
Import Vector.

Definition Forall {X} (p : X -> Prop) := fix Forall {n} (v : t X n) :=
  match v with
  | nil _ => True
  | cons _ x _ v => p x /\ Forall v
  end.

Definition Forall2 {X Y} (p : X -> Y -> Prop) := fix Forall2 {n} (v1 : t X n) (v2 : t Y n) :=
  match v1 in Vector.t _ n return t Y n -> Prop with
  | nil _ => fun _ => True
  | cons _ x _ v1 => fun v2 => p x (hd v2) /\ Forall2 v1 (tl v2)
  end v2.

  
Lemma Forall2_Forall {X Y Z n} (p : Y -> Z -> Prop) (f1 : X -> Y) (f2 : X -> Z) v :
  @Forall2 Y Z p n (map f1 v) (map f2 v) <-> @Forall X (fun x => p (f1 x) (f2 x)) n v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall_ext {X n} (p q : X -> Prop) (v : t X n) :
  (forall x, p x -> q x) -> Forall p v -> Forall q v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall_ext_Forall {X n} (p q : X -> Prop) (v : t X n) :
  Forall (fun x => p x -> q x) v -> Forall p v -> Forall q v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall_ext_in {X n} (p q : X -> Prop) (v : t X n) :
  (forall x, In x v -> p x -> q x) -> Forall p v -> Forall q v.
Proof.
  intros H1 H2. induction v; cbn. easy. split. apply H1. constructor.
  apply H2. apply IHv. intros x H3. apply H1. now constructor. apply H2.
Qed.

Lemma Forall_in {X n} (p : X -> Prop) (v : t X n) :
  Forall p v <-> forall x, In x v -> p x.
Proof.
  induction v. easy. split.
  - intros H1 x.
    assert (HIn : forall {n: nat} (x : X) (xs : Vector.t X n), In x xs ->
      match xs with | Vector.nil _ => False | cons _ y _ ys => y = x \/ In x ys end).
    { now intros ??? []; [left|right]. }
    intros ?%HIn. firstorder (now subst).
  - intros H. split. apply H. constructor. apply IHv. intros x H1. apply H. now constructor.
Qed.

Lemma Forall_map {X Y n} (p : Y -> Prop) (f : X -> Y) (v : t X n) :
  Forall p (map f v) <-> Forall (fun x => p (f x)) v.
Proof.
  induction v; firstorder.
Qed.

Lemma map_ext_forall {X Y n} (f g : X -> Y) (v : t X n):
  Forall (fun x => f x = g x) v -> map f v = map g v.
Proof.
  induction v; cbn. reflexivity. intros. f_equal; firstorder.
Qed.

End VectorForall.
Export VectorForall.

#[export]
Instance eqdec_full_logic_sym : eq_dec full_logic_sym.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

#[export]
Instance eqdec_full_logic_quant : eq_dec full_logic_quant.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

Definition L_binop (n : nat) := List.cons Conj (List.cons Impl (List.cons Disj List.nil)).

#[export]
Instance enum_binop :
  list_enumerator__T L_binop binop.
Proof.
  intros []; exists 0; cbn; tauto.
Qed.

Definition L_quantop (n : nat) := List.cons All (List.cons Ex List.nil).

#[export]
Instance enum_quantop :
  list_enumerator__T L_quantop quantop.
Proof.
  intros []; exists 0; cbn; tauto.
Qed.

Lemma enumT_binop :
  enumerable__T binop.
Proof.
  apply enum_enumT. exists L_binop. apply enum_binop.
Qed.

Lemma enumT_quantop :
  enumerable__T quantop.
Proof.
  apply enum_enumT. exists L_quantop. apply enum_quantop.
Qed.



(* ** Elimination for terms *)

Section Elimination.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.

  Lemma term_ind (p : term -> Prop) :
    (forall n, p (var_indi n))
    -> (forall ar n v (IH : Forall p v), p (func (var_func n ar) v))
    -> (forall f v (IH : Forall p v), p (func (sym f) v))
    -> forall t, p t.
  Proof.
    intros H1 H2 H3. fix term_ind 1. destruct t.
    - apply H1.
    - destruct f.
      + apply H2. induction v.
        * constructor.
        * constructor. apply term_ind. exact IHv.
      + apply H3. induction v.
        * constructor.
        * constructor. apply term_ind. exact IHv.
  Qed.

  Lemma term_ind' (p : term -> Prop) :
    (forall n, p (var_indi n))
    -> (forall ar (f : function ar) v (IH : Forall p v), p (func f v))
    -> forall t, p t.
  Proof.
    intros H1 H2. fix term_ind' 1. destruct t.
    - apply H1.
    - apply H2. clear f. induction v; constructor. apply term_ind'. exact IHv.
  Qed.

End Elimination.



Section FirstorderFragment.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Fixpoint first_order_term (t : term) := match t with
    | var_indi _ => True
    | func (var_func _) _ => False 
    | func (sym f) v => Forall first_order_term v
  end.

  Fixpoint first_order phi := match phi with
    | fal => True
    | atom (pred _) v => Forall first_order_term v
    | atom (var_pred _ _) _ => False
    | bin _ phi psi => first_order phi /\ first_order psi
    | quant_indi _ phi => first_order phi
    | quant_func _ _ _ => False
    | quant_pred _ _ _ => False
  end.

End FirstorderFragment.


Section FunctionFreeFragment.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Fixpoint funcfreeTerm (t : SOL.term) := match t with
  | var_indi x => True
  | func (var_func _) _ => False
  | func (sym _) v => Forall funcfreeTerm v
  end.

  Fixpoint funcfree (phi : SOL.form) := match phi with
  | atom _ v => Forall funcfreeTerm v
  | fal => True
  | bin _ phi psi => funcfree phi /\ funcfree psi
  | quant_indi _ phi => funcfree phi
  | quant_func _ ar' phi => False
  | quant_pred _ _ phi => funcfree phi
  end.

  Lemma firstorder_funcfree_term t :
    first_order_term t -> funcfreeTerm t.
  Proof.
    now induction t.
  Qed.

  Lemma firstorder_funcfree phi :
    first_order phi -> funcfree phi.
  Proof.
    induction phi; firstorder. now destruct p.
  Qed.

End FunctionFreeFragment.


(* *** Bounds *)

Section Bounded.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Fixpoint bounded_indi_term n (t : term) := match t with
    | var_indi x => n > x
    | func _ v => Forall (bounded_indi_term n) v
  end.

  Fixpoint bounded_func_term ar n (t : term) := match t with
    | var_indi x => True
    | @func _ ar' (var_func x) v => (n > x \/ ar <> ar') /\ Forall (bounded_func_term ar n) v
    | func (sym _) v => Forall (bounded_func_term ar n) v
  end.

  Fixpoint bounded_indi n (phi : form) := match phi with
    | atom _ v => Forall (bounded_indi_term n) v
    | fal => True
    | bin _ phi psi => bounded_indi n phi /\ bounded_indi n psi
    | quant_indi _ phi => bounded_indi (S n) phi
    | quant_func _ _ phi => bounded_indi n phi
    | quant_pred _ _ phi => bounded_indi n phi
  end.

  Fixpoint bounded_func ar n (phi : form) := match phi with
    | atom _ v => Forall (bounded_func_term ar n) v
    | fal => True
    | bin _ phi psi => bounded_func ar n phi /\ bounded_func ar n psi
    | quant_indi _ phi => bounded_func ar n phi
    | quant_func _ ar' phi => (ar = ar' /\ bounded_func ar (S n) phi) \/ (ar <> ar' /\ bounded_func ar n phi)
    | quant_pred _ _ phi => bounded_func ar n phi
  end.

  Fixpoint bounded_pred ar n (phi : form) := match phi with
    | @atom _ _ _ ar' (var_pred x) _ => n > x \/ ar <> ar'
    | atom (pred _) _ => True
    | fal => True
    | bin _ phi psi => bounded_pred ar n phi /\ bounded_pred ar n psi
    | quant_indi _ phi => bounded_pred ar n phi
    | quant_func _ _ phi => bounded_pred ar n phi
    | quant_pred _ ar' phi => (ar = ar' /\ bounded_pred ar (S n) phi) \/ (ar <> ar' /\ bounded_pred ar n phi)
  end.

  Definition closed phi := bounded_indi 0 phi /\ (forall ar, bounded_func ar 0 phi) /\ (forall ar, bounded_pred ar 0 phi).

  Definition bounded_indi_L n A := forall phi, List.In phi A -> bounded_indi n phi.
  Definition bounded_func_L ar n A := forall phi, List.In phi A -> bounded_func ar n phi.
  Definition bounded_pred_L ar n A := forall phi, List.In phi A -> bounded_pred ar n phi.


  Lemma bounded_indi_term_up n m t :
    m >= n -> bounded_indi_term n t -> bounded_indi_term m t.
  Proof using Σ_pred ops.
    intros H1. induction t; intros H2; cbn in *.
    lia. induction v; firstorder. induction v; firstorder.
  Qed.

  Lemma bounded_func_term_up ar n m t :
    m >= n -> bounded_func_term ar n t -> bounded_func_term ar m t.
  Proof.
    intros H1. induction t; intros H2; cbn in *. easy. split. lia.
    eapply Forall_ext_Forall. apply IH. apply H2.
    eapply Forall_ext_Forall. apply IH. apply H2.
  Qed.

  Lemma bounded_indi_up n m phi :
    m >= n -> bounded_indi n phi -> bounded_indi m phi.
  Proof.
    revert m n. induction phi; intros m n' H1 H2; cbn in *. easy.
    eapply Forall_ext. 2: apply H2. intros v; now apply bounded_indi_term_up.
    firstorder. eapply IHphi. 2: apply H2. lia. all: firstorder.
  Qed.

  Lemma bounded_func_up ar n m phi :
    m >= n -> bounded_func ar n phi -> bounded_func ar m phi.
  Proof.
    revert m n. induction phi; intros m n' H1 H2; cbn in *. easy.
    eapply Forall_ext. 2: apply H2. intros v; now apply bounded_func_term_up.
    1,2,4: firstorder. destruct H2 as [H2|H2].
    - left. split. easy. eapply IHphi. 2: apply H2. lia.
    - right. split. easy. eapply IHphi. 2: apply H2. lia.
  Qed.

  Lemma bounded_pred_up ar n m phi :
    m >= n -> bounded_pred ar n phi -> bounded_pred ar m phi.
  Proof.
    revert m n. induction phi; intros m n' H1 H2; cbn in *. easy.
    destruct p. lia. easy. 1-3: firstorder. destruct H2 as [H2|H2].
    - left. split. easy. eapply IHphi. 2: apply H2. lia.
    - right. split. easy. eapply IHphi. 2: apply H2. lia.
  Qed.

  Lemma funcfree_bounded_func_term t :
    funcfreeTerm t -> forall x ar, bounded_func_term x ar t.
  Proof.
    intros F x ar. induction t; cbn in *; try easy.
    eapply Forall_ext_Forall. apply IH. apply F.
  Qed.

  Lemma funcfree_bounded_func phi :
    funcfree phi -> forall x ar, bounded_func x ar phi.
  Proof.
    intros F. induction phi; intros x ar'; cbn. 1,3-6: firstorder.
    apply Forall_in. intros v H. apply funcfree_bounded_func_term.
    eapply Forall_in in F. apply F. easy.
  Qed.

  Lemma firstorder_bounded_pred phi :
    first_order phi -> forall x ar, bounded_pred x ar phi.
  Proof.
    induction phi; firstorder. now destruct p.
  Qed.


End Bounded.



(* *** Discreteness *)

Section EqDec.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Context `{syms_eq_dec : eq_dec syms}.
  Context `{preds_eq_dec : eq_dec preds}.
  Context `{binop_eq_dec : eq_dec binop}.
  Context `{quantop_eq_dec : eq_dec quantop}.

  Lemma function_eq_dep ar (f1 f2 : function ar) :
    eq_dep _ _ ar f1 ar f2 <-> f1 = f2.
  Proof.
    rewrite <- eq_sigT_iff_eq_dep. split.
    - intros H%Eqdep_dec.inj_pair2_eq_dec. exact H. decide equality.
    - now intros ->.
  Qed.

  Lemma predicate_eq_dep ar (P1 P2 : predicate ar) :
    eq_dep _ _ ar P1 ar P2 <-> P1 = P2.
  Proof.
    rewrite <- eq_sigT_iff_eq_dep. split.
    - intros H%inj_pair2_eq_dec. exact H. decide equality.
    - now intros ->.
  Qed.

  Lemma dec_function_dep ar1 ar2 (f1 : function ar1) (f2 : function ar2) :
    dec (eq_dep _ _ ar1 f1 ar2 f2).
  Proof using syms_eq_dec.
    destruct f1, f2.
    - destruct (PeanoNat.Nat.eq_dec ar ar0) as [->|].
      destruct (PeanoNat.Nat.eq_dec n n0) as [->|].
      left; now apply function_eq_dep.
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right; intros H%eq_sigT_iff_eq_dep; congruence.
    - destruct (PeanoNat.Nat.eq_dec ar (ar_syms f)) as [->|].
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right. intros H%eq_sigT_iff_eq_dep. inversion H.
    - destruct (PeanoNat.Nat.eq_dec ar (ar_syms f)) as [->|].
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right. intros H%eq_sigT_iff_eq_dep. inversion H.
    - destruct (syms_eq_dec f f0) as [->|].
      left; now apply function_eq_dep.
      right. now intros [=]%eq_sigT_iff_eq_dep.
  Qed.

  Lemma dec_predicate_dep ar1 ar2 (P1 : predicate ar1) (P2 : predicate ar2) :
    dec (eq_dep _ _ ar1 P1 ar2 P2).
  Proof using preds_eq_dec.
    destruct P1, P2.
    - destruct (PeanoNat.Nat.eq_dec ar ar0) as [->|].
      destruct (PeanoNat.Nat.eq_dec n n0) as [->|].
      left; now apply predicate_eq_dep.
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right; intros H%eq_sigT_iff_eq_dep; congruence.
    - destruct (PeanoNat.Nat.eq_dec ar (ar_preds P)) as [->|].
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right. intros H%eq_sigT_iff_eq_dep. inversion H.
    - destruct (PeanoNat.Nat.eq_dec ar (ar_preds P)) as [->|].
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right. intros H%eq_sigT_iff_eq_dep. inversion H.
    - destruct (preds_eq_dec P P0) as [->|].
      left; now apply predicate_eq_dep.
      right. now intros [=]%eq_sigT_iff_eq_dep.
  Qed.

  #[export]
  Instance function_eq_dec ar :
    eq_dec (function ar).
  Proof using syms_eq_dec.
    intros f1 f2. destruct (dec_function_dep _ _ f1 f2).
    - left. now apply function_eq_dep.
    - right. now intros H%function_eq_dep.
  Qed.

  #[export]
  Instance predicate_eq_dec ar :
    eq_dec (predicate ar).
  Proof using preds_eq_dec.
    intros P1 P2. destruct (dec_predicate_dep _ _ P1 P2).
    - left. now apply predicate_eq_dep.
    - right. now intros H%predicate_eq_dep.
  Qed.

  #[export]
  Instance term_eq_dec :
    eq_dec term.
  Proof using syms_eq_dec.
    fix IH 1. intros [] []; try (right; congruence).
    - destruct (PeanoNat.Nat.eq_dec n n0) as [->|]. now left. right; congruence.
    - destruct (PeanoNat.Nat.eq_dec ar ar0) as [->|]. 2: right; congruence.
      destruct (function_eq_dec ar0 f f0) as [->|].
      + assert ({v = v0} + {v <> v0}) as [->|]. {
          clear f0. induction v.
          * left. pattern v0. now apply Vector.case0.
          * apply (Vector.caseS' v0). intros.
            destruct (IH h h0) as [->|]. 2: right; congruence.
            destruct (IHv t) as [->|]. now left. right. intros H. apply n0.
            enough (Vector.tl (Vector.cons term h0 n v) = Vector.tl (Vector.cons term h0 n t)) by easy.
            now rewrite H. }
        now left. right. intros H. apply n. inversion H.
        apply inj_pair2_eq_dec in H1. exact H1. decide equality.
      + right. intros H. apply n. inversion H.
        apply inj_pair2_eq_dec in H1. exact H1. decide equality.
  Qed.

  #[export]
  Instance form_eq_dec :
    eq_dec form.
  Proof using syms_eq_dec quantop_eq_dec preds_eq_dec binop_eq_dec.
    induction x; intros []; try (right; congruence).
    - now left.
    - destruct (PeanoNat.Nat.eq_dec ar ar0) as [->|]. 2: right; congruence.
      destruct (predicate_eq_dec ar0 p p0) as [->|].
      + rename t into v. rename t0 into v0. assert ({v = v0} + {v <> v0}) as [->|]. {
          clear p0. induction v.
          * left. pattern v0. now apply Vector.case0.
          * apply (Vector.caseS' v0). intros.
            destruct (term_eq_dec h h0) as [->|]. 2: right; congruence.
            destruct (IHv t) as [->|]. now left. right. intros H. apply n0.
            enough (Vector.tl (Vector.cons term h0 n v) = Vector.tl (Vector.cons term h0 n t)) by easy.
            now rewrite H. }
        now left. right. intros H. apply n. inversion H.
        apply inj_pair2_eq_dec in H1. exact H1. decide equality.
      + right. intros H. apply n. inversion H. apply inj_pair2_eq_dec in H1. exact H1. decide equality.
    - destruct (binop_eq_dec b b0) as [->|]. 2: right; congruence.
      destruct (IHx1 f) as [->|]. 2: right; congruence.
      destruct (IHx2 f0) as [->|]. now left. right; congruence.
    - destruct (quantop_eq_dec q q0) as [->|]. 2: right; congruence.
      destruct (IHx f) as [->|]. now left. right; congruence.
    - destruct (quantop_eq_dec q q0) as [->|]. 2: right; congruence.
      destruct (PeanoNat.Nat.eq_dec n n0) as [->|]. 2: right; congruence.
      destruct (IHx f) as [->|]. now left. right; congruence.
    - destruct (quantop_eq_dec q q0) as [->|]. 2: right; congruence.
      destruct (PeanoNat.Nat.eq_dec n n0) as [->|]. 2: right; congruence.
      destruct (IHx f) as [->|]. now left. right; congruence.
  Qed.

End EqDec.


(* *** Enumerability *)


From Stdlib Require Import List.
Import ListNotations.

#[local] Notation "x 'el' L" := (In x L) (at level 70).
#[local] Notation "[ s | p ∈ A ]" := (map (fun p => s) A) (p pattern).

Ltac in_app n :=
  (match goal with
  | [ |- In _ (_ ++ _) ] => 
    match n with
    | 0 => idtac
    | 1 => eapply in_app_iff; left
    | S ?n => eapply in_app_iff; right; in_app n
    end
  | [ |- In _ (_ :: _) ] => match n with 0 => idtac | 1 => left | S ?n => right; in_app n end
  end) || (repeat (try right; eapply in_app_iff; right)).

Ltac in_collect a :=
  eapply in_map_iff; exists a; split; [ eauto | match goal with [ |- In _ (filter _ _) ] =>  eapply filter_In; split; [ try (rewrite !in_prod_iff; repeat split) ] | _ => try (rewrite !in_prod_iff; repeat split) end ].

Section Enumerability.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Variable L_Funcs : nat -> list syms.
  Hypothesis enum_Funcs : list_enumerator__T L_Funcs syms.

  Variable L_Preds : nat -> list preds.
  Hypothesis enum_Preds : list_enumerator__T L_Preds preds.

  Variable L_binop : nat -> list binop.
  Hypothesis enum_binop : list_enumerator__T L_binop binop.

  Variable L_quantop : nat -> list quantop.
  Hypothesis enum_quantop : list_enumerator__T L_quantop quantop.

  Fixpoint vecs_from {X} (A : list X) (n : nat) : list (vec X n) :=
    match n with
    | 0 => [Vector.nil X]
    | S n => [ Vector.cons X x _ v | (x, v) ∈ (list_prod A (vecs_from A n)) ]
    end.

  Fixpoint L_nat n : list nat := match n with
    | 0 => [0]
    | S n => S n :: L_nat n
  end.

  Fixpoint L_term n : list term := match n with
    | 0 => []
    | S n => L_term n ++ var_indi n :: 
                   concat [[ func (@var_func _ x ar) v | v ∈ vecs_from (L_term n) ar ] | (x, ar) ∈ (list_prod (L_nat n) (L_nat n)) ]
                ++ concat [[ func (@sym _ f) v | v ∈ vecs_from (L_term n) (ar_syms f) ] | f ∈ L_T n]
  end.

  Fixpoint L_form n : list form := match n with
    | 0 => [fal]
    | S n => L_form n
                ++ concat [[ atom (var_pred x ar) v | v ∈ vecs_from (L_term n) ar ] | (x, ar) ∈ (list_prod (L_nat n) (L_nat n)) ]
                ++ concat [[ atom (pred P) v | v ∈ vecs_from (L_term n) (ar_preds P) ] | P ∈ L_T n]
                ++ concat ([ [ bin op phi psi | (phi, psi) ∈ (list_prod (L_form n) (L_form n)) ] | op ∈ L_T n])
                ++ concat ([ [ quant_indi op phi | phi ∈ L_form n ] | op ∈ L_T n])
                ++ concat ([ [ quant_func op ar phi | phi ∈ L_form n ] | (op, ar) ∈ (list_prod (L_T n) (L_nat n))])
                ++ concat ([ [ quant_pred op ar phi | phi ∈ L_form n ] | (op, ar) ∈ (list_prod (L_T n) (L_nat n))])
  end.

  Lemma L_nat_correct n m :
    m <= n -> m el L_nat n.
  Proof.
    induction n.
    - intros H. left. lia.
    - intros H. cbn. assert (m = S n \/ m <= n) as [] by lia; firstorder.
  Qed.

  Lemma list_prod_in X Y (x : X * Y) A B :
      x el (list_prod A B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
  Proof.
    induction A; cbn.
    - intros [].
    - intros [H | H] % in_app_or. 2: firstorder.
      apply in_map_iff in H as (y & <- & Hel). exists a, y. tauto.
  Qed.

  Lemma vecs_from_correct X (A : list X) (n : nat) (v : vec X n) :
    VectorForall.Forall (fun x => x el A) v <-> v el vecs_from A n.
  Proof.
    induction n; cbn.
    - split.
      + intros. left. pattern v. now apply Vector.case0.
      + now intros [<-|[]].
    - split.
      + intros. revert H. apply (Vector.caseS' v). intros. in_collect (h, t); destruct (IHn t).
        apply H. apply H0. apply H.
      + intros Hv. apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
        split. easy. destruct (IHn v'). now apply H2.
  Qed.

  Lemma vec_forall_cml X (L : nat -> list X) n (v : vec X n) :
    cumulative L -> (VectorForall.Forall (fun x => exists m, x el L m) v) -> exists m, v el vecs_from (L m) n.
  Proof.
    intros HL Hv. induction v; cbn.
    - exists 0. now left.
    - destruct IHv as [m H], Hv as [[m' H'] Hv]. easy.
      exists (m + m'). in_collect (h, v).
      apply (cum_ge' (n:=m')); intuition lia.
      apply vecs_from_correct. rewrite <- vecs_from_correct in H.
      eapply Forall_ext. 2: apply H. cbn.
      intros x Hx. apply (cum_ge' (n:=m)). all: eauto. lia.
  Qed.

  Lemma L_term_cml :
    cumulative L_term.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma enum_term :
    list_enumerator__T L_term term.
  Proof with eapply cum_ge'; eauto; lia.
    intros t. induction t.
    - exists (S n); cbn. apply in_or_app. right. now left.
    - apply vec_forall_cml in IH as [m H]. 2: exact L_term_cml.
      exists (S (m + n + ar)); cbn. in_app 3. eapply in_concat. eexists. split.
      1: in_collect (n, ar). 1,2: apply L_nat_correct; lia.
      in_collect v. rewrite <- vecs_from_correct in H |-*. eapply Forall_ext.
      2: apply H. cbn. intros...
    - apply vec_forall_cml in IH as [m H]. 2: exact L_term_cml.
      destruct (el_T f) as [m' H']. exists (S (m + m')); cbn.
      in_app 4. eapply in_concat. eexists. split. 1: in_collect f...
      in_collect v. rewrite <- vecs_from_correct in H |-*. eapply Forall_ext.
      2: apply H. cbn. intros...
  Qed.

  Lemma enum_form :
    list_enumerator__T L_form form.
  Proof with eapply cum_ge'; eauto; lia.
    intros phi. induction phi.
    - exists 0. now left.
    - rename t into v. destruct (@vec_forall_cml term L_term _ v) as [m H]; eauto.
      + clear p. induction v. easy. split. apply enum_term. apply IHv.
      + destruct p; cbn.
        * exists (S (m + n + ar)); cbn. in_app 2. eapply in_concat.
          eexists. split. 1: in_collect (n, ar). 1,2: apply L_nat_correct; lia.
          in_collect v. rewrite <- vecs_from_correct in H |-*. eapply Forall_ext.
          2: apply H. cbn. intros...
        * destruct (el_T P) as [m']. exists (S (m + m')); cbn. in_app 3.
          eapply in_concat. eexists. split. 1: in_collect P...
          in_collect v. rewrite <- vecs_from_correct in H |-*. eapply Forall_ext.
          2: apply H. cbn. intros...
    - destruct (el_T b) as [m], IHphi1 as [m1], IHphi2 as [m2]. 
      exists (1 + m + m1 + m2); cbn. in_app 4. apply in_concat. eexists. split.
      in_collect b... in_collect (phi1, phi2)...
    - destruct (el_T q) as [m], IHphi as [m']. exists (S (m + m')); cbn. in_app 5.
      apply in_concat. eexists. split. in_collect q... in_collect phi...
    - destruct (el_T q) as [m], IHphi as [m']. exists (S (m + m' + n)); cbn.
      in_app 6. apply in_concat. eexists. split. in_collect (q, n). 
      eapply cum_ge'; eauto; lia. apply L_nat_correct; lia. in_collect phi...
    - destruct (el_T q) as [m], IHphi as [m']. exists (S (m + m' + n)); cbn.
      in_app 7. apply in_concat. eexists. split. in_collect (q, n). 
      eapply cum_ge'; eauto; lia. apply L_nat_correct; lia. in_collect phi...
  Qed.

End Enumerability.

Section Enumerability'.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Hypothesis enumerable_funcs : enumerable__T syms.
  Hypothesis enumerable_preds : enumerable__T preds.
  Hypothesis enumerable_binop : enumerable__T binop.
  Hypothesis enumerable_quantop : enumerable__T quantop.

  Lemma form_enumerable :
    enumerable__T form.
  Proof using enumerable_quantop enumerable_preds enumerable_funcs enumerable_binop.
    apply enum_enumT.
    apply enum_enumT in enumerable_funcs as [Lf HLf].
    apply enum_enumT in enumerable_preds as [Lp HLp].
    apply enum_enumT in enumerable_binop as [Lb HLb].
    apply enum_enumT in enumerable_quantop as [Lq HLq].
    eexists. apply enum_form.
  Qed.

End Enumerability'.
