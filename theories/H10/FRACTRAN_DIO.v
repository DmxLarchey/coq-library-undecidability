(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** FRACTRAN reduces to Diophantine logic *)

Require Import List Arith Omega.

From Undecidability Require Import ILL.Definitions.

From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.H10.Fractran Require Import fractran_defs fractran_dio.
From Undecidability.H10.Dio Require Import dio_elem dio_single dio_logic.
From Undecidability.H10 Require Import MM_FRACTRAN.

Set Implicit Arguments.

Fact reduction_dependent X Y (P : X -> Prop) (Q : Y -> Prop) :
        P ⪯ Q <-> inhabited (forall x, { y | P x <-> Q y }).
Proof.
  split.
  + intros (f & Hf); exists.
    intros x; exists (f x); auto.
  + intros [f].
    exists (fun x => proj1_sig (f x)).
    intros x; apply (proj2_sig (f x)).
Qed.

(** A diophantine logic satisfiability question is given
    a diophantine logic formula f and a valuation for the
    parameters. Is the formula valid ? *)

Definition DIO_LOGIC_PROBLEM := 
  (dio_formula * (nat -> nat))%type.

Definition DIO_LOGIC_SAT (p : DIO_LOGIC_PROBLEM) :=
  let (f,ν) := p in df_pred f ν. 

Theorem FRACTRAN_HALTING_DIO_LOGIC_SAT : FRACTRAN_HALTING ⪯ DIO_LOGIC_SAT.
Proof.
  apply reduction_dependent; exists.
  intros (l & x).
  destruct FRACTRAN_HALTING_on_diophantine 
    with (ll := l) (x := fun _ : nat -> nat => x) as (f & Hf); simpl.
  + dio_rel_auto.
  + exists (f, fun _ => x); unfold DIO_LOGIC_SAT; rewrite Hf; tauto.
Qed.

(** An elementary diophantine problem is a list of elementary diophantine
    constraints and a valuation for the parameters. The question is whether
    there exists a valuation for the variables that satisfies all the constraints
    simultaneously *)

Definition DIO_ELEM_PROBLEM := 
  (list dio_constraint * (nat -> nat))%type.

Definition DIO_ELEM_SAT (p : DIO_ELEM_PROBLEM) :=
  let (l,v) := p in exists φ, Forall (dc_eval φ v) l.

Theorem DIO_LOGIC_ELEM_SAT : DIO_LOGIC_SAT ⪯  DIO_ELEM_SAT.
Proof.
  apply reduction_dependent; exists.
  intros (A,v).
  destruct (dio_formula_elem A) as (l & _ & _ & Hl).
  exists (l,v); apply Hl.
Qed.

Definition DIO_SINGLE_PROBLEM := 
  (dio_single nat nat * (nat -> nat))%type.

Definition DIO_SINGLE_SAT (p : DIO_SINGLE_PROBLEM) :=
  let (E,φ) := p in dio_single_pred E φ.

Theorem DIO_ELEM_SINGLE_SAT : DIO_ELEM_SAT ⪯ DIO_SINGLE_SAT.
Proof.
  apply reduction_dependent; exists.
  intros (l,v).
  destruct (dio_elem_equation l) as (E & _ & HE).
  exists (E,v).
  unfold DIO_ELEM_SAT, DIO_SINGLE_SAT.
  rewrite <- HE; tauto.
Qed.


