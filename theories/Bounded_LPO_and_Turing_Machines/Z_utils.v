(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From TuringDec Require Import nat_utils.

Import NatUtilsNotations.

Set Implicit Arguments.

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
