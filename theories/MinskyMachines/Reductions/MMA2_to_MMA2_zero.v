(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Relations Lia.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

From Undecidability.Shared.Libs.DLW Require Import utils pos vec sss subcode.
From Undecidability.MinskyMachines Require Import MMA.
From Undecidability.MinskyMachines Require MMA_to_MMA_zero.

Set Implicit Arguments.

Theorem MMA2_MMA2_HALTS_ON_ZERO : MMA2_HALTING ⪯ MMA2_HALTS_ON_ZERO.
Proof. apply MMA_to_MMA_zero.reduction. Qed.
