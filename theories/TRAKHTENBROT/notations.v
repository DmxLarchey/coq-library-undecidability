(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Set Implicit Arguments.

Definition discrete X := forall x y : X, { x = y } + { x <> y }.

(** Lifting a DeBruijn subtitution with
    a non-recursive fixpoint definition to get correct unfolding *)

Reserved Notation "phi ↑ k" (at level 1, format "phi ↑ k", left associativity).

Fixpoint env_lift {X} (φ : nat -> X) k n { struct n } :=
  match n with
    | 0   => k
    | S n => φ n
  end.

Notation "phi ↑ k" := (env_lift phi k).

(* Unicode DB for cut/paste 
  -> ⇡ ↑ 
  -> ⟬  ⟭ ⟦ ⟧ ⟪ ⟫ ⦃ ⦄
  -> φ ψ σ ρ 𝕋 𝔽 
  -> ⌞ ⌟ ∅ ⪧ ≈ ≉ ∈ ∉ ≾ ≺ ε ∙ ∊ ⋷
  -> ∑ ∏
*)

Notation "x '≋' y" := (prod (x->y) (y->x)) 
   (at level 95, no associativity,
    format "x  '≋'  y") : type_scope.

Notation "'∀' x .. y , p" := (forall x , .. (forall y , p) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' '∀'  x  ..  y ,  '/ ' p ']'", only printing)
  : type_scope.

Notation "'∃' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity,
   format "'[' '∃'  x  ..  y ,  '/ ' p ']'", only printing)
  : type_scope.

Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity,
   format "'[' '∑'  x  ..  y ,  '/ ' p ']'", only printing)
  : type_scope.

Notation "'∑' x .. y z , p" := (sigT (fun x => .. (sigT (fun y => sig (fun z => p))) ..))
  (at level 200, x binder, y binder, right associativity,
   format "'[' '∑'  x  ..  y  z ,  '/ ' p ']'", only printing)
  : type_scope.

(** Lifting a term substitution *)
Reserved Notation "⇡ sig" (at level 1, format "⇡ sig").

(** Term substitution and semantics *)
Reserved Notation "t '⟬' σ '⟭'" (at level 1, format "t ⟬ σ ⟭").
Reserved Notation "'⟦' t '⟧'" (at level 1, format "⟦ t ⟧").

(** Formula subsitution and semantics*)
Reserved Notation "f '⦃' σ '⦄'" (at level 1, format "f ⦃ σ ⦄").
Reserved Notation "'⟪' f '⟫'" (at level 1, format "⟪ f ⟫").

(* Unary ops *)

Reserved Notation "⌞ x ⌟" (at level 1, format "⌞ x ⌟").
Reserved Notation "↓ x"   (at level 1, format "↓ x").
Reserved Notation "x †"   (at level 1, format "x †").

(* Infix Binary ops *)
 
Reserved Notation "x ∙ y"  (at level 2, right associativity, format "x ∙ y").
Reserved Notation "x ⪧ y" (at level 2, right associativity, format "x ⪧ y").
Reserved Notation "x → y" (at level 2, right associativity, format "x → y").

Reserved Notation "⟬ s , t ⟭" (at level 1, format "⟬ s , t ⟭").
Reserved Notation "x ∪ y" (at level 52, left associativity).

  (* Infix Binary rels *)

Reserved Notation "x ∈ y" (at level 59, no associativity).
Reserved Notation "x ∉ y" (at level 70, no associativity).
Reserved Notation "x ≈ y" (at level 59, no associativity).
Reserved Notation "x ≉ y" (at level 59, no associativity). 
Reserved Notation "x ⊆ y" (at level 59, no associativity). 

Reserved Notation "x ≾ y" (at level 70, no associativity). 

(* Reserved Notation "x ≺ y" (at level 70, no associativity). *)
(* Reserved Notation "x ⊆ y" (at level 70, no associativity). *)



