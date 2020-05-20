Section impredicate_set_strong_xm_Absurd.

  (** This scripts typechecks with -impredicative-set 

      It does not compile w/o impredicative sets or if Set is replaced with Type 

      It actualizes the script described in the paper 

          "Inconsistency of classical logic in type theory" (H. Geuvers 2001, updated 2007) 

      to recent versions of Coq (should work with Coq 8.* upto 11.*

      Compile it with: coqc -impredicative-set strong_xm_absurd.v
   
     *)

  Implicit Types (P : Prop) (A : Set).
 
  Variable cl : forall P, { P } + { ~ P }.

  Definition P2b (P : Prop) := if cl P then true else false.
  Definition b2P (b : bool) := if b then True else False.

  Lemma p2p P : b2P (P2b P) <-> P.
  Proof.
    unfold b2P, P2b.
    destruct (cl P); tauto.
  Qed.

  Notation p2p_1 := (proj1 (p2p _)).
  Definition retract P : P -> b2P (P2b P) := proj2 (p2p P).
  
  Definition V : Set := forall A, ((A -> bool) -> (A -> bool)) -> A -> bool.

  Definition U : Set := V -> bool.

  Definition sb A : ((A -> bool) -> A -> bool) -> A -> V -> bool := 
    fun r a z => r (z _ r) a.
  
  Notation Sb := (sb _).

  Definition le : (U -> bool) -> U -> bool :=
    fun i x => x (fun _ r a => i (Sb r a)).

  Definition induct : (U -> bool) -> bool :=
    fun i => P2b (forall x : U, (b2P (le i x)) -> (b2P (i x))).

  Definition WF : V -> bool := fun z => induct (z _ le).

  Notation B := False.

  Definition I : U -> bool := 
    fun x => P2b ((forall (i : U -> bool), b2P (le i x) -> b2P (i (Sb le x)) )-> B).

  Lemma omega : forall i, b2P (induct i) -> b2P (i WF).
  Proof.
    intros i y; unfold induct in y.
    generalize (p2p_1 y); intros H.
    apply H, retract.
    intros x H0; apply H, H0.
  Qed.

  Lemma lemma : b2P (induct I).
  Proof.
    unfold induct. 
    apply retract.
    intros x p.
    unfold I; apply retract.
    intros q.
    generalize (q I p); intros H.
    unfold I in H.
    generalize (p2p_1 H); intros H0.
    apply H0.
    intros i.
    apply q.
  Qed.

  Lemma lemma2 : (forall i : U -> bool, b2P (induct i) -> b2P (i WF)) -> B.
  Proof.
    intros x.
    generalize (x I lemma); intros H.
    unfold I, WF in H.
    generalize (p2p_1 H); intros H1.
    apply H1.
    intros i.
    generalize (x (fun y => (i (Sb le y)))).
    intros H0 H3.
    apply H0, H3.
  Qed.

  Lemma absurd : B.
  Proof.
    apply lemma2, omega.
  Qed.

End impredicate_set_strong_xm_Absurd.

Check absurd.
Print Assumptions absurd.
