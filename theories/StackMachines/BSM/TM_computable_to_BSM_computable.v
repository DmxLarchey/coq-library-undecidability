Require Import 
  Undecidability.StackMachines.BSM Undecidability.StackMachines.Util.BSM_computable
  Undecidability.TM.TM Undecidability.TM.Util.TM_facts Undecidability.TM.Util.TM_computable.
From Undecidability.TM Require Import Single.StepTM Code.CodeTM TM mTM_to_TM Arbitrary_to_Binary HaltTM_1_to_HaltSBTM. 
From Undecidability.StackMachines Require Import HaltSBTM_to_HaltBSM.
From Undecidability.Shared.Libs.DLW Require Import vec pos sss subcode.
From Undecidability Require Import bsm_utils bsm_defs.
From Undecidability Require Import BSM_computable_to_MM_computable.

Notation "v @[ t ]" := (Vector.nth v t) (at level 50).

Definition complete_encode (Σ : finType) n (t : Vector.t (tape Σ) n) :=
  (conv_tape [| encode_tape' (Vector.nth (mTM_to_TM.enc_tape [] t) Fin0) |]).

Lemma SBTM_complete_simulation n Σ (M : TM Σ n) :
  {M' : SBTM.SBTM |  
        (forall q t t', TM.eval M (TM.start M) t q t' -> exists q', SBTM.eval M' Fin.F1 (complete_encode t) q' (complete_encode t')) /\
        (forall t, (exists q' t', SBTM.eval M' Fin.F1 (complete_encode t) q' t') -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (TM_sTM_simulation M) as (M1 & Hf1 & Hb1).
  destruct (binary_simulation M1) as (M2 & Hf2 & Hb2).
  destruct (SBTM_simulation M2) as (M3 & Hf3 & Hb3).
  exists M3. split.
  - intros q t t' [q1 [q2 [q3 H] % Hf3] % Hf2] % Hf1. eexists. eapply H.
  - intros t H % Hb3 % Hb2 % Hb1. exact H.
Qed.

Lemma BSM_addstacks n i (P : list (bsm_instr n)) m : 
   {P' | (forall j v o v', BSM.eval n (i, P) (j, v) (o, v') -> forall v'', BSM.eval (m + n) (i, P') (j, Vector.append v'' v) (o, Vector.append v'' v'))
          /\ forall v v'' j out, BSM.eval (m + n) (i, P') (j, Vector.append v'' v) out -> exists out, BSM.eval n (i, P) (j, v) out}.
Proof.
Admitted.  

Lemma BSM_addstacks' n i (P : list (bsm_instr n)) m m' : 
   {P' | length P = length P' /\
   (forall j v o v', BSM.eval n (i, P) (j, v) (o, v') -> forall v'' v''', BSM.eval (m + (m' + n)) (i, P') (j, Vector.append v'' (Vector.append v''' v)) (o, Vector.append v'' (Vector.append v''' v')))
          /\ forall v v'' v''' j out, BSM.eval (m + (m' + n)) (i, P') (j, Vector.append v'' (Vector.append v''' v)) out -> exists out, BSM.eval n (i, P) (j, v) out}.
Proof.
Admitted.  

Definition encode_bsm (Σ : finType) n (t : Vector.t (tape Σ) n) :=
  enc_tape (complete_encode t).
Arguments encode_bsm {_ _} _, _ {_} _.

Lemma encode_bsm_nil (Σ : finType) n   :
  { '( str1, str2, n') | str1 = nil /\ forall (t : Vector.t (tape Σ) n),
      encode_bsm Σ (niltape ::: t) = 
     [| str1 ++ (encode_bsm Σ t)@[Fin0]; (encode_bsm Σ t)@[Fin1]; str2 ++ (skipn n' ((encode_bsm Σ t)@[Fin2])); (encode_bsm Σ t)@[Fin3] |]}.
Proof.
  eexists (_, _, _). split. shelve. cbn. intros t.
  unfold encode_bsm at 1.
  unfold enc_tape at 1. repeat f_equal.
  - unfold complete_encode. unfold conv_tape.
    etransitivity.
    destruct destruct_vector_cons as (? & ? & E). inv E. cbn.
    destruct_tapes. cbn. reflexivity.
    symmetry. etransitivity.
    destruct destruct_vector_cons as (? & ? & E). inv E. cbn.
    destruct_tapes. cbn. reflexivity. instantiate (1 := []). reflexivity.
  - unfold complete_encode, conv_tape.
    etransitivity.
    destruct destruct_vector_cons as (? & ? & E). inv E. cbn.
    destruct_tapes. cbn. reflexivity.
    destruct destruct_vector_cons as (? & ? & E). inv E. cbn. reflexivity.
  - unfold complete_encode, conv_tape.
    etransitivity.
    destruct destruct_vector_cons as (? & ? & E). inv E. cbn - [skipn].
    destruct_tapes. cbn - [skipn]. reflexivity.
    symmetry. etransitivity.
    destruct destruct_vector_cons as (? & ? & E). inv E. cbn - [skipn].
    destruct_tapes. cbn - [skipn]. reflexivity.
    rewrite skipn_app. 2: now rewrite length_encode_sym.
  
    instantiate (1 := encode_sym _ ++ true :: false :: encode_sym _ ++ true :: false :: encode_sym _). cbn.
    rewrite <- app_assoc. cbn. now rewrite <- app_assoc.
    Unshelve. reflexivity.
Qed.

Definition strpush_common_short (Σ : finType) (s b : Σ) :=
encode_sym
  (projT1
     (projT2
        (FinTypeEquiv.finite_n
           (finType_CS (boundary + sigList (EncodeTapes.sigTape Σ)))))
     (inl START)) ++
true
:: false
   :: encode_sym
        (projT1
           (projT2
              (FinTypeEquiv.finite_n
                 (finType_CS (boundary + sigList (EncodeTapes.sigTape Σ)))))
           (inr sigList_cons)) ++
      true
      :: false
         :: encode_sym
              (projT1
                 (projT2
                    (FinTypeEquiv.finite_n
                       (finType_CS
                          (boundary + sigList (EncodeTapes.sigTape Σ)))))
                 (inr (sigList_X (EncodeTapes.LeftBlank false)))) ++
            true
            :: false
               :: encode_sym
                    (projT1
                       (projT2
                          (FinTypeEquiv.finite_n
                             (finType_CS
                                (boundary + sigList (EncodeTapes.sigTape Σ)))))
                       (inr (sigList_X (EncodeTapes.MarkedSymbol b)))).

Definition strpush_common (Σ : finType) (s b : Σ) :=
strpush_common_short s b ++
                  true
                  :: false :: nil.

Definition strpush_zero (Σ : finType) (s b : Σ) :=
  strpush_common s b ++
                      encode_sym
                          (projT1
                             (projT2
                                (FinTypeEquiv.finite_n
                                   (finType_CS
                                      (boundary +
                                       sigList (EncodeTapes.sigTape Σ)))))
                             (inr (sigList_X (EncodeTapes.RightBlank false)))).

Lemma encode_bsm_at0 (Σ : finType) n (t : Vector.t (tape Σ) n) :
   (encode_bsm Σ t) @[Fin0] = [].
Proof.
  unfold encode_bsm, enc_tape, complete_encode, conv_tape.
  destruct destruct_vector_cons as (? & ? & E). inv E. reflexivity.
Qed.

Lemma encode_bsm_at1 (Σ : finType) n :
   forall (t : Vector.t (tape Σ) n), (encode_bsm Σ t) @[Fin1] = [false].
Proof.
  intros t.
  unfold encode_bsm, enc_tape, complete_encode, conv_tape.
  destruct destruct_vector_cons as (? & ? & E). inv E. reflexivity.
Qed.

Lemma encode_bsm_at3 (Σ : finType) n (t : Vector.t (tape Σ) n) :
   (encode_bsm Σ t) @[Fin3] = [].
Proof.
  unfold encode_bsm, enc_tape, complete_encode, conv_tape.
  destruct destruct_vector_cons as (? & ? & E). inv E. reflexivity.
Qed.

Lemma encode_bsm_zero (Σ : finType) s b :
  { n' | forall n(t : Vector.t (tape Σ) n), (encode_bsm Σ (encNatTM s b 0 ::: t)) @[Fin2] = strpush_zero s b ++ (skipn n' ((encode_bsm Σ t)@[Fin2]))}.
Proof.
  eexists _. intros t.
  unfold encode_bsm at 1.
  unfold enc_tape at 1. cbn.
  unfold complete_encode, conv_tape.
  etransitivity.
  destruct destruct_vector_cons as (? & ? & E). inv E. cbn - [skipn].
  destruct_tapes. cbn - [skipn]. reflexivity.
  symmetry. etransitivity.
  destruct destruct_vector_cons as (? & ? & E). inv E. cbn - [skipn].
  destruct_tapes. cbn - [skipn]. reflexivity.
  rewrite skipn_app. 2: now rewrite length_encode_sym. unfold strpush_zero, strpush_common, strpush_common_short.
  rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. reflexivity.
Qed.

Definition strpush_succ (Σ : finType) (s b : Σ) :=
strpush_common s b ++
                     encode_sym
                          (projT1
                             (projT2
                                (FinTypeEquiv.finite_n
                                   (finType_CS
                                      (boundary +
                                       sigList (EncodeTapes.sigTape Σ)))))
                             (inr (sigList_X (EncodeTapes.UnmarkedSymbol s)))).

Lemma encode_bsm_succ (Σ : finType) n m s b (t : Vector.t (tape Σ) n) :
      (encode_bsm Σ (encNatTM s b (S m) ::: t)) @[Fin2] = strpush_succ s b ++ (skipn (length (strpush_common_short s b)) ((encode_bsm Σ (encNatTM s b m ::: t))@[Fin2])).
Proof.
  unfold encode_bsm.
  unfold enc_tape. repeat f_equal.
  unfold complete_encode, conv_tape.
  etransitivity.
  destruct destruct_vector_cons as (? & ? & E). cbn - [skipn]. inv E. cbn - [skipn].
  unfold strpush_common, strpush_common_short.
  destruct_tapes. cbn - [skipn]. reflexivity. 
  unfold strpush_common, strpush_common_short. cbn - [skipn].
  
  symmetry. etransitivity. cbn - [skipn].
  destruct destruct_vector_cons as (? & ? & E). inv E. cbn - [skipn].
  destruct_tapes. cbn - [skipn]. reflexivity. 
  match goal with [|- context [ skipn _ (?x1 ++ true :: false :: ?x2 ++ true :: false :: ?x3 ++ true :: false :: ?x4 ++ ?x5) ]] =>
    replace (x1 ++ true :: false :: x2 ++ true :: false :: x3 ++ true :: false :: x4 ++ x5) with
            ((x1 ++ true :: false :: x2 ++ true :: false :: x3 ++ true :: false :: x4) ++ x5)
  end.    
  rewrite skipn_app. 2:{ reflexivity. }
  2:{ rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. reflexivity. }
  unfold strpush_succ, strpush_common, strpush_common_short.
  rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. reflexivity.
Qed.

Lemma BSM_complete_simulation' n Σ (M : TM Σ n) m m' i :
{ P |
      (forall q t t', TM.eval M (TM.start M) t q t' -> 
       forall v'' v''', BSM.eval (m + (m' + 4)) (i, P) (i, Vector.append v'' (Vector.append v''' (encode_bsm t))) (i + length P, Vector.append v'' (Vector.append v''' (encode_bsm t')))) /\
      (forall t v'' v''', (exists out, BSM.eval (m + (m' + 4)) (i, P) (i, Vector.append v'' (Vector.append v''' (encode_bsm t))) out) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (SBTM_complete_simulation M) as (M1 & Hf1 & Hb1).
  destruct (BSM_addstacks' i (SIM M1 i) m m') as (M2 & Hl & Hf2 & Hb2).
  exists M2. split.
  - intros q t t' [q1 H % (SIM_computes i) ] % Hf1.
    intros. eapply Hf2. eapply BSM_sss.eval_iff. split.
    cbn [Fin.to_nat proj1_sig mult] in H. rewrite !NPeano.Nat.add_0_l, NPeano.Nat.add_0_r in H.
    rewrite <- Hl. rewrite SIM_length. rewrite mult_comm. eapply H.
    right. unfold fst, subcode.code_end, snd, fst. rewrite <- Hl. lia.
  - intros t v'' v''' (out & [[out1 out2] [Ho1 Ho2]% BSM_sss.eval_iff] % Hb2). eapply Hb1.
    eapply SIM_term with (q := Fin.F1) in Ho2 .
    2:{ cbn [Fin.to_nat proj1_sig mult]. rewrite !NPeano.Nat.add_0_l, NPeano.Nat.add_0_r. eapply Ho1. }
    destruct Ho2 as (q' & t' & H1 & -> & H2). eauto.
Qed.  

Lemma BSM_complete_simulation n Σ (M : TM Σ n) m m' i :
{ P |
      (forall q t t', TM.eval M (TM.start M) t q t' -> 
       forall v'' v''', BSM.eval (m + (m' + 4)) (i, P) (i, Vector.append v'' (Vector.append v''' (encode_bsm t))) (i + length P, Vector.append v'' (Vector.append v''' (encode_bsm t')))) /\
      (forall t v'' v''', (sss.sss_terminates (bsm_sss (n := (m + (m' + 4)))) (i, P) (i, Vector.append v'' (Vector.append v''' (encode_bsm t)))) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (@BSM_complete_simulation' n Σ M m m' i) as (P & H1 & H2).
  exists P. split. exact H1.
  intros t v'' v''' ([out1 out2] & H % BSM_sss.eval_iff). eapply H2. eauto.
Qed. 

Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).

Lemma vec_app_spec {X n m} (v : Vector.t X n) (w : Vector.t X m) :
  vec_app v w = Vector.append v w.
Proof.
  induction v.
  - cbn. eapply vec_pos_ext. intros. now rewrite vec_pos_set.
  - rewrite vec_app_cons. cbn. congruence.
Qed.

Lemma pos_right_left {n m} p q :
@pos_left n m p <> @pos_right n m q.
Proof.
induction n; cbn.
- inversion p.
- eapply (Fin.caseS' p).
  + cbn. congruence.
  + cbn. intros ? ? % pos_nxt_inj. firstorder.
Qed.

Lemma pos_left_right {n m} p q :
@pos_right n m q <> @pos_left n m p.
Proof.
induction n; cbn.
- inversion p.
- eapply (Fin.caseS' p).
  + cbn. congruence.
  + cbn. intros ? ? % pos_nxt_inj. firstorder.
Qed.
Hint Immediate pos_left_right pos_right_left : core.

Lemma pos_right_inj {n m} p q :
  @pos_right n m p = @pos_right n m q -> p = q.
Proof.
  induction n in p, q |- *; cbn in *. 
  - eauto.
  - intros. eapply IHn, pos_nxt_inj, H.
Qed.

Lemma vec_pos_const {k} {X x} (p : pos k) : vec_pos (@Vector.const X x k) p = x.
Proof.
  induction p; cbn; eauto.
Qed.

Lemma vec_pos_spec {k} {X} (p : pos k) (v : Vector.t X k) : vec_pos v p = Vector.nth v p.
Proof.
  induction v in p |- *.
  - inversion p.
  - eapply (Fin.caseS' p).
    + reflexivity.
    + intros. cbn. eauto.
Qed.

Lemma Fin4_cases (P : pos 4 -> Prop) :
   P Fin0 -> P Fin1 -> P Fin2 -> P Fin3 -> forall p, P p.
Proof.
  intros H0 H1 H2 H3. 
  repeat (intros p; eapply (Fin.caseS' p); clear p; [ eauto | ]).
  intros p. inversion p.
Qed.

Lemma PREP1_spec k Σ  : 
{ PREP1 : list (bsm_instr ((1 + k) + 4)) | forall v : Vector.t nat k, 
    (0, PREP1) // (0, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) (Vector.const [] 4)) ->>
                  (length PREP1, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) ((@encode_bsm Σ _ (Vector.const niltape 4)))) }.
Proof.
  exists (push_exactly (pos_right (1 + k) Fin0) ((@encode_bsm Σ _ (Vector.const niltape 4))@[Fin0])
       ++ push_exactly (pos_right (1 + k) Fin1) ((@encode_bsm Σ _ (Vector.const niltape 4))@[Fin1])
       ++ push_exactly (pos_right (1 + k) Fin2) ((@encode_bsm Σ _ (Vector.const niltape 4))@[Fin2])
       ++ push_exactly (pos_right (1 + k) Fin3) ((@encode_bsm Σ _ (Vector.const niltape 4))@[Fin3])).
  intros v.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin0) 0 ((@encode_bsm Σ _ (Vector.const niltape 4))@[Fin0])). 1:auto.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin1) _ ((@encode_bsm Σ _ (Vector.const niltape 4))@[Fin1])). 1:auto.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin2) _ ((@encode_bsm Σ _ (Vector.const niltape 4))@[Fin2])). 1:auto.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin3) _ ((@encode_bsm Σ _ (Vector.const niltape 4))@[Fin3])). 1:auto.
  bsm sss stop. f_equal.
  1:rewrite !app_length; lia.
  eapply vec_pos_ext. eapply pos_left_right_rect. 
  - rewrite <- !vec_app_spec. symmetry. rewrite vec_pos_app_left.
    rewrite !vec_change_neq; auto.
    now rewrite vec_pos_app_left.
  - rewrite <- !vec_app_spec. rewrite !vec_pos_app_right. 
    intros p; eapply (Fin.caseS' p); clear p.
    1:{ repeat (rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence]).
        rewrite vec_change_eq; [ | auto]. rewrite vec_pos_app_right.
        now rewrite vec_pos_const, app_nil_r, vec_pos_spec. }
    intros p; eapply (Fin.caseS' p); clear p.
    1:{ rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_eq; [ | auto]. rewrite vec_pos_app_right.
        rewrite vec_pos_const. rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite vec_pos_app_right. now rewrite vec_pos_const, app_nil_r, vec_pos_spec. }
    intros p; eapply (Fin.caseS' p); clear p.
    1:{ rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        rewrite vec_change_eq; [ | auto]. rewrite vec_pos_app_right.
        rewrite vec_pos_const. rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite vec_pos_app_right. now rewrite vec_pos_const, app_nil_r, vec_pos_spec. }
    intros p; eapply (Fin.caseS' p); clear p.
    1:{ rewrite vec_change_eq; [ | auto]. rewrite vec_pos_app_right.
        rewrite vec_pos_const. rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite vec_pos_app_right. now rewrite vec_pos_const, app_nil_r, vec_pos_spec. }
    intros p. inversion p.
Qed.

Lemma vec_map_spec {X Y n} (v : Vector.t X n) (f : X -> Y) :
  vec_map f v = Vector.map f v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma pos_left_inj {n m} p q :
  @pos_left n m p = @pos_left n m q -> p = q.
Proof.
  induction p in q |- *; cbn in *. 
  - eapply (Fin.caseS' q).
    + reflexivity.
    + clear q. cbn. congruence.
  - eapply (Fin.caseS' q).
    + cbn. congruence.
    + clear q. cbn. intros. f_equal. eapply IHp.
      now eapply pos_nxt_inj.
Qed.

Lemma PREP2_spec'' k (Σ : finType) (x : pos k) i s b : 
{ PREP2 : list (bsm_instr ((1 + k) + 4)) | length PREP2 = 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b)) /\
forall v : Vector.t (list bool) k,  forall n, forall t : Vector.t (tape Σ) n, forall m m',
   v @[x] = repeat true m ->
    (i, PREP2) // (i,                Vector.append ([] ::: v) ((@encode_bsm Σ _ (encNatTM s b m' ::: t)))) ->>
                  (i + length PREP2, Vector.append ([] ::: vec_change v x nil) ((@encode_bsm Σ _ (encNatTM s b (m + m') ::: t)))) }.
Proof.
  exists (POP (pos_left 4 (pos_right 1 x)) 0 (i + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b)))
       :: pop_many (pos_right (1 + k) Fin2) (length (strpush_common_short s b)) (1 + i)
       ++ push_exactly (pos_right (1 + k) Fin2) (strpush_succ s b)
       ++ POP (pos_left 4 Fin0) 0 i :: nil). split.
  { cbn. rewrite !app_length. cbn. rewrite pop_many_length, push_exactly_length. lia. }
  intros v n t m m' Hx.
  induction m in v, m', Hx |- *.
  - bsm sss POP empty with (pos_left 4 (pos_right 1 x)) 0 (i + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b))).
    rewrite <- !vec_app_spec, vec_pos_app_left. cbn in *. 
    rewrite vec_pos_spec, Hx. reflexivity.
    bsm sss stop. f_equal. cbn. rewrite !app_length. cbn. rewrite pop_many_length, push_exactly_length. lia. cbn in Hx.
    rewrite <- Hx. now rewrite <- vec_pos_spec, vec_change_same.
  - bsm sss POP 1 with (pos_left 4 (pos_right 1 x)) 0 (i + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b))) (repeat true m).
    1:{ rewrite <- !vec_app_spec, vec_pos_app_left. cbn.
        rewrite vec_pos_spec, Hx. reflexivity. }
    eapply subcode_sss_compute_trans. 2: eapply (pop_many_spec (pos_right (1 + k) Fin2) (length (strpush_common_short s b)) (1 + i)). 1:auto.
    eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin2) _ (strpush_succ s b)).
    { eexists (POP _ _ _ :: pop_many _ _ _), ([POP _ _ _]). split. 
      simpl_list. cbn. simpl_list. reflexivity.
      cbn; rewrite pop_many_length. lia.
    }
    bsm sss POP empty with (pos_left 4 Fin0) 0 i. {
      eexists (POP _ _ _ :: pop_many _ _ _ ++ push_exactly _ _), []. simpl_list. cbn. simpl_list. cbn. split. reflexivity.
      rewrite pop_many_length, push_exactly_length. lia. }
    specialize IHm with (m' := (S m')). replace (S m + m') with (m + S m') by lia.
    match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : Vector.t (list bool) ((1 + k) + 4)); enough (st = ev) as ->; subst ev end.
    match goal with [ |- sss_compute _ _ _ (_, ?st) ] => evar (ev : Vector.t (list bool) ((1 + k) + 4)); enough (st = ev) as ->; subst ev end.
    eapply IHm with (v := vec_change v x (repeat true m)). now rewrite <- vec_pos_spec, vec_change_eq. now rewrite vec_change_idem.
    rewrite <- !vec_app_spec.
    eapply vec_pos_ext. eapply pos_left_right_rect. 
    + symmetry. rewrite vec_pos_app_left.
      rewrite vec_change_neq; auto.
      rewrite vec_change_neq; auto. cbn in p.
      eapply (Fin.caseS' p); clear p. cbn. reflexivity.
      intros p. 
      destruct (pos_eq_dec p x).
      * rewrite vec_change_eq. 2: now subst. cbn. subst. now rewrite vec_change_eq.
      * rewrite vec_change_neq. 2: intros ? % pos_left_inj % pos_nxt_inj; eauto.
        rewrite vec_pos_app_left.  cbn. rewrite vec_change_neq; eauto.
    + intros p. symmetry. rewrite !vec_pos_app_right. symmetry.
      rewrite !vec_change_idem.
      revert p. 
      apply Fin4_cases.
      * repeat (rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence]).
          rewrite vec_change_neq; [ | eapply pos_right_left]. rewrite vec_pos_app_right.
          now rewrite !vec_pos_spec, !encode_bsm_at0.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | auto].
        now rewrite vec_pos_app_right, !vec_pos_spec, !encode_bsm_at1.
      * rewrite vec_change_eq; auto.
        rewrite vec_change_eq; eauto.
        rewrite vec_change_neq; eauto.
        rewrite vec_pos_app_right.
        now rewrite !vec_pos_spec, encode_bsm_succ.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | auto]. 
        now rewrite vec_pos_app_right, !vec_pos_spec, !encode_bsm_at3.
Qed.

Definition PREP2''_length (Σ : finType) (s b : Σ) := proj1_sig (encode_bsm_zero s b) + length (strpush_zero s b) + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b)).

Lemma PREP2_spec' k (Σ : finType) (x : pos k) i s b n : 
{ PREP2 : list (bsm_instr ((1 + k) + 4)) | length PREP2 = PREP2''_length s b  /\
forall v : Vector.t (list bool) k, forall t : Vector.t (tape Σ) n, forall m,
   v @[x] = repeat true m ->
    (i, PREP2) // (i,                Vector.append ([] ::: v) ((@encode_bsm Σ _ t))) ->>
                  (i + length PREP2, Vector.append ([] ::: vec_change v x nil) ((@encode_bsm Σ _ (encNatTM s b m ::: t)))) }.
Proof.
  unfold PREP2''_length. 
  destruct (encode_bsm_zero s b) as [n' Hn'].
  destruct (PREP2_spec'' x (i + n' + length (strpush_zero s b)) s b) as [PREP2 [Hl2 H]].
  exists (pop_many (pos_right (1 + k) Fin2) n' i 
       ++ push_exactly (pos_right (1 + k) Fin2) (strpush_zero s b)
       ++ PREP2). split.
  {  cbn. rewrite !app_length. cbn. rewrite pop_many_length, push_exactly_length. cbn in Hl2. rewrite Hl2. lia. }
  intros v t m Hm.
  eapply subcode_sss_compute_trans. 2: eapply (pop_many_spec (pos_right (1 + k) Fin2) n' i). 1:auto.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin2) _ (strpush_zero s b)). 
  { eexists (pop_many _ _ _), PREP2. split. reflexivity. rewrite pop_many_length. lia. }
  specialize H with (m' := 0) (v := v) (1 := Hm). replace (m + 0) with m in H by lia.
  eapply subcode_sss_compute_trans. 2:{
  match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : Vector.t (list bool) ((1 + k) + 4)); enough (st = ev) as ->; subst ev end.
  match goal with [ |- sss_compute _ _ (?st, _) _ ] => evar (ev : nat); enough (st = ev) as ->; subst ev end.
  - eapply H. 
  - rewrite push_exactly_length. lia.
  - eapply vec_pos_ext. eapply pos_left_right_rect.
    + intros p. rewrite <- !vec_app_spec, !vec_pos_app_left.
      rewrite vec_change_neq; auto.
      rewrite vec_change_neq; auto. now rewrite vec_pos_app_left.
    + rewrite <- !vec_app_spec. eapply Fin4_cases.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite !vec_pos_app_right.
        rewrite !vec_pos_spec. now rewrite !encode_bsm_at0.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        now rewrite !vec_pos_app_right, !vec_pos_spec, !encode_bsm_at1.
      * rewrite vec_change_eq; auto.
        rewrite vec_change_eq; eauto.
        rewrite !vec_pos_app_right.
        now rewrite !vec_pos_spec, Hn'.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        now rewrite !vec_pos_app_right, !vec_pos_spec, !encode_bsm_at3.
  }
  { eexists (pop_many _ _ _ ++ push_exactly _ _), []. rewrite app_nil_r. split. now simpl_list. rewrite app_length, pop_many_length, push_exactly_length. lia. }
  bsm sss stop. f_equal.
  rewrite !app_length, pop_many_length, push_exactly_length. lia.
Qed.

Fixpoint PREP2' (Σ : finType) (s b : Σ) k (k' : nat) (H : k' <= k) (i : nat) : list (bsm_instr ((1 + k) + 4)).
Proof.
  destruct k'.
  - exact List.nil.
  - refine (List.app (PREP2' Σ s b k k' _ i) _). abstract lia.
    assert (Hn : k' < k) by abstract lia.
    refine (proj1_sig (@PREP2_spec' k Σ (Fin.of_nat_lt Hn) (14 * k' + i) s b (k' + 4))).
Defined.

Lemma PREP2'_length (Σ : finType) (s b : Σ) k (k' : nat) (H : k' <= k) (i : nat) :
  | @PREP2' Σ s b k k' H i | = k' * PREP2''_length s b.
Proof.
  induction k' in k, H, i |- *.
  - cbn. reflexivity.
  - cbn - [mult]. destruct PREP2_spec' as (? & ? & ?). cbn. rewrite app_length. cbn in e. rewrite e. cbn in IHk'. rewrite IHk'. lia.
Qed.

Notation "v1 +++ v2" := (Vector.append v1 v2) (at level 60).

Lemma PREP2_spec_strong k (Σ : finType) (x : pos k) i s b k' k'' v (v' : Vector.t nat k') (t : Vector.t (tape Σ) 4) : 
  forall H,
    (i, @PREP2' Σ s b (k'' + k') k'' H  i) //
        (i,                                   ([] ::: Vector.map (fun n => repeat true n) v +++ Vector.const [] k') +++  (@encode_bsm Σ _ (Vector.map (encNatTM s b) v' +++ t))) ->>
        (i + length(@PREP2' Σ s b (k'' + k') k'' H  i), ([] ::: Vector.const [] (k'' + k')                                    +++  (@encode_bsm Σ _ (Vector.map (encNatTM s b) (v +++ v') +++ t)))).
Proof.
  intros H. induction k'' in k', H, v, v', i |- *.
  - cbn. bsm sss stop. f_equal. lia. f_equal. revert v. eapply (Vector.case0). cbn. reflexivity.
  - cbn - [mult]. 
    edestruct (vector_inv_back v) as [(y, vl) Hv]. cbn - [mult].
    eapply subcode_sss_compute_trans with (P := (i, _)). { eexists [], _. cbn - [mult]. split. reflexivity. cbn; now rewrite NPeano.Nat.add_0_r. } 
    { cbn - [mult] in IHk''. specialize (IHk'' i (S k') vl (y ::: v')).
      generalize (@PREP2'_subproof (S (k'' + k')) k'' H).
      replace (S (k'' + k')) with (k'' + S k').
      unshelve epose proof (IHk'' _). astract lia.
      
      match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : vec (list bool) (S (S (k'' + k' + 4)))); enough (st = ev) as ->; subst ev end. eapply IHk''.
      
    specialize IHk'' with (v := vl) (v' := y ::: v').
  

Lemma PREP_spec m k n Σ s b :
  { PREP | forall v : Vector.t nat k,
    BSM.eval ((1 + k) + (m + 4)) (0, PREP) (0, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) (Vector.const [] (m + 4))) 
                                           (length PREP, Vector.append (Vector.const [] (1 + k)) (Vector.append (Vector.const [] m) (@encode_bsm Σ _ (Vector.append (niltape ::: Vector.map (encNatTM s b) v)
                                           (Vector.const niltape n)))))
  }.
Admitted.

Lemma POSTP_spec m' k n (Σ : finType) s b i :
  { POSTP | forall v : Vector.t _ k, forall t : Vector.t (tape Σ) (k + n), forall m,
    BSM.eval ((1 + k) + (m' + 4)) (i, POSTP) (i, Vector.append ([] ## v) (Vector.append (Vector.const [] m') (encode_bsm (encNatTM s b m ## t))))
                                            (i + length POSTP, Vector.append (repeat true m ## v) (Vector.append (Vector.const [] m') (Vector.const [] _) ))
  }.
(* take off strpush_common *)
(* pop unmarked symbol s, if yes increase and repeat *)
(* if no finish *)
Admitted.

Theorem TM_computable_to_BSM_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  TM_computable R -> BSM_computable R.
Proof.
  intros (n & Σ & s & b & Hsb & M & HM1 & HM2) % TM_computable_iff.
  destruct (@PREP_spec 1 k n Σ s b) as [PREP HPREP].
  destruct (BSM_complete_simulation M (1 + k) 1 (length PREP)) as (Mbsm & Hf & Hb).
  destruct (@POSTP_spec 1 k n Σ s b (length (PREP ++ Mbsm))) as [POSTP HPOSTP].
  eapply BSM_computable_iff.
  eexists. exists 0. exists (PREP ++ Mbsm ++ POSTP). split.
  - intros v m (q & t & Heval & Hhd)% HM1. eapply Hf in Heval.
    cbn in t. destruct_tapes. cbn in Hhd. subst.
    eapply BSM_sss.eval_iff in Heval. 
    setoid_rewrite BSM_sss.eval_iff in HPREP.
    setoid_rewrite BSM_sss.eval_iff in HPOSTP.
    setoid_rewrite BSM_sss.eval_iff. fold plus. eexists. eexists.
    split.
    + eapply subcode_sss_compute_trans with (P := (0, PREP)). 1:auto.
      eapply HPREP.
      eapply subcode_sss_compute_trans with (P := (|PREP|, Mbsm)). 1:auto.
      eapply Heval.
      eapply subcode_sss_compute_trans with (P := (|PREP ++ Mbsm|, POSTP)). 1:auto.
      rewrite <- app_length. eapply (HPOSTP (Vector.const [] k)).
      bsm sss stop. reflexivity. 
    + cbn. right. rewrite !app_length. lia.
  - intros. edestruct Hb as (? & ? & HbH). 2:eapply HM2. 2:eapply HbH.
    setoid_rewrite BSM_sss.eval_iff in HPREP.
    eapply subcode_sss_terminates.
    2:{ eapply subcode_sss_terminates_inv. eapply bsm_sss_fun.
        eapply H. 2: eapply HPREP. auto. }
    auto.
Qed.