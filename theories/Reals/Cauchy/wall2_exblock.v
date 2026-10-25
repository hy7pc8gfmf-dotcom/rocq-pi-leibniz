(* ===================================================================== *)
(* Module.  wall2_exblock.v                                              *)
(*                                                                       *)
(* Mission.  Set-carried twin of the cosine root-approximation theorem:  *)
(*   for every positive rational eps there is a rational x in (3/2, 5/3) *)
(*   together with an explicit tail index N such that all partial cosine *)
(*   sums beyond N at x are within eps of zero.  This recasts            *)
(*   [PiCosApproxRoot.v approx_root_cos_prop], whose outer face was      *)
(*   already a [sig] but whose inner existential                      *)
(*   [exists N : nat, ...] was a Prop [ex] and was therefore recorded    *)
(*   as the W-EXBLOCK structural blocker.  The recast replaces the       *)
(*   inner Prop existential by a [sigT] witness: the index is obtained   *)
(*   as data from the Set twin [vt_pow_half_archT], so no large          *)
(*   elimination of Prop is performed anywhere.                          *)
(*                                                                       *)
(* Dependencies.  PiCompareT (QltT/QleT'/NatLe/And), PiKernelSlack       *)
(*   (order bridges, qeqT_imp_qeq, leibsep lipschitz), PiVertexPolyDiff, *)
(*   PiCosTailScan, PiExpTrigSeries, PiExpArch, PiCosApproxRoot (defs    *)
(*   and Prop-face lemmas consumed inside proofs), twin46_b23a           *)
(*   (vt_pow_half_archT, vt_bisect_specT), Stdlib QArith.                *)
(*                                                                       *)
(* References.  PiCosApproxRoot.v approx_root_cos_prop ([:301]);         *)
(*   consumers: the escape-window and zero-sequence convergence lines.   *)
(*                                                                       *)
(* Constructivity.  Statement carried by sigT/And/QltT/NatLe (all Set);  *)
(*   the premise face is [QltT 0 eps].  Proof bodies consume the         *)
(*   constructive stdlib Q-order lemmas (Prop, informative-proof       *)
(*   erasure); the two witness extractions eliminate Set-level [sigT]    *)
(*   and And data only.  No axioms, no Admitted, no solver-closed       *)
(*   goals.                                                              *)
(*                                                                       *)
(* Build.  coqc -Q . "" wall2_exblock.v  (born-in-place, Rocq 9.1)       *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.
Require Import PiCompareT PiKernelSlack PiVertexPolyDiff PiCosTailScan
  PiExpTrigSeries PiExpArch PiCosApproxRoot twin46_b23a.

(* The per-index tail bound, factored out of the main assembly so the
   original proof structure is preserved at a fresh bullet scope.  All
   ingredients are the bisection-context facts established before the
   Set-carried assembly. *)
Lemma approx_root_tailQ : forall (eps : Q) (A N n : nat) (Habq : Qlt (3#2) (5#3)),
  Qle 0 (3#2) -> Qle 0 (5#3) -> Qle (5#3) 2 -> (2 <= A)%nat ->
  (N <= A)%nat ->
  Qle 0 ((3#2) * cos_abs_term (5#3) 1) ->
  Qlt (((3#2) * cos_abs_term (5#3) 1) * q_pow (1#2) N) (eps * (1#2)) ->
  Qlt (((1#6) * leibsep_abssum_cos (5#3) A) * q_pow (1#2) n) (eps * (1#2)) ->
  ((5#3) - (3#2)) * q_pow (1#2) n ==
    snd (vt_bisect A (3#2) (5#3) Habq n) - fst (vt_bisect A (3#2) (5#3) Habq n) ->
  QltT 0 (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))) ->
  QleT' (cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n))) 0 ->
  Qle (3#2) (fst (vt_bisect A (3#2) (5#3) Habq n)) ->
  Qle (snd (vt_bisect A (3#2) (5#3) Habq n)) (5#3) ->
  Qlt (fst (vt_bisect A (3#2) (5#3) Habq n)) (snd (vt_bisect A (3#2) (5#3) Habq n)) ->
  Qle 0 (fst (vt_bisect A (3#2) (5#3) Habq n)) ->
  Qle 0 (snd (vt_bisect A (3#2) (5#3) Habq n)) ->
  Qle (3#2) (vt_mid (fst (vt_bisect A (3#2) (5#3) Habq n))
    (snd (vt_bisect A (3#2) (5#3) Habq n))) ->
  Qle (vt_mid (fst (vt_bisect A (3#2) (5#3) Habq n))
    (snd (vt_bisect A (3#2) (5#3) Habq n))) (5#3) ->
  forall k : nat, (A <= k)%nat ->
  Qlt (Qabs (cos_partial k (vt_mid (fst (vt_bisect A (3#2) (5#3) Habq n))
    (snd (vt_bisect A (3#2) (5#3) Habq n))))) eps.
Proof.
  intros eps A N n Habq H032 H053 H532 HA2 HAGE HD1 Harch1 Harch2
    S3' S4 S5 HSA HSB Habab H0a H0b Hxlole Hxhile k Hk.
  set (x := vt_mid (fst (vt_bisect A (3#2) (5#3) Habq n))
                   (snd (vt_bisect A (3#2) (5#3) Habq n))).
  assert (HabUP := Qlt_le_weak _ _ Habab).
      assert (Hx0 : Qle 0 x)
        by (apply (Qle_trans 0 (3#2) x); [exact H032 | exact Hxlole]).
      assert (Hx2 : Qle x 2)
        by (apply (Qle_trans x (5#3) 2); [exact Hxhile | exact H532]).
      assert (HT := vt_cos_partial_tail_bound_prop x A k Hx0 Hx2 HA2 Hk).
      assert (Hax : Qle (fst (vt_bisect A (3#2) (5#3) Habq n)) x)
        by (apply Qlt_le_weak; apply (vt_mid_gt_l_prop _ _ Habab)).
      assert (Hxb : Qle x (snd (vt_bisect A (3#2) (5#3) Habq n)))
        by (apply Qlt_le_weak; apply (vt_mid_lt_r_prop _ _ Habab)).
      assert (Hxa0 : Qle 0 ((x - fst (vt_bisect A (3#2) (5#3) Habq n)) * (1#2))).
      { apply Qmult_le_0_compat.
        - exact (proj1 (Qle_minus_iff (fst (vt_bisect A (3#2) (5#3) Habq n)) x) Hax).
        - unfold Qle. simpl. lia. }
      assert (Hbx0 : Qle 0 ((snd (vt_bisect A (3#2) (5#3) Habq n) - x) * (1#2))).
      { apply Qmult_le_0_compat.
        - exact (proj1 (Qle_minus_iff x (snd (vt_bisect A (3#2) (5#3) Habq n))) Hxb).
        - unfold Qle. simpl. lia. }
      assert (Hupper : Qle (cos_partial A x)
                   (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n)))).
      { assert (Hdec := vt_cos_decr_half_prop A (fst (vt_bisect A (3#2) (5#3) Habq n)) x
                          HA2 HSA Hax Hxhile).
        apply (Qle_trans _ (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                  - (x - fst (vt_bisect A (3#2) (5#3) Habq n)) * (1#2))).
        - exact Hdec.
        - apply vt_sub_le_r_prop. exact Hxa0. }
      assert (Hlower : Qle (cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n)))
                   (cos_partial A x)).
      { assert (Hdec := vt_cos_decr_half_prop A x (snd (vt_bisect A (3#2) (5#3) Habq n))
                          HA2 Hxlole Hxb HSB).
        apply (Qle_trans _ (cos_partial A x
                  - (snd (vt_bisect A (3#2) (5#3) Habq n) - x) * (1#2))).
        - exact Hdec.
        - apply vt_sub_le_r_prop. exact Hbx0. }
      assert (Hpa4 : Qlt 0 (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))))
        by exact (QltT_to_Qlt _ _ S4).
      assert (Hpb4 : Qle (cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n))) 0)
        by exact (QleT'_to_Qle _ _ S5).
      assert (Hnegb : Qle 0 (- (cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n))))).
      { apply (Qle_trans _ (- 0));
          [unfold Qle; simpl; lia | apply (Qopp_le_compat _ _ Hpb4)]. }
      assert (Hsq : Qle (Qabs (cos_partial A x))
                    (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                  - cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n)))).
      { apply (proj2 (Qabs_Qle_condition (cos_partial A x)
                  (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                - cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n))))). split.
        - assert (Hcomm1 : - (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                     - cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n)))
                   == cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n))
                    - cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))) by ring.
          rewrite Hcomm1.
          apply (Qle_trans _ (cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n)))).
          + apply vt_sub_le_r_prop. apply (Qlt_le_weak 0 _). exact Hpa4.
          + exact Hlower.
        - apply (Qle_trans _ (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n)))).
          + exact Hupper.
          + apply (Qle_trans _ (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                      + - (cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n))))).
            * apply vt_add_le_r_prop. exact Hnegb.
            * apply qeq_le_prop. reflexivity. }
      assert (Hlip : Qle (Qabs (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                              - cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n))))
                         (Qabs (fst (vt_bisect A (3#2) (5#3) Habq n)
                              - snd (vt_bisect A (3#2) (5#3) Habq n))
                       * leibsep_abssum_cos (5#3) A)).
      { apply QleT'_to_Qle.
        apply (leibsep_cos_partial_lipschitz (fst (vt_bisect A (3#2) (5#3) Habq n))
                 (snd (vt_bisect A (3#2) (5#3) Habq n)) (5#3) A).
        - apply Qle_to_QleT'. unfold Qle. simpl. lia.
        - apply Qle_to_QleT'.
          rewrite (Qabs_pos (fst (vt_bisect A (3#2) (5#3) Habq n)) H0a).
          apply (Qle_trans _ (snd (vt_bisect A (3#2) (5#3) Habq n)));
            [exact HabUP | exact HSB].
        - apply Qle_to_QleT'.
          rewrite (Qabs_pos (snd (vt_bisect A (3#2) (5#3) Habq n)) H0b). exact HSB. }
      assert (Hablen : Qabs (fst (vt_bisect A (3#2) (5#3) Habq n)
                           - snd (vt_bisect A (3#2) (5#3) Habq n))
                     == snd (vt_bisect A (3#2) (5#3) Habq n)
                      - fst (vt_bisect A (3#2) (5#3) Habq n)).
      { rewrite (Qabs_Qminus (fst (vt_bisect A (3#2) (5#3) Habq n))
                  (snd (vt_bisect A (3#2) (5#3) Habq n))).
        apply Qabs_pos.
        exact (proj1 (Qle_minus_iff (fst (vt_bisect A (3#2) (5#3) Habq n))
                      (snd (vt_bisect A (3#2) (5#3) Habq n))) HabUP). }
      rewrite Hablen in Hlip.
      assert (Hc16 : ((5#3) - (3#2)) == (1#6)) by (unfold Qeq; simpl; lia).
      assert (Hspanlip2 : Qle (Qabs (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                                  - cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n))))
                         (eps * (1#2))).
      { apply (Qle_trans _ ((snd (vt_bisect A (3#2) (5#3) Habq n)
                  - fst (vt_bisect A (3#2) (5#3) Habq n)) * leibsep_abssum_cos (5#3) A)).
        - exact Hlip.
        - apply (Qle_trans _ (((1#6) * leibsep_abssum_cos (5#3) A) * q_pow (1#2) n)).
          + apply qeq_le_prop. rewrite <- S3'. rewrite Hc16. ring.
          + apply Qlt_le_weak. exact Harch2. }
      assert (Hspansmall : Qle (Qabs (cos_partial A x))
                           (Qabs (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                                - cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n))))).
      { apply (Qle_trans _ (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                  - cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n)))).
        - exact Hsq.
        - apply Qle_Qabs. }
      assert (Hmono53 : Qle (cos_abs_term x (Datatypes.S A))
                            (cos_abs_term (5#3) (Datatypes.S A)))
        by exact (vt_abs_term_mono_x_prop x (5#3) (Datatypes.S A) Hx0 Hxhile).
      assert (HSA1 : Datatypes.S A = (1 + A)%nat) by lia.
      assert (H11 : (1 <= 1)%nat) by lia.
      assert (Hc13 : Qle (q_pow (1#3) A) (q_pow (1#2) A))
        by (apply (vt_q_pow_base_mono_prop (1#3) (1#2) A); unfold Qle; simpl; lia).
      assert (Htaillt : Qlt ((3#2) * cos_abs_term x (Datatypes.S A)) (eps * (1#2))).
      { apply (Qle_lt_trans _ (((3#2) * cos_abs_term (5#3) 1) * q_pow (1#2) N)).
        - apply (Qle_trans _ ((3#2) * cos_abs_term (5#3) (Datatypes.S A))).
          + apply (Qle_trans _ (cos_abs_term x (Datatypes.S A) * (3#2))).
            * apply qeq_le_prop. apply Qmult_comm.
            * apply (Qle_trans _ (cos_abs_term (5#3) (Datatypes.S A) * (3#2))).
              -- exact (Qmult_le_compat_r _ _ _ Hmono53 H032).
              -- apply qeq_le_prop. apply Qmult_comm.
          + apply (Qle_trans _ ((3#2) * (q_pow (1#3) A * cos_abs_term (5#3) 1))).
            * rewrite HSA1.
              apply (Qle_trans _ (cos_abs_term (5#3) (1 + A) * (3#2))).
              -- apply qeq_le_prop. apply Qmult_comm.
              -- apply (Qle_trans _ ((q_pow (1#3) A * cos_abs_term (5#3) 1) * (3#2))).
                 ++ exact (Qmult_le_compat_r _ _ _
                        (vt_abs_term_decay_prop (5#3) 1 A H053 H532 H11) H032).
                 ++ apply qeq_le_prop. apply Qmult_comm.
            * apply (Qle_trans _ (((3#2) * cos_abs_term (5#3) 1) * q_pow (1#3) A)).
              -- apply qeq_le_prop. ring.
              -- apply (Qle_trans _ (((3#2) * cos_abs_term (5#3) 1) * q_pow (1#2) A)).
                 ++ exact (vt_qmult_le_compat_l_prop _ _ _ Hc13 HD1).
                 ++ exact (vt_qmult_le_compat_l_prop _ _ _
                           (vt_q_pow_half_mono_prop N A HAGE) HD1).
        - exact Harch1. }
      assert (Hdc := proj1 (Qabs_Qle_condition (cos_partial k x - cos_partial A x)
                  (Qabs (cos_partial k x - cos_partial A x))) (Qle_refl _)).
      destruct Hdc as [Hdc1 Hdc2].
      assert (Hxc := proj1 (Qabs_Qle_condition (cos_partial A x)
                  (Qabs (cos_partial A x))) (Qle_refl _)).
      destruct Hxc as [Hxc1 Hxc2].
      assert (Hsid : cos_partial k x
                   == cos_partial k x - cos_partial A x + cos_partial A x) by ring.
      assert (Hsid' : cos_partial k x - cos_partial A x + cos_partial A x
                    == cos_partial k x) by ring.
      assert (Htri : Qle (Qabs (cos_partial k x))
                     (Qabs (cos_partial k x - cos_partial A x)
                      + Qabs (cos_partial A x))).
      { apply (proj2 (Qabs_Qle_condition (cos_partial k x)
                  (Qabs (cos_partial k x - cos_partial A x)
                   + Qabs (cos_partial A x)))). split.
        - apply (Qle_trans _ (-(Qabs (cos_partial k x - cos_partial A x))
                  + - (Qabs (cos_partial A x)))).
          + apply qeq_le_prop. ring.
          + apply (Qle_trans _ (cos_partial k x - cos_partial A x
                      + cos_partial A x)).
            * apply (Qplus_le_compat _ _ _ _ Hdc1 Hxc1).
            * apply qeq_le_prop. exact Hsid'.
        - apply (Qle_trans _ (cos_partial k x - cos_partial A x
                    + cos_partial A x)).
          + apply qeq_le_prop. exact Hsid.
          + apply (Qplus_le_compat _ _ _ _ Hdc2 Hxc2). }
      assert (Hepsadd : eps * (1#2) + eps * (1#2) == eps) by ring.
      apply (Qle_lt_trans (Qabs (cos_partial k x))
               ((3#2) * cos_abs_term x (Datatypes.S A)
                  + Qabs (cos_partial A (fst (vt_bisect A (3#2) (5#3) Habq n))
                        - cos_partial A (snd (vt_bisect A (3#2) (5#3) Habq n)))) eps).
      - apply (Qle_trans _ (Qabs (cos_partial k x - cos_partial A x)
                  + Qabs (cos_partial A x))).
        + exact Htri.
        + apply (Qplus_le_compat _ _ _ _ HT Hspansmall).
      - rewrite <- Hepsadd. apply (Qplus_lt_le_compat _ _ _ _ Htaillt Hspanlip2).
Qed.

Lemma approx_root_cosT : forall eps : Q, QltT 0 eps ->
  sigT (fun x : Q => sigT (fun N : nat =>
    And (QltT (3#2) x)
    (And (QltT x (5#3))
         (forall k : nat, NatLe N k -> QltT (Qabs (cos_partial k x)) eps)))).
Proof.
  intros eps HE.
  assert (HE' : Qlt 0 eps) by (apply QltT_to_Qlt; exact HE).
  assert (Heps2 : Qlt 0 (eps * (1#2)))
    by (apply (Qmult_lt_0_compat eps (1#2));
        [exact HE' | unfold Qlt; simpl; reflexivity]).
  assert (Heps2T : QltT 0 (eps * (1#2))) by (apply Qlt_to_QltT; exact Heps2).
  assert (H032 : Qle 0 (3#2)) by (unfold Qle; simpl; lia).
  assert (H532 : Qle (5#3) 2) by (unfold Qle; simpl; lia).
  assert (H053 : Qle 0 (5#3)) by (unfold Qle; simpl; lia).
  assert (HD1 : Qle 0 ((3#2) * cos_abs_term (5#3) 1))
    by (apply Qmult_le_0_compat;
        [unfold Qle; simpl; lia | apply (vt_abs_term_nonneg_prop (5#3) 1 H053)]).
  assert (HD1T : QleT' 0 ((3#2) * cos_abs_term (5#3) 1))
    by (apply Qle_to_QleT'; exact HD1).
  (* The two witness indices are extracted from the Set twins, never
     from a Prop existential. *)
  destruct (vt_pow_half_archT ((3#2) * cos_abs_term (5#3) 1) (eps * (1#2))
              HD1T Heps2T) as [N Harch1T].
  assert (Harch1 : Qlt (((3#2) * cos_abs_term (5#3) 1) * q_pow (1#2) N)
                       (eps * (1#2)))
    by (apply QltT_to_Qlt; exact Harch1T).
  assert (HAN5 : (5 <= N + 5)%nat) by lia.
  assert (HAGE : (N <= N + 5)%nat) by lia.
  assert (HA2 : (2 <= N + 5)%nat) by lia.
  assert (Hleib0 : Qle 0 (leibsep_abssum_cos (5#3) (N + 5)))
    by (apply vt_leibsep35_pos_prop).
  assert (HD2 : Qle 0 ((1#6) * leibsep_abssum_cos (5#3) (N + 5)))
    by (apply Qmult_le_0_compat; [unfold Qle; simpl; lia | exact Hleib0]).
  assert (HD2T : QleT' 0 ((1#6) * leibsep_abssum_cos (5#3) (N + 5)))
    by (apply Qle_to_QleT'; exact HD2).
  destruct (vt_pow_half_archT ((1#6) * leibsep_abssum_cos (5#3) (N + 5))
              (eps * (1#2)) HD2T Heps2T) as [n Harch2T].
  assert (Harch2 : Qlt (((1#6) * leibsep_abssum_cos (5#3) (N + 5)) * q_pow (1#2) n)
                       (eps * (1#2)))
    by (apply QltT_to_Qlt; exact Harch2T).
  set (A := (N + 5)%nat).
  assert (Hab35 : Qlt (3#2) (5#3)) by (compute; reflexivity).
  assert (Hpa : QltT 0 (cos_partial A (3#2)))
    by (apply Qlt_to_QltT; apply vt_three_halves_pos_prop; exact HAN5).
  assert (Hpb : QleT' (cos_partial A (5#3)) 0)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply vt_five_thirds_neg_prop;
        exact HAN5).
  assert (H032T : QleT' 0 (3#2)) by (apply Qle_to_QleT'; exact H032).
  assert (H532T : QleT' (5#3) 2) by (apply Qle_to_QleT'; exact H532).
  assert (HA2Nat : NatLe 2 A) by (apply NatLe_lift; exact HA2).
  assert (Hab35T : QltT (3#2) (5#3)) by (apply Qlt_to_QltT; exact Hab35).
  destruct (vt_bisect_specT n A (3#2) (5#3) Hab35T H032T H532T HA2Nat Hpa Hpb)
    as [S1 [S2 [S3 [S4 S5]]]].
  set (Habq := QltT_to_Qlt (3#2) (5#3) Hab35T) in *.
  assert (S3' : ((5#3) - (3#2)) * q_pow (1#2) n
              == snd (vt_bisect A (3#2) (5#3) Habq n)
               - fst (vt_bisect A (3#2) (5#3) Habq n))
    by (apply qeqT_imp_qeq; exact S3).
  assert (HSA : Qle (3#2) (fst (vt_bisect A (3#2) (5#3) Habq n)))
    by (apply QleT'_to_Qle; exact S1).
  assert (HSB : Qle (snd (vt_bisect A (3#2) (5#3) Habq n)) (5#3))
    by (apply QleT'_to_Qle; exact S2).
  assert (Hlen0 : Qlt 0 (((5#3) - (3#2)) * q_pow (1#2) n))
    by (apply (Qmult_lt_0_compat ((5#3) - (3#2)) (q_pow (1#2) n));
        [unfold Qlt; simpl; lia | apply vt_pos_half_pow_prop]).
  assert (Habab : Qlt (fst (vt_bisect A (3#2) (5#3) Habq n))
                      (snd (vt_bisect A (3#2) (5#3) Habq n))).
  { apply (proj2 (Qlt_minus_iff (fst (vt_bisect A (3#2) (5#3) Habq n))
                  (snd (vt_bisect A (3#2) (5#3) Habq n)))).
    change (Qlt 0 (snd (vt_bisect A (3#2) (5#3) Habq n)
                 - fst (vt_bisect A (3#2) (5#3) Habq n))).
    rewrite <- S3'. exact Hlen0. }
  assert (HabUP : Qle (fst (vt_bisect A (3#2) (5#3) Habq n))
                      (snd (vt_bisect A (3#2) (5#3) Habq n)))
    by (apply Qlt_le_weak; exact Habab).
  assert (H0a : Qle 0 (fst (vt_bisect A (3#2) (5#3) Habq n)))
    by (apply (Qle_trans 0 (3#2) (fst (vt_bisect A (3#2) (5#3) Habq n)));
        [exact H032 | exact HSA]).
  assert (H0b : Qle 0 (snd (vt_bisect A (3#2) (5#3) Habq n)))
    by (apply (Qle_trans 0 (fst (vt_bisect A (3#2) (5#3) Habq n))
                  (snd (vt_bisect A (3#2) (5#3) Habq n)));
        [exact H0a | exact HabUP]).
  set (x := vt_mid (fst (vt_bisect A (3#2) (5#3) Habq n))
                   (snd (vt_bisect A (3#2) (5#3) Habq n))).
  assert (Hxlo : Qlt (3#2) x).
  { apply (Qle_lt_trans (3#2) (fst (vt_bisect A (3#2) (5#3) Habq n)) x).
    - exact HSA.
    - apply (vt_mid_gt_l_prop _ _ Habab). }
  assert (Hxhi : Qlt x (5#3)).
  { apply (Qlt_le_trans x (snd (vt_bisect A (3#2) (5#3) Habq n)) (5#3)).
    - apply (vt_mid_lt_r_prop _ _ Habab).
    - exact HSB. }
  assert (Hxlole : Qle (3#2) x) by (apply Qlt_le_weak; exact Hxlo).
  assert (Hxhile : Qle x (5#3)) by (apply Qlt_le_weak; exact Hxhi).
  (* Assemble the Set-carried conclusion: the mid-point witness, its
     strict order faces, and the explicit tail index with the per-index
     QltT bound. *)
  exists x. exists A. split.
  - apply Qlt_to_QltT. exact Hxlo.
  - split.
    + apply Qlt_to_QltT. exact Hxhi.
    + intros k Hk.
      apply NatLe_drop in Hk.
      assert (Harch2A : Qlt (((1#6) * leibsep_abssum_cos (5#3) A) * q_pow (1#2) n)
                         (eps * (1#2))) by exact Harch2.
      assert (HAGEA : (N <= A)%nat) by exact HAGE.
      apply Qlt_to_QltT.
      apply (approx_root_tailQ eps A N n Habq H032 H053 H532 HA2 HAGEA HD1
               Harch1 Harch2A S3' S4 S5 HSA HSB Habab H0a H0b Hxlole Hxhile
               k Hk).
Qed.

Print Assumptions approx_root_tailQ.
Print Assumptions approx_root_cosT.
