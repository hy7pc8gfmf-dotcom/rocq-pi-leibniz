(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Bounds, inverse bounds, and the Cauchy property of the cosine
    zero sequence

    Mission.  Nine statements about the cosine zero sequence
    [cos_zero_seq]: the five interval and magnitude bounds (lower
    bound, upper bound, nonnegativity, bound by two, absolute-value
    bound); the three inverse bounds (the pointwise root bound, and
    the inverse bound in pointwise form and in distance form); and the
    Cauchy property of the sequence.  The n-th term of the zero
    sequence is taken from [PiCosZeroSeqProbe.cos_zero_seq] (the
    localization point with tolerance [eps_n = (1/2)^(n+1)]); the root
    localization is supplied by [PiCosApproxRoot.approx_root_cos_prop]; the
    [log_eps] lemma family is supplied by [QCauchyZeroCos]; the
    term-wise difference bound is supplied by
    [PiVertexPolyDiff.sc_cos_partial_diff_leT].

    Dependencies.  Stdlib [QArith] ([QArith]/[Qabs]/[Qfield]);
    [PiKernelSlack] ([q_pow]/[cos_partial] and the bridge lemmas);
    [QCauchyZeroCos]; [PiCosTailScan]; [PiVertexPolyDiff];
    [PiCosApproxRoot]; [PiCosZeroSeqProbe].

    References.  [S10_KVQuantTrig.v :8123/:8131/:8139/:8146/:8413]
    ([cos_zero_lowerT]/[cos_zero_upperT]/[cos_zero_nonnegT]/
    [cos_zero_le_twoT]/[cos_zero_abs_le_twoT]), [:8156/:8184/:8243]
    ([cos_root_pt_bound_prop]/[cos_inv_pt_prop]/[cos_inv_distT]), and [:8296]
    ([cos_seq_cauchy_prop]): the [Q]-level restatements.

    Constructivity.  Statements carried at the [Set] level ([sig]
    witnesses, [Q] values); within proofs the constructive stdlib
    [Qlt]/[Qle]/[Qeq] predicates are used; assumption-free and fully
    proved, with no non-constructive principles (the closing
    [Print Assumptions] lines all report closed).

    Build.  [rocq c -native-compiler no -q -Q . ""
    PiCosZeroSeqConv.v]; the first eight bytes of the artifact are
    [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid Morphisms.
Require Import PiKernelSlack.
Require Import PiCompareT.
Require Import QCauchyZeroCos.
Require Import PiCosTailScan.
Require Import PiVertexPolyDiff.
Require Import PiCosApproxRoot.
Require Import PiCosZeroSeqProbe.

(* ============================================================ *)
(* Section 1. Interval bounds of the zero sequence *)
(* ============================================================ *)

(* Lower bound: [z_n > 3/2] (first component of the [approx_root_cos_prop]
   witness). *)
Lemma cos_zero_lower_prop : forall n : nat, Qlt (3#2)%Q (cos_zero_seq n).
Proof.
  intros n.
  unfold cos_zero_seq.
  destruct (approx_root_cos_prop (log_eps n) (log_eps_pos_prop n)) as [x [Hlo [Hhi HN]]].
  exact Hlo.
Qed.

(* Upper bound: [z_n < 5/3] (second component of the [approx_root_cos_prop]
   witness). *)
Lemma cos_zero_upper_prop : forall n : nat, Qlt (cos_zero_seq n) (5#3)%Q.
Proof.
  intros n.
  unfold cos_zero_seq.
  destruct (approx_root_cos_prop (log_eps n) (log_eps_pos_prop n)) as [x [Hlo [Hhi HN]]].
  exact Hhi.
Qed.

(* Nonnegativity: [0 <= z_n] (transitivity through [0 < 3/2] and the
   lower bound). *)
(* Set twin of cos_zero_lowerT *)
Lemma cos_zero_lowerT : forall n : nat, QltT (3#2)%Q (cos_zero_seq n).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (cos_zero_lower_prop n).
  all: first [ apply QltT_to_Qlt; assumption
            | apply QleT'_to_Qle; assumption
            | apply qeqT_imp_qeq; assumption
            | apply NatLe_drop; assumption
            | (intros; apply QltT_to_Qlt; assumption)
            | (intros; apply QleT'_to_Qle; assumption)
            | (intros; apply qeqT_imp_qeq; assumption)
            | (intros; apply NatLe_drop; assumption)
            | assumption ].
Qed.

Lemma cos_zero_nonneg_prop : forall n : nat, Qle 0 (cos_zero_seq n).
Proof.
  intros n.
  apply (Qlt_le_weak 0 (cos_zero_seq n)).
  apply (Qlt_trans 0 (3#2)%Q).
  - change (Qlt 0 (3#2)%Q). unfold Qlt. simpl. lia.
  - apply QltT_to_Qlt. apply cos_zero_lowerT.
Qed.

(* Second upper bound: [z_n <= 2] (transitivity through the upper
   bound [5/3 < 2]). *)
(* Set twin of cos_zero_upperT *)
Lemma cos_zero_upperT : forall n : nat, QltT (cos_zero_seq n) (5#3)%Q.
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (cos_zero_upper_prop n).
  all: first [ apply QltT_to_Qlt; assumption
            | apply QleT'_to_Qle; assumption
            | apply qeqT_imp_qeq; assumption
            | apply NatLe_drop; assumption
            | (intros; apply QltT_to_Qlt; assumption)
            | (intros; apply QleT'_to_Qle; assumption)
            | (intros; apply qeqT_imp_qeq; assumption)
            | (intros; apply NatLe_drop; assumption)
            | assumption ].
Qed.

Lemma cos_zero_le_two_prop : forall n : nat, Qle (cos_zero_seq n) 2.
Proof.
  intros n.
  apply (Qlt_le_weak (cos_zero_seq n) 2).
  apply (Qlt_trans (cos_zero_seq n) (5#3)%Q).
  - apply QltT_to_Qlt. apply cos_zero_upperT.
  - change (Qlt (5#3)%Q 2). unfold Qlt. simpl. lia.
Qed.

(* Absolute-value bound: [|z_n| <= 2] (composed from
   [Qabs_Qle_condition] and the previous two statements). *)
(* Set twin of cos_zero_nonnegT *)
Lemma cos_zero_nonnegT : forall n : nat, QleT' 0 (cos_zero_seq n).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (cos_zero_nonneg_prop n).
  all: first [ apply QltT_to_Qlt; assumption
            | apply QleT'_to_Qle; assumption
            | apply qeqT_imp_qeq; assumption
            | apply NatLe_drop; assumption
            | (intros; apply QltT_to_Qlt; assumption)
            | (intros; apply QleT'_to_Qle; assumption)
            | (intros; apply qeqT_imp_qeq; assumption)
            | (intros; apply NatLe_drop; assumption)
            | assumption ].
Qed.

(* Set twin of cos_zero_le_twoT *)
Lemma cos_zero_le_twoT : forall n : nat, QleT' (cos_zero_seq n) 2.
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (cos_zero_le_two_prop n).
  all: first [ apply QltT_to_Qlt; assumption
            | apply QleT'_to_Qle; assumption
            | apply qeqT_imp_qeq; assumption
            | apply NatLe_drop; assumption
            | (intros; apply QltT_to_Qlt; assumption)
            | (intros; apply QleT'_to_Qle; assumption)
            | (intros; apply qeqT_imp_qeq; assumption)
            | (intros; apply NatLe_drop; assumption)
            | assumption ].
Qed.

Lemma cos_zero_abs_le_two_prop : forall n : nat, Qle (Qabs (cos_zero_seq n)) 2.
Proof.
  intros n.
  apply (proj2 (Qabs_Qle_condition (cos_zero_seq n) 2)).
  split.
  - apply (Qle_trans _ 0 _).
    + change (Qle (- 2) 0). unfold Qle. simpl. lia.
    + apply QleT'_to_Qle. apply cos_zero_nonnegT.
  - apply QleT'_to_Qle. apply cos_zero_le_twoT.
Qed.

(* ============================================================ *)
(* Section 2. Pointwise root bound and inverse bounds *)
(* ============================================================ *)

(* Pointwise root bound: [|cos_k(z_n)| < eps_n] for [k] large enough
   (supplied directly by the third component of [approx_root_cos_prop]; a
   strengthened [Q]-level form with all five [Real]-layer bridges
   removed).  The existence witness is carried by [exists]: the
   upstream third component of [approx_root_cos_prop] is itself the
   [exists] form, this form is verbatim same-shaped with it, and its
   consumption sites (the pairing orders of the Cauchy statement)
   eliminate it at [exists] goals, with no [Set] elimination. *)
Lemma cos_root_pt_bound_prop : forall n : nat,
  exists N : nat, forall k : nat, (N <= k)%nat ->
    Qlt (Qabs (cos_partial k (cos_zero_seq n))) (log_eps n).
Proof.
  intros n.
  unfold cos_zero_seq.
  destruct (approx_root_cos_prop (log_eps n) (log_eps_pos_prop n)) as [x [Hlo [Hhi HN]]].
  destruct HN as [N HN].
  exists N.
  exact HN.
Qed.

(* Inverse bound (pointwise form): [k >= 2], [0 <= u <= v <= 2],
   [|cos_k(u)| < du], [|cos_k(v)| < dv] imply
   [(v^2 - u^2)/6 < du + dv].  Main chain: [sc_cos_partial_diff_leT]
   gives [cos_k(v) <= cos_k(u) - (v^2-u^2)/6], while
   [cos_k(u) - cos_k(v) <= |cos_k(u)| + |cos_k(v)| < du + dv]. *)
Lemma cos_inv_pt_prop : forall (u v : Q) (k : nat) (du dv : Q),
  (2 <= k)%nat -> Qle 0 u -> Qle u v -> Qle v 2 ->
  Qlt (Qabs (cos_partial k u)) du ->
  Qlt (Qabs (cos_partial k v)) dv ->
  Qlt ((v * v - u * u) * (1 / 6)) (du + dv).
Proof.
  intros u v k du dv Hk Hu0 Huv Hv2 Hdu Hdv.
  assert (Hmain : Qle (cos_partial k v)
                      (cos_partial k u - (v * v - u * u) * (1 / 6))).
  { apply (sc_cos_partial_diff_le_prop k u v Hu0 Huv Hv2 Hk). }
(* [(v^2-u^2)/6 <= cos_k(u) - cos_k(v)]. *)
  assert (Hd : Qle ((v * v - u * u) * (1 / 6))
                   (cos_partial k u - cos_partial k v)).
  { apply (proj2 (Qle_minus_iff ((v * v - u * u) * (1 / 6))
                                (cos_partial k u - cos_partial k v))).
    assert (Hr : (cos_partial k u - cos_partial k v) - (v * v - u * u) * (1 / 6) ==
                 (cos_partial k u - (v * v - u * u) * (1 / 6)) - cos_partial k v) by ring.
    rewrite Hr.
    apply (proj1 (Qle_minus_iff (cos_partial k v)
                                (cos_partial k u - (v * v - u * u) * (1 / 6)))).
    exact Hmain. }
(* [cos_k(u) - cos_k(v) <= |cos_k(u)| + |cos_k(v)| < du + dv]. *)
  assert (Htri : Qle (Qabs (cos_partial k u - cos_partial k v))
                     (Qabs (cos_partial k u) + Qabs (cos_partial k v))).
  { apply (Qle_trans _ (Qabs (cos_partial k u + - cos_partial k v)) _).
    - apply QleT'_to_Qle. apply qeq_leT'. apply Qabs_wd. ring.
    - apply (Qle_trans _ (Qabs (cos_partial k u) + Qabs (- cos_partial k v)) _).
      + apply Qabs_triangle.
      + apply QleT'_to_Qle. apply qeq_leT'.
        assert (Hn1 : - cos_partial k v == 0 - cos_partial k v) by ring.
        rewrite (Qabs_wd _ _ Hn1).
        rewrite (Qabs_Qminus 0%Q (cos_partial k v)).
        assert (Hz0 : cos_partial k v - 0 == cos_partial k v) by ring.
        rewrite (Qabs_wd _ _ Hz0).
        reflexivity. }
  apply (Qle_lt_trans ((v * v - u * u) * (1 / 6))
                      (cos_partial k u - cos_partial k v)
                      (du + dv)).
  - exact Hd.
  - apply (Qle_lt_trans (cos_partial k u - cos_partial k v)
                        (Qabs (cos_partial k u) + Qabs (cos_partial k v))
                        (du + dv)).
    + apply (Qle_trans _ (Qabs (cos_partial k u - cos_partial k v)) _).
      * apply Qle_Qabs.
      * exact Htri.
    + apply (Qplus_lt_compat (Qabs (cos_partial k u)) du
                             (Qabs (cos_partial k v)) dv).
      * exact Hdu.
      * exact Hdv.
Qed.

(* Inverse bound (distance form): [3/2 <= u <= v <= 5/3], pointwise
   [|cos_k(u)| < du], [|cos_k(v)| < dv] imply [v - u < 2*(du + dv)].
   From [v^2-u^2 == (v-u)(v+u)] and [v+u >= 3] one gets
   [3*(v-u) <= v^2-u^2]; compose with the pointwise form. *)
Lemma cos_inv_dist_prop : forall (u v du dv : Q) (k : nat),
  (2 <= k)%nat -> Qle (3#2)%Q u -> Qle u v -> Qle v (5#3)%Q ->
  Qlt (Qabs (cos_partial k u)) du ->
  Qlt (Qabs (cos_partial k v)) dv ->
  Qlt (v - u) (2 * (du + dv)).
Proof.
  intros u v du dv k Hk Hu3 Huv Hv53 Hdu Hdv.
(* [0 <= u] and [v <= 2] (premises of the pointwise form). *)
  assert (Hu0 : Qle 0 u).
  { apply (Qle_trans _ (3#2)%Q _).
    - change (Qle 0 (3#2)%Q). unfold Qle. simpl. lia.
    - exact Hu3. }
  assert (Hv2 : Qle v 2).
  { apply (Qle_trans _ (5#3)%Q _).
    - exact Hv53.
    - change (Qle (5#3)%Q 2). unfold Qle. simpl. lia. }
(* [(v^2-u^2)/6 < du + dv]. *)
  assert (Hq : Qlt ((v * v - u * u) * (1 / 6)) (du + dv)).
  { apply (cos_inv_pt_prop u v k du dv Hk Hu0 Huv Hv2 Hdu Hdv). }
(* [v^2-u^2 == (v-u)(v+u)] and [v+u >= 3] imply
   [3*(v-u) <= v^2-u^2]. *)
  assert (Hprod : (v - u) * (v + u) == v * v - u * u) by ring.
  assert (Hvu3 : Qle ((v - u) * 3) ((v - u) * (v + u))).
  { apply (Qmult_le_compat_nonneg (v - u) (v - u) 3 (v + u)).
    - split; [apply (proj1 (Qle_minus_iff u v)); exact Huv | apply Qle_refl].
    - split; [change (Qle 0 3); unfold Qle; simpl; lia | ].
      assert (H3 : Qle 3 (v + u)).
      { apply (Qle_trans _ ((3#2)%Q + (3#2)%Q) _).
        - apply QleT'_to_Qle. apply qeq_leT'. unfold Qdiv. field.
        - apply (Qplus_le_compat (3#2)%Q v (3#2)%Q u).
          + apply (Qle_trans _ u _); [exact Hu3 | exact Huv].
          + exact Hu3. }
      exact H3. }
(* Chain: [v-u <= (v^2-u^2)/3 < 2*(du+dv)]. *)
  apply (Qle_lt_trans (v - u) ((v * v - u * u) * (1 / 3)) (2 * (du + dv))).
  - apply (Qle_trans _ (((v - u) * 3) * (1 / 3)) _).
    + apply QleT'_to_Qle. apply qeq_leT'.
      assert (Hr3 : ((v - u) * 3) * (1 / 3) == v - u)
        by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      apply Qeq_sym. exact Hr3.
    + apply (Qmult_le_compat_r ((v - u) * 3) (v * v - u * u) (1 / 3)).
      * apply (Qle_trans _ ((v - u) * (v + u)) _).
        -- exact Hvu3.
        -- apply QleT'_to_Qle. apply qeq_leT'. exact Hprod.
      * apply (Qlt_le_weak 0 (1 / 3)).
        change (Qlt 0 (1 / 3)). unfold Qdiv. compute. reflexivity.
  - assert (Hm : (v * v - u * u) * (1 / 3) == ((v * v - u * u) * (1 / 6)) * 2)
      by (unfold Qdiv; field; unfold Qeq; simpl; lia).
    assert (Hm2 : (du + dv) * 2 == 2 * (du + dv)) by ring.
    apply (Qlt_le_trans ((v * v - u * u) * (1 / 3)) ((du + dv) * 2) (2 * (du + dv))).
    + apply (Qle_lt_trans ((v * v - u * u) * (1 / 3))
                          (((v * v - u * u) * (1 / 6)) * 2) ((du + dv) * 2)).
      * apply QleT'_to_Qle. apply qeq_leT'. exact Hm.
      * apply (Qmult_lt_compat_r ((v * v - u * u) * (1 / 6)) (du + dv) 2).
        -- change (Qlt 0 2). compute. reflexivity.
        -- exact Hq.
    + apply QleT'_to_Qle. apply qeq_leT'. exact Hm2.
Qed.

(* ============================================================ *)
(* Section 3. The Cauchy property of the sequence *)
(* ============================================================ *)

(* Cauchy property: [|z_m - z_n| -> 0].  Eighth-of-eps budget:
   [eps_m, eps_n < eps/8] and the tail chain [2*(eps_n + eps_m) < eps];
   at a common pairing order [k0 >= 2] the distance-form inverse bound
   gives [|z_m - z_n| < 2*(eps_n + eps_m)]. *)
Lemma cos_seq_cauchy_prop : forall eps : Q, Qlt 0 eps ->
  { N : nat | forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
      Qlt (Qabs (cos_zero_seq m - cos_zero_seq n)) eps }.
Proof.
  intros eps Heps.
  assert (Heps8 : Qlt 0 (eps / 8)).
  { apply (Qlt_shift_div_l 0 eps 8).
    - change (Qlt 0 8). compute. reflexivity.
    - simpl. exact Heps. }
  assert (H01 : Qle 0 1).
  { apply Qlt_le_weak. change (Qlt 0 1). compute. reflexivity. }
  destruct (vt_pow_half_arch_prop 1 (eps / 8) H01 Heps8) as [t Ht].
  exists (Datatypes.S t).
  intros m n Hm Hn.
  assert (Heps_m_lt : Qlt (log_eps m) (eps / 8)).
  { apply (log_eps_lt_delta_prop (eps / 8) t m).
    - exact Ht.
    - exact Hm. }
  assert (Heps_n_lt : Qlt (log_eps n) (eps / 8)).
  { apply (log_eps_lt_delta_prop (eps / 8) t n).
    - exact Ht.
    - exact Hn. }
(* Tail chain: [2*(eps_n + eps_m) < eps]. *)
  assert (Htail : Qlt (2 * (log_eps n + log_eps m)) eps).
  { assert (Hcom : 2 * (log_eps n + log_eps m) == (log_eps n + log_eps m) * 2) by ring.
    rewrite Hcom.
    assert (Hsum : Qlt (log_eps n + log_eps m) (eps / 4)).
    { apply (Qlt_le_trans (log_eps n + log_eps m) (eps / 8 + eps / 8) (eps / 4)).
      - apply (Qplus_lt_compat (log_eps n) (eps / 8) (log_eps m) (eps / 8));
          [exact Heps_n_lt | exact Heps_m_lt].
      - apply QleT'_to_Qle. apply qeq_leT'. unfold Qdiv. field. }
    apply (Qle_lt_trans ((log_eps n + log_eps m) * 2) ((eps / 4) * 2) eps).
    - apply (Qmult_le_compat_r (log_eps n + log_eps m) (eps / 4) 2).
      + apply Qlt_le_weak. exact Hsum.
      + apply Qlt_le_weak. change (Qlt 0 2). compute. reflexivity.
    - assert (He : (eps / 4) * 2 == eps / 2) by (unfold Qdiv; field).
      apply (Qle_lt_trans ((eps / 4) * 2) (eps / 2) eps).
      + apply QleT'_to_Qle. apply qeq_leT'. exact He.
      + apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
        apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
        * apply (Qlt_shift_div_l 0 eps 2).
          -- change (Qlt 0 2). compute. reflexivity.
          -- simpl. exact Heps.
        * apply QleT'_to_Qle. apply qeq_leT'. unfold Qminus. field. }
  destruct (Qlt_le_dec (cos_zero_seq n) (cos_zero_seq m)) as [Hnm_lt | Hmn].
  - (* [z_n < z_m]: take [u := z_n], [v := z_m]. *)
    destruct (cos_root_pt_bound_prop n) as [Nn HNn].
    destruct (cos_root_pt_bound_prop m) as [Nm HMm].
    set (k0 := Nat.max 2 (Nat.max Nn Nm)).
    assert (Hk0n : (Nn <= k0)%nat).
    { unfold k0. apply (Nat.le_trans _ (Nat.max Nn Nm) _);
        [apply Nat.le_max_l | apply Nat.le_max_r]. }
    assert (Hk0m : (Nm <= k0)%nat).
    { unfold k0. apply (Nat.le_trans _ (Nat.max Nn Nm) _);
        [apply Nat.le_max_r | apply Nat.le_max_r]. }
    assert (Hd : Qlt (cos_zero_seq m - cos_zero_seq n)
                     (2 * (log_eps n + log_eps m))).
    { apply (cos_inv_dist_prop (cos_zero_seq n) (cos_zero_seq m)
                          (log_eps n) (log_eps m) k0).
      - unfold k0. apply Nat.le_max_l.
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_lowerT.
      - apply Qlt_le_weak. exact Hnm_lt.
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_upperT.
      - apply (HNn k0). exact Hk0n.
      - apply (HMm k0). exact Hk0m. }
    apply (Qle_lt_trans (Qabs (cos_zero_seq m - cos_zero_seq n))
                        (cos_zero_seq m - cos_zero_seq n) eps).
    + apply QleT'_to_Qle. apply qeq_leT'. apply Qabs_pos.
      apply (proj1 (Qle_minus_iff (cos_zero_seq n) (cos_zero_seq m))).
      apply Qlt_le_weak. exact Hnm_lt.
    + apply (Qle_lt_trans (cos_zero_seq m - cos_zero_seq n)
                          (2 * (log_eps n + log_eps m)) eps).
      * apply Qlt_le_weak. exact Hd.
      * exact Htail.
  - (* [z_m <= z_n]: take [u := z_m], [v := z_n] (symmetric case). *)
    destruct (cos_root_pt_bound_prop m) as [Nm HMm].
    destruct (cos_root_pt_bound_prop n) as [Nn HNn].
    set (k0 := Nat.max 2 (Nat.max Nm Nn)).
    assert (Hk0m : (Nm <= k0)%nat).
    { unfold k0. apply (Nat.le_trans _ (Nat.max Nm Nn) _);
        [apply Nat.le_max_l | apply Nat.le_max_r]. }
    assert (Hk0n : (Nn <= k0)%nat).
    { unfold k0. apply (Nat.le_trans _ (Nat.max Nm Nn) _);
        [apply Nat.le_max_r | apply Nat.le_max_r]. }
    assert (Hd : Qlt (cos_zero_seq n - cos_zero_seq m)
                     (2 * (log_eps m + log_eps n))).
    { apply (cos_inv_dist_prop (cos_zero_seq m) (cos_zero_seq n)
                          (log_eps m) (log_eps n) k0).
      - unfold k0. apply Nat.le_max_l.
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_lowerT.
      - exact Hmn.
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_upperT.
      - apply (HMm k0). exact Hk0m.
      - apply (HNn k0). exact Hk0n. }
    apply (Qle_lt_trans (Qabs (cos_zero_seq m - cos_zero_seq n))
                        (cos_zero_seq n - cos_zero_seq m) eps).
    + rewrite (Qabs_Qminus (cos_zero_seq m) (cos_zero_seq n)).
      apply QleT'_to_Qle. apply qeq_leT'. apply Qabs_pos.
      apply (proj1 (Qle_minus_iff (cos_zero_seq m) (cos_zero_seq n))).
      exact Hmn.
    + apply (Qle_lt_trans (cos_zero_seq n - cos_zero_seq m)
                          (2 * (log_eps m + log_eps n)) eps).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hcom : 2 * (log_eps m + log_eps n) == 2 * (log_eps n + log_eps m)) by ring.
        rewrite Hcom. exact Htail.
Qed.

(* Assumption audit for all mission statements of this file. *)
Print Assumptions cos_zero_lower_prop.
Print Assumptions cos_zero_upper_prop.
Print Assumptions cos_zero_nonneg_prop.
Print Assumptions cos_zero_le_two_prop.
Print Assumptions cos_zero_abs_le_two_prop.
Print Assumptions cos_root_pt_bound_prop.
Print Assumptions cos_inv_pt_prop.
Print Assumptions cos_inv_dist_prop.
Print Assumptions cos_seq_cauchy_prop.

(* ============================================================ *)
(* Appended section: Set-carried twins of the order faces        *)
(*
   Mission.  Set-carried twins of the strict-order, non-strict
     order and equality statement faces of this file: each twin
     restates the same mathematical content with the reflected
     decision types [QltT]/[QleT']/[QeqT]/[NatLe] in the place of
     the [Prop]-level [Qlt]/[Qle]/[Qeq]/[(<=)%nat] faces, so the
     twin statement face lives in [Set] with no [Prop] component.
     Each twin is proved by transporting through the decision
     bridges and calling the original statement; the original
     statements are untouched.

   Dependencies.  The decision bridges of PiKernelSlack
     ([QltT_to_Qlt]/[Qlt_to_QltT]/[QleT'_to_Qle]/[Qle_to_QleT']/
     [qeqT_imp_qeq]/[qeq_imp_qeqT]/[NatLe_drop]/[NatLe_lift]).

   References.  The original statements of this file (each twin
     names its original in the one-line annotation above it).

   Constructivity.  Statement faces carried at the [Set] level
     ([QltT]/[QleT']/[QeqT]/[NatLe]); proof bodies are transport
     chains through the decision bridges; no solver closes any
     twin; assumption-free.

   Build.  Compiled together with this file; see the header of
     this file for the build recipe.
*)


(* Set twin of cos_zero_abs_le_twoT *)
Lemma cos_zero_abs_le_twoT : forall n : nat, QleT' (Qabs (cos_zero_seq n)) 2.
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (cos_zero_abs_le_two_prop n).
  all: first [ apply QltT_to_Qlt; assumption
            | apply QleT'_to_Qle; assumption
            | apply qeqT_imp_qeq; assumption
            | apply NatLe_drop; assumption
            | (intros; apply QltT_to_Qlt; assumption)
            | (intros; apply QleT'_to_Qle; assumption)
            | (intros; apply qeqT_imp_qeq; assumption)
            | (intros; apply NatLe_drop; assumption)
            | assumption ].
Qed.

(* Set twin of cos_inv_pt_prop *)
Lemma cos_inv_ptT : forall (u v : Q) (k : nat) (du dv : Q), NatLe (2) (k) -> QleT' 0 u -> QleT' u v -> QleT' v 2 -> QltT (Qabs (cos_partial k u)) du -> QltT (Qabs (cos_partial k v)) dv -> QltT ((v * v - u * u) * (1 / 6)) (du + dv).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (cos_inv_pt_prop u v k du dv).
  all: first [ apply QltT_to_Qlt; assumption
            | apply QleT'_to_Qle; assumption
            | apply qeqT_imp_qeq; assumption
            | apply NatLe_drop; assumption
            | (intros; apply QltT_to_Qlt; assumption)
            | (intros; apply QleT'_to_Qle; assumption)
            | (intros; apply qeqT_imp_qeq; assumption)
            | (intros; apply NatLe_drop; assumption)
            | assumption ].
Qed.

(* Set twin of cos_inv_distT *)
Lemma cos_inv_distT : forall (u v du dv : Q) (k : nat), NatLe (2) (k) -> QleT' (3#2)%Q u -> QleT' u v -> QleT' v (5#3)%Q -> QltT (Qabs (cos_partial k u)) du -> QltT (Qabs (cos_partial k v)) dv -> QltT (v - u) (2 * (du + dv)).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (cos_inv_dist_prop u v du dv k).
  all: first [ apply QltT_to_Qlt; assumption
            | apply QleT'_to_Qle; assumption
            | apply qeqT_imp_qeq; assumption
            | apply NatLe_drop; assumption
            | (intros; apply QltT_to_Qlt; assumption)
            | (intros; apply QleT'_to_Qle; assumption)
            | (intros; apply qeqT_imp_qeq; assumption)
            | (intros; apply NatLe_drop; assumption)
            | assumption ].
Qed.
