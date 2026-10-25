(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * PiPascalResidueT: Set-carried twins for the anti-diagonal band
      representation of the truncation remainder

    Mission.  Path A v2.4 Set-carried twins for all named statements
    in [PiPascalResidue] -- the dual-rail companion providing
    QeqT-based decidable carriers for each statement face, enabling
    extraction with zero [Obj.magic].  Every twin proof body in this
    file is self-sufficient: it consumes no Prop-carried statement,
    running instead on the decision-carried equality [QeqT] through
    a two-bridge hub into rational-field arithmetic and the
    definitional folds of the row-sum machine.  Four faces whose
    dependency closure needs the row-identity depth
    ([piLc_bandsep_stepT]/[piLc_dres_bandsepT]/[piLc_dres_bandT]/
    [piLc_double_sum_bandT]) keep their transport bodies pending the
    self-sufficient recast of the row identity.

    Dependencies.  [PiPascalResidue] (the definition and statement
    faces of the anti-diagonal band layer), [PiCompareT] (the
    [Id]/[QltT]/[QleT']/[NatLe] canonical carriers); [PiKernelSlack]
    and [PiPascalMachine] are required directly because the recast
    bodies reference the [QeqT] carrier, the power-series data face
    and the row-sum machine by their own names (imports are not
    transitive).

    References.  [PiKernelSlack] (the [QeqT] carrier and the
    power-series data face); [PiPascalMachine] (the [piLsb_sumR]
    row-sum machine); [PiRowIdentity] (the product-coefficient row).

    Constructivity.  Statement faces are all carried at the [Set]
    level; the recast bodies consume zero Prop-carried statements --
    the only in-body [Prop] residue is constructive rational-field
    bookkeeping inside the two hub bridges and ring/rewrite steps
    (stdlib [Qeq_alt] and field identities); [lia] appears only as
    auxiliary [nat]-side index bookkeeping; no solver closes any
    twin statement; definitions are transparent and extractable;
    the computational witnesses of the final section are auxiliary
    statements whose trivial character is declared explicitly.

    Build.  coqc -q -Q theories pi_leibniz -Q theories/Reals/Cauchy "" theories/Reals/Cauchy/PiPascalResidueT.v
*)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.
Require Import PiPascalMachine.
Require Import PiRowIdentity.
Require Import PiPascalResidue.
Require Import PiCompareT.

(* ==== Section 1. The decision-carried equality hub (two bridges) ==== *)

(* Down-lift: the decision-carried equality implies the field
   equality.  Consumes only the stdlib [Qeq_alt] characterization. *)
Lemma piLcrt_qeq_of_qeqT : forall a b : Q, QeqT a b -> a == b.
Proof.
  intros a b H. unfold QeqT in H. destruct (Qcompare a b) eqn:E.
  - exact (proj2 (Qeq_alt a b) E).
  - inversion H.
  - inversion H.
Qed.

(* Up-lift: the field equality implies the decision-carried equality. *)
Lemma piLcrt_qeqT_of_qeq : forall a b : Q, a == b -> QeqT a b.
Proof.
  intros a b Hab. unfold QeqT. destruct (Qcompare a b) eqn:E.
  - apply id_refl.
  - exfalso.
    assert (Hc : Qcompare a b = Eq) by exact (proj1 (Qeq_alt a b) Hab).
    rewrite E in Hc. discriminate Hc.
  - exfalso.
    assert (Hc : Qcompare a b = Eq) by exact (proj1 (Qeq_alt a b) Hab).
    rewrite E in Hc. discriminate Hc.
Qed.

(* Reflexivity of the decision-carried equality, via the hub. *)
Lemma piLcrt_qeqT_refl : forall a : Q, QeqT a a.
Proof. intros a. apply piLcrt_qeqT_of_qeq. apply Qeq_refl. Qed.

(* Symmetry, via the hub. *)
Lemma piLcrt_qeqT_sym : forall a b : Q, QeqT a b -> QeqT b a.
Proof.
  intros a b H. apply piLcrt_qeqT_of_qeq.
  rewrite (piLcrt_qeq_of_qeqT a b H). apply Qeq_refl.
Qed.

(* Transitivity, via the hub. *)
Lemma piLcrt_qeqT_trans : forall a b c : Q, QeqT a b -> QeqT b c -> QeqT a c.
Proof.
  intros a b c H1 H2. apply piLcrt_qeqT_of_qeq.
  transitivity b.
  - exact (piLcrt_qeq_of_qeqT a b H1).
  - exact (piLcrt_qeq_of_qeqT b c H2).
Qed.

(* ==== Section 2. The row-sum machine at the decision-carried level ==== *)

(* The definitional snoc fold, stated for rewriting. *)
Lemma piLcrt_sumR_snocT : forall (f : nat -> Q) (n : nat),
  QeqT (piLsb_sumR f (Datatypes.S n)) (piLsb_sumR f n + f n).
Proof. intros f n. apply piLcrt_qeqT_refl. Qed.

(* Pointwise congruence of row sums ([NatLe]-carried pointwise premise). *)
Lemma piLcrt_sumR_extT : forall (f g : nat -> Q) (n : nat),
  (forall i : nat, NatLe (Datatypes.S i) n -> QeqT (f i) (g i)) ->
  QeqT (piLsb_sumR f n) (piLsb_sumR g n).
Proof.
  intros f g n. induction n as [| m IH]; intros Hfg.
  - apply piLcrt_qeqT_refl.
  - apply piLcrt_qeqT_of_qeq. cbn [piLsb_sumR].
    rewrite (piLcrt_qeq_of_qeqT _ _ (IH (fun i Hi =>
      Hfg i (NatLe_lift (Datatypes.S i) (Datatypes.S m)
               (Nat.le_le_succ_r (Datatypes.S i) m (NatLe_drop (Datatypes.S i) m Hi)))))).
    rewrite (piLcrt_qeq_of_qeqT _ _ (Hfg m
      (NatLe_lift (Datatypes.S m) (Datatypes.S m) (Nat.le_refl (Datatypes.S m))))).
    apply Qeq_refl.
Qed.

(* The row-sum machine is additive pointwise. *)
Lemma piLcrt_sumR_plusT : forall (f g : nat -> Q) (n : nat),
  QeqT (piLsb_sumR (fun i => f i + g i) n) (piLsb_sumR f n + piLsb_sumR g n).
Proof.
  intros f g n. induction n as [| m IH].
  - apply piLcrt_qeqT_of_qeq. cbn [piLsb_sumR]. cbv beta. ring.
  - apply piLcrt_qeqT_of_qeq. cbn [piLsb_sumR]. cbv beta.
    rewrite (piLcrt_qeq_of_qeqT _ _ IH). ring.
Qed.

(* Scalar extraction from a row sum. *)
Lemma piLcrt_sumR_scalT : forall (c : Q) (f : nat -> Q) (n : nat),
  QeqT (piLsb_sumR (fun i => c * f i) n) (c * piLsb_sumR f n).
Proof.
  intros c f n. induction n as [| m IH].
  - apply piLcrt_qeqT_of_qeq. cbn [piLsb_sumR]. cbv beta. ring.
  - apply piLcrt_qeqT_of_qeq. cbn [piLsb_sumR]. cbv beta.
    rewrite (piLcrt_qeq_of_qeqT _ _ IH). ring.
Qed.

(* Negation commutes with the row-sum machine. *)
Lemma piLcrt_sumR_oppT : forall (f : nat -> Q) (n : nat),
  QeqT (piLsb_sumR (fun i => - f i) n) (- piLsb_sumR f n).
Proof.
  intros f n. induction n as [| m IH].
  - apply piLcrt_qeqT_of_qeq. cbn [piLsb_sumR]. cbv beta. ring.
  - apply piLcrt_qeqT_of_qeq. cbn [piLsb_sumR]. cbv beta.
    rewrite (piLcrt_qeq_of_qeqT _ _ IH). ring.
Qed.

(* Head splitting of a row sum. *)
Lemma piLcrt_sumR_headT : forall (f : nat -> Q) (n : nat),
  QeqT (piLsb_sumR f (Datatypes.S n))
       (f 0%nat + piLsb_sumR (fun i => f (Datatypes.S i)) n).
Proof.
  intros f n. induction n as [| m IH].
  - apply piLcrt_qeqT_of_qeq. cbn [piLsb_sumR]. cbv beta. ring.
  - apply piLcrt_qeqT_of_qeq. cbn [piLsb_sumR]. cbv beta.
    rewrite (piLcrt_qeq_of_qeqT _ _ IH). ring.
Qed.

(* ==== Section 3. The series data face at the decision-carried level ==== *)

Lemma piLcrt_q_pow_succ : forall x n, q_pow x (Datatypes.S n) == x * q_pow x n.
Proof. intros. reflexivity. Qed.

Lemma piLcrt_q_fact_succ : forall k : nat, q_fact (Datatypes.S k) == (Z.of_nat (Datatypes.S k) # 1) * q_fact k.
Proof. intro k. reflexivity. Qed.

(* The zeroth sine term is the identity (normalization face;
   canonical rewrite chain). *)
Lemma piLcrt_q_pow_0 : forall x : Q, q_pow x 0 == 1.
Proof. intros x. reflexivity. Qed.

Lemma piLcrt_q_fact_0 : q_fact 0 == 1.
Proof. reflexivity. Qed.

Lemma piLcrt_qdiv_1_r : forall x : Q, (x / 1)%Q == x.
Proof.
  intros x. unfold Qdiv, Qeq. cbn. destruct x as [xn xd]. cbn.
  rewrite Z.mul_1_r. rewrite (Pos.mul_1_r xd). reflexivity.
Qed.

Lemma piLcrt_sin_term_0 : forall x : Q, sin_term 0%nat x == x.
Proof.
  intros x. unfold sin_term.
  rewrite (piLcrt_q_pow_0 (-1)%Q).
  rewrite (piLcrt_q_pow_succ x 0).
  rewrite (piLcrt_q_pow_0 x).
  rewrite (piLcrt_q_fact_succ 0).
  rewrite piLcrt_q_fact_0.
  change (Z.of_nat 1) with 1%Z.
  rewrite (Qmult_1_r x).
  rewrite (Qmult_1_r (1 # 1)%Q).
  rewrite (piLcrt_qdiv_1_r x).
  apply Qmult_1_l.
Qed.

(* The zeroth cosine term is one (normalization face;
   canonical rewrite chain). *)
Lemma piLcrt_cos_term_0 : forall x : Q, cos_term 0%nat x == 1.
Proof.
  intros x. unfold cos_term.
  change (2 * 0)%nat with 0%nat.
  rewrite (piLcrt_q_pow_0 (-1)%Q).
  rewrite (piLcrt_q_pow_0 x).
  rewrite piLcrt_q_fact_0.
  rewrite (piLcrt_qdiv_1_r 1%Q).
  apply Qmult_1_l.
Qed.

(* The row-sum-machine representation of the sine partial sums. *)
Lemma piLcrt_sin_partial_sumRT : forall (n : nat) (x : Q),
  QeqT (sin_partial n x) (piLsb_sumR (fun m => sin_term m x) (Datatypes.S n)).
Proof.
  intros n x. induction n as [| p IH].
  - apply piLcrt_qeqT_of_qeq. cbn [sin_partial piLsb_sumR]. cbv beta. ring.
  - apply piLcrt_qeqT_of_qeq. cbn [sin_partial].
    rewrite (piLcrt_qeq_of_qeqT _ _ IH). cbn [piLsb_sumR]. cbv beta. ring.
Qed.

(* The double-angle stratification identity:
   [2 * S_m * C_m == S_m(2x) + dres m x], by the [dres] recursion. *)
Lemma piLcrt_double_sum_dres : forall (m : nat) (x : Q),
  QeqT (2%Q * sin_partial m x * cos_partial m x)
       (sin_partial m (2 * x)%Q + piL_sin_dres m x).
Proof.
  intros m x. induction m as [| p IH].
  - apply piLcrt_qeqT_of_qeq. cbn [sin_partial cos_partial piL_sin_dres].
    rewrite (piLcrt_sin_term_0 x), (piLcrt_cos_term_0 x).
    rewrite (piLcrt_sin_term_0 (2 * x)%Q). ring.
  - apply piLcrt_qeqT_of_qeq. cbn [sin_partial cos_partial piL_sin_dres].
    assert (Hre : (sin_partial p (2 * x)%Q + sin_term (Datatypes.S p) (2 * x)%Q)
                  + (piL_sin_dres p x
                     + 2 * sin_partial p x * cos_term (Datatypes.S p) x
                     + 2 * cos_partial p x * sin_term (Datatypes.S p) x
                     + 2 * sin_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
                     - sin_term (Datatypes.S p) (2 * x)%Q)
                  == (sin_partial p (2 * x)%Q + piL_sin_dres p x)
                     + (2 * sin_partial p x * cos_term (Datatypes.S p) x
                        + 2 * cos_partial p x * sin_term (Datatypes.S p) x
                        + 2 * sin_term (Datatypes.S p) x * cos_term (Datatypes.S p) x))
      by ring.
    rewrite Hre.
    rewrite <- (piLcrt_qeq_of_qeqT _ _ IH). ring.
Qed.

(* ==== Section 4. Index-reversal and triangular regrouping ==== *)

(* Set twin of piLc_sumR_rev (self-sufficient body). *)
Lemma piLc_sumR_revT : forall (n : nat) (g : nat -> Q),
  QeqT (piLsb_sumR (fun i => g (n - 1 - i)%nat) n) (piLsb_sumR g n).
Proof.
  intros n g. induction n as [| m IH].
  - apply piLcrt_qeqT_refl.
  - apply piLcrt_qeqT_of_qeq.
    assert (Ht : QeqT (piLsb_sumR (fun i => g (Datatypes.S m - 1 - Datatypes.S i)%nat) m)
                      (piLsb_sumR (fun i => g (m - 1 - i)%nat) m)).
    { apply piLcrt_sumR_extT. intros i Hi. apply piLcrt_qeqT_of_qeq.
      replace (Datatypes.S m - 1 - Datatypes.S i)%nat with (m - 1 - i)%nat by lia.
      apply Qeq_refl. }
    rewrite (piLcrt_qeq_of_qeqT _ _ (piLcrt_sumR_headT (fun i => g (Datatypes.S m - 1 - i)%nat) m)). cbv beta.
    replace (Datatypes.S m - 1 - 0)%nat with m%nat by lia.
    rewrite (piLcrt_qeq_of_qeqT _ _ (piLcrt_sumR_snocT g m)).
    rewrite (piLcrt_qeq_of_qeqT _ _ Ht), (piLcrt_qeq_of_qeqT _ _ IH). ring.
Qed.

(* Set twin of piLc_flatten (self-sufficient body). *)
Lemma piLc_flattenT : forall (K : nat) (f : nat -> nat -> Q),
  QeqT (piLsb_sumR (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (K - u)%nat) K)
       (piLsb_sumR (fun w => piLsb_sumR (fun v => f w v) (Datatypes.S w)) K).
Proof.
  intros K f. induction K as [| K IH].
  - apply piLcrt_qeqT_refl.
  - assert (Hlast : (Datatypes.S K - K)%nat = 1%nat) by lia.
    assert (Hsplit :
      QeqT (piLsb_sumR (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (Datatypes.S K - u)%nat) K)
           (piLsb_sumR (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (K - u)%nat) K
            + piLsb_sumR (fun u => f (u + (K - u))%nat (K - u)%nat) K)).
    { apply piLcrt_qeqT_trans with
        (b := piLsb_sumR (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (K - u)%nat
                          + f (u + (K - u))%nat (K - u)%nat) K).
      - apply (piLcrt_sumR_extT
                 (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (Datatypes.S K - u)%nat)
                 (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (K - u)%nat
                          + f (u + (K - u))%nat (K - u)%nat) K).
        intros u Hu. apply piLcrt_qeqT_of_qeq.
        pose proof (NatLe_drop (Datatypes.S u) K Hu) as Hud.
        replace (Datatypes.S K - u)%nat with (Datatypes.S (K - u))%nat by lia.
        cbn [piLsb_sumR]. cbv beta. apply Qeq_refl.
      - apply (piLcrt_sumR_plusT
                 (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (K - u)%nat)
                 (fun u => f (u + (K - u))%nat (K - u)%nat) K). }
    assert (HB : QeqT (piLsb_sumR (fun u => f (u + (K - u))%nat (K - u)%nat) K)
                      (piLsb_sumR (fun i => f K (Datatypes.S i)%nat) K)).
    { apply piLcrt_qeqT_trans
        with (b := piLsb_sumR (fun i => (fun u => f (u + (K - u))%nat (K - u)%nat) (K - 1 - i)%nat) K).
      - exact (piLcrt_qeqT_sym _ _
                 (piLc_sumR_revT K (fun u => f (u + (K - u))%nat (K - u)%nat))).
      - apply (piLcrt_sumR_extT
                 (fun i => (fun u => f (u + (K - u))%nat (K - u)%nat) (K - 1 - i)%nat)
                 (fun i => f K (Datatypes.S i)%nat) K).
        intros i Hi. apply piLcrt_qeqT_of_qeq. cbv beta.
        pose proof (NatLe_drop (Datatypes.S i) K Hi) as Hid.
        replace ((K - 1 - i) + (K - (K - 1 - i)))%nat with K by lia.
        replace (K - (K - 1 - i))%nat with (Datatypes.S i) by lia.
        apply Qeq_refl. }
    apply piLcrt_qeqT_of_qeq.
    rewrite (piLcrt_qeq_of_qeqT _ _
      (piLcrt_sumR_snocT (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (Datatypes.S K - u)%nat) K)).
    cbv beta.
    rewrite Hlast. cbn [piLsb_sumR]. cbv beta.
    replace (K + 0)%nat with K by lia.
    rewrite (piLcrt_qeq_of_qeqT _ _ Hsplit), (piLcrt_qeq_of_qeqT _ _ IH).
    rewrite (piLcrt_qeq_of_qeqT _ _
      (piLcrt_sumR_snocT (fun w => piLsb_sumR (fun v => f w v) (Datatypes.S w)) K)).
    cbv beta.
    rewrite (piLcrt_qeq_of_qeqT _ _ HB), (piLcrt_qeq_of_qeqT _ _ (piLcrt_sumR_headT (f K) K)).
    ring.
Qed.

(* ==== Section 5. The tail-segment difference and the band bridge ==== *)

(* Set twin of piLc_cos_tail (self-sufficient body). *)
Lemma piLc_cos_tailT : forall (w K : nat) (x : Q), NatLe (Datatypes.S (w)) (K) ->
  QeqT (piLsb_sumR (fun v => cos_term (K - v)%nat x) (Datatypes.S w))
       (cos_partial K x - cos_partial (K - 1 - w)%nat x).
Proof.
  induction w as [| w IH]; intros K x Hw.
  - pose proof (NatLe_drop (Datatypes.S 0) K Hw) as Hw0.
    apply piLcrt_qeqT_of_qeq.
    replace K with (Datatypes.S (K - 1))%nat by lia.
    replace (Datatypes.S (K - 1) - 1 - 0)%nat with (K - 1)%nat by lia.
    cbn [piLsb_sumR cos_partial]. cbv beta.
    replace (Datatypes.S (K - 1) - 0)%nat with (Datatypes.S (K - 1))%nat by lia.
    ring.
  - pose proof (NatLe_drop (Datatypes.S (Datatypes.S w)) K Hw) as Hwd.
    apply piLcrt_qeqT_of_qeq.
    rewrite (piLcrt_qeq_of_qeqT _ _ (piLcrt_sumR_snocT (fun v => cos_term (K - v)%nat x) (Datatypes.S w))).
    cbv beta.
    rewrite (piLcrt_qeq_of_qeqT _ _ (IH K x (NatLe_lift (Datatypes.S w) K ltac:(lia)))).
    replace (K - 1 - w)%nat with (Datatypes.S (K - 1 - Datatypes.S w))%nat by lia.
    replace (K - Datatypes.S w)%nat with (Datatypes.S (K - 1 - Datatypes.S w))%nat by lia.
    cbn [cos_partial]. ring.
Qed.

(* Set twin of piLc_bandsum_bridge (self-sufficient body). *)
Lemma piLc_bandsum_bridgeT : forall (k t : nat) (x : Q),
  QeqT (piLc_bandsum k t x)
       (piLsb_sumR (fun u => piLc_bandrow k (Datatypes.S (k + u)%nat) x) (Datatypes.S t)).
Proof.
  intros k t x. induction t as [| t IH].
  - apply piLcrt_qeqT_of_qeq. cbn [piLc_bandsum piLsb_sumR]. cbv beta.
    rewrite Nat.add_0_r. ring.
  - apply piLcrt_qeqT_of_qeq. cbn [piLc_bandsum]. cbv beta.
    rewrite (piLcrt_qeq_of_qeqT _ _
      (piLcrt_sumR_snocT (fun u => piLc_bandrow k (Datatypes.S (k + u)%nat) x) (Datatypes.S t))).
    cbv beta.
    rewrite (piLcrt_qeq_of_qeqT _ _ IH). ring.
Qed.

(* Set twin of piLc_bandrow_full (self-sufficient body). *)
Lemma piLc_bandrow_fullT : forall (k u : nat) (x : Q), NatLe (Datatypes.S (u)) (k) ->
  QeqT (piLc_bandrow k (Datatypes.S (k + u)%nat) x)
       (piLsb_sumR (fun v => 2%Q * sin_term (Datatypes.S (u + v)%nat) x
                            * cos_term (k - v)%nat x) (k - u)%nat).
Proof.
  intros k u x Hu. unfold piLc_bandrow.
  apply piLcrt_qeqT_trans with
    (b := piLsb_sumR (fun v => 2%Q * sin_term (Datatypes.S (k + u) - k + v)%nat x
                                  * cos_term (k - v)%nat x) (k - u)%nat).
  - apply piLcrt_qeqT_of_qeq.
    replace (2 * k + 1 - Datatypes.S (k + u))%nat with (k - u)%nat by lia.
    apply Qeq_refl.
  - apply (piLcrt_sumR_extT
             (fun v => 2%Q * sin_term (Datatypes.S (k + u) - k + v)%nat x * cos_term (k - v)%nat x)
             (fun v => 2%Q * sin_term (Datatypes.S (u + v)%nat) x * cos_term (k - v)%nat x) (k - u)%nat).
    intros v Hv. apply piLcrt_qeqT_of_qeq.
    replace (Datatypes.S (k + u) - k + v)%nat with (Datatypes.S (u + v))%nat by lia.
    apply Qeq_refl.
Qed.

(* ==== Section 6. The separated representation of the band sum ==== *)

(* Set twin of piLc_bandsum_sep (self-sufficient body). *)
Lemma piLc_bandsum_sepT : forall (k : nat) (x : Q),
  QeqT (piLc_bandsum k (k - 1)%nat x) (piLc_bandsep k x).
Proof.
  intros k x. destruct k as [| k].
  - apply piLcrt_qeqT_refl.
  - replace (Datatypes.S k - 1)%nat with k by lia.
    apply piLcrt_qeqT_trans with
      (b := piLsb_sumR (fun u => piLc_bandrow (Datatypes.S k)
                              (Datatypes.S (Datatypes.S k + u)%nat) x) (Datatypes.S k)).
    { apply piLc_bandsum_bridgeT. }
    apply piLcrt_qeqT_trans with
      (b := piLsb_sumR (fun u => piLsb_sumR (fun v =>
                          2%Q * sin_term (Datatypes.S (u + v)%nat) x
                          * cos_term (Datatypes.S k - v)%nat x)
                          (Datatypes.S k - u)%nat) (Datatypes.S k)).
    { apply (piLcrt_sumR_extT
               (fun u => piLc_bandrow (Datatypes.S k) (Datatypes.S (Datatypes.S k + u)%nat) x)
               (fun u => piLsb_sumR (fun v => 2%Q * sin_term (Datatypes.S (u + v)%nat) x
                                    * cos_term (Datatypes.S k - v)%nat x)
                          (Datatypes.S k - u)%nat) (Datatypes.S k)).
      intros u Hu.
      apply (piLc_bandrow_fullT (Datatypes.S k) u x Hu). }
    apply piLcrt_qeqT_trans with
      (b := piLsb_sumR (fun w => piLsb_sumR (fun v =>
                      2%Q * sin_term (Datatypes.S w) x
                      * cos_term (Datatypes.S k - v)%nat x) (Datatypes.S w))
                      (Datatypes.S k)).
    { apply (piLc_flattenT (Datatypes.S k)
               (fun w v => 2%Q * sin_term (Datatypes.S w) x
                           * cos_term (Datatypes.S k - v)%nat x)). }
    unfold piLc_bandsep.
    apply piLcrt_qeqT_trans with
      (b := piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                                   * piLsb_sumR (fun v => cos_term (Datatypes.S k - v)%nat x)
                                              (Datatypes.S w)) (Datatypes.S k)).
    { apply (piLcrt_sumR_extT
               (fun w => piLsb_sumR (fun v => 2%Q * sin_term (Datatypes.S w) x
                                                * cos_term (Datatypes.S k - v)%nat x) (Datatypes.S w))
               (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * piLsb_sumR (fun v => cos_term (Datatypes.S k - v)%nat x) (Datatypes.S w))
               (Datatypes.S k)).
      intros w Hw.
      apply (piLcrt_sumR_scalT (2%Q * sin_term (Datatypes.S w) x)
               (fun v => cos_term (Datatypes.S k - v)%nat x) (Datatypes.S w)). }
    { apply (piLcrt_sumR_extT
               (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * piLsb_sumR (fun v => cos_term (Datatypes.S k - v)%nat x) (Datatypes.S w))
               (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * (cos_partial (Datatypes.S k) x
                            - cos_partial (Datatypes.S k - 1 - w)%nat x))
               (Datatypes.S k)).
      intros w Hw.
      apply piLcrt_qeqT_of_qeq. cbv beta.
      rewrite (piLcrt_qeq_of_qeqT _ _ (piLc_cos_tailT w (Datatypes.S k) x Hw)).
      apply Qeq_refl. }
Qed.

(* ==== Section 7. The step of the separated representation and the match with the remainder
   recursion ==== *)

(* Set twin of piLc_bandsep_step (self-sufficient body; the row
   identity enters at the decision-carried level). *)
Lemma piLc_bandsep_stepT : forall (k : nat) (x : Q), QeqT (piLc_bandsep (Datatypes.S k) x) (piLc_bandsep k x + (2%Q * sin_partial k x * cos_term (Datatypes.S k) x + 2%Q * cos_partial k x * sin_term (Datatypes.S k) x + 2%Q * sin_term (Datatypes.S k) x * cos_term (Datatypes.S k) x - sin_term (Datatypes.S k) (2 * x)%Q)).
Proof.
  intros k x. unfold piLc_bandsep.
  apply piLcrt_qeqT_of_qeq.
  rewrite (piLcrt_qeq_of_qeqT _ _
    (piLcrt_sumR_snocT (fun w => 2%Q * sin_term (Datatypes.S w) x
                                   * (cos_partial (Datatypes.S k) x
                                      - cos_partial (Datatypes.S k - 1 - w)%nat x)) k)).
  cbv beta.
  replace (Datatypes.S k - 1)%nat with k by lia.
  replace (k - k)%nat with 0%nat by lia.
  cbn [cos_partial].
  assert (Hpt : QeqT
    (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * (cos_partial k x + cos_term (Datatypes.S k) x
                            - cos_partial (k - w)%nat x)) k)
    (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * (cos_partial k x - cos_partial (k - 1 - w)%nat x)) k
     + piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                          * (cos_term (Datatypes.S k) x - cos_term (k - w)%nat x)) k)).
  { apply piLcrt_qeqT_trans with
      (b := piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                                  * (cos_partial k x - cos_partial (k - 1 - w)%nat x)
                                  + (2%Q * sin_term (Datatypes.S w) x
                                     * (cos_term (Datatypes.S k) x - cos_term (k - w)%nat x))) k).
    - apply (piLcrt_sumR_extT
               (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * (cos_partial k x + cos_term (Datatypes.S k) x
                            - cos_partial (k - w)%nat x))
               (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * (cos_partial k x - cos_partial (k - 1 - w)%nat x)
                         + (2%Q * sin_term (Datatypes.S w) x
                            * (cos_term (Datatypes.S k) x - cos_term (k - w)%nat x))) k).
      intros w Hw. apply piLcrt_qeqT_of_qeq. cbv beta.
      pose proof (NatLe_drop (Datatypes.S w) k Hw) as Hwd.
      replace (k - w)%nat with (Datatypes.S (k - 1 - w))%nat by lia.
      cbn [cos_partial]. ring.
    - apply (piLcrt_sumR_plusT
               (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * (cos_partial k x - cos_partial (k - 1 - w)%nat x))
               (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * (cos_term (Datatypes.S k) x - cos_term (k - w)%nat x)) k). }
  rewrite (piLcrt_qeq_of_qeqT _ _ Hpt).
  assert (Hrow : QeqT (piLrowB_row (Datatypes.S k) x)
    (2%Q * sin_term 0 x * cos_term (Datatypes.S k) x
     + (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                                   * cos_term (k - w)%nat x) k
        + 2%Q * sin_term (Datatypes.S k) x * cos_term 0 x))).
  { unfold piLrowB_row.
    apply piLcrt_qeqT_of_qeq.
    rewrite (piLcrt_qeq_of_qeqT _ _ (piLcrt_sumR_headT
      (fun i => 2%Q * sin_term i x * cos_term (Datatypes.S k - i)%nat x) (Datatypes.S k))).
    cbv beta.
    rewrite (piLcrt_qeq_of_qeqT _ _ (piLcrt_sumR_snocT
      (fun i => 2%Q * sin_term (Datatypes.S i) x
                * cos_term (Datatypes.S k - Datatypes.S i)%nat x) k)).
    cbv beta.
    replace (Datatypes.S k - Datatypes.S k)%nat with 0%nat by lia.
    apply Qeq_refl. }
  pose proof (piLrowB_row_sin_termT (Datatypes.S k) x) as HTwin.
  assert (Hrow2 : QeqT (sin_term (Datatypes.S k) (2 * x)%Q)
    (2%Q * sin_term 0 x * cos_term (Datatypes.S k) x
     + (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                                   * cos_term (k - w)%nat x) k
        + 2%Q * sin_term (Datatypes.S k) x * cos_term 0 x))).
  { apply piLcrt_qeqT_trans with (b := piLrowB_row (Datatypes.S k) x).
    - apply piLcrt_qeqT_sym. exact HTwin.
    - exact Hrow. }
  assert (HE2 : QeqT
    (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                          * cos_term (k - w)%nat x) k)
    (sin_term (Datatypes.S k) (2 * x)%Q
     - (2%Q * sin_term 0 x * cos_term (Datatypes.S k) x
        + 2%Q * sin_term (Datatypes.S k) x * cos_term 0 x))).
  { apply piLcrt_qeqT_of_qeq.
    rewrite (piLcrt_qeq_of_qeqT _ _ Hrow2). ring. }
  assert (Hshift : QeqT (piLsb_sumR (fun w => sin_term (Datatypes.S w) x) k)
                        (sin_partial k x - sin_term 0 x)).
  { apply piLcrt_qeqT_of_qeq.
    rewrite (piLcrt_qeq_of_qeqT _ _ (piLcrt_sin_partial_sumRT k x)).
    rewrite (piLcrt_qeq_of_qeqT _ _ (piLcrt_sumR_headT (fun m => sin_term m x) k)).
    cbv beta. ring. }
  assert (HsplA : QeqT
    (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x * cos_term (Datatypes.S k) x) k)
    (piLsb_sumR (fun w => 2%Q * cos_term (Datatypes.S k) x * sin_term (Datatypes.S w) x) k)).
  { apply (piLcrt_sumR_extT
             (fun w => 2%Q * sin_term (Datatypes.S w) x * cos_term (Datatypes.S k) x)
             (fun w => 2%Q * cos_term (Datatypes.S k) x * sin_term (Datatypes.S w) x) k).
    intros w Hw. apply piLcrt_qeqT_of_qeq. ring. }
  assert (HsplB : QeqT
    (2%Q * cos_term (Datatypes.S k) x * piLsb_sumR (fun w => sin_term (Datatypes.S w) x) k)
    (2%Q * cos_term (Datatypes.S k) x * (sin_partial k x - sin_term 0 x))).
  { apply piLcrt_qeqT_of_qeq.
    rewrite (piLcrt_qeq_of_qeqT _ _ Hshift).
    ring. }
  assert (HsplA2 : QeqT
    (piLsb_sumR (fun w => 2%Q * cos_term (Datatypes.S k) x * sin_term (Datatypes.S w) x) k)
    (2%Q * cos_term (Datatypes.S k) x * piLsb_sumR (fun w => sin_term (Datatypes.S w) x) k)).
  { apply (piLcrt_sumR_scalT (2%Q * cos_term (Datatypes.S k) x)
             (fun w => sin_term (Datatypes.S w) x) k). }
  assert (Hspl : QeqT
    (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x * cos_term (Datatypes.S k) x) k)
    (2%Q * cos_term (Datatypes.S k) x * (sin_partial k x - sin_term 0 x))).
  { apply piLcrt_qeqT_trans with
      (b := 2%Q * cos_term (Datatypes.S k) x * piLsb_sumR (fun w => sin_term (Datatypes.S w) x) k).
    - apply piLcrt_qeqT_trans with
        (b := piLsb_sumR (fun w => 2%Q * cos_term (Datatypes.S k) x * sin_term (Datatypes.S w) x) k).
      + exact HsplA.
      + exact HsplA2.
    - exact HsplB. }
  assert (Hconst : QeqT
    (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                          * (cos_term (Datatypes.S k) x
                             - cos_term (k - w)%nat x)) k)
    (2%Q * cos_term (Datatypes.S k) x * (sin_partial k x - sin_term 0 x)
     - (sin_term (Datatypes.S k) (2 * x)%Q
        - (2%Q * sin_term 0 x * cos_term (Datatypes.S k) x
           + 2%Q * sin_term (Datatypes.S k) x * cos_term 0 x)))).
  { apply piLcrt_qeqT_trans with
      (b := piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                                   * cos_term (Datatypes.S k) x) k
       + piLsb_sumR (fun w => - (2%Q * sin_term (Datatypes.S w) x
                                   * cos_term (k - w)%nat x)) k).
    - apply piLcrt_qeqT_trans with
        (b := piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x * cos_term (Datatypes.S k) x
                                   + -(2%Q * sin_term (Datatypes.S w) x
                                      * cos_term (k - w)%nat x)) k).
      { apply (piLcrt_sumR_extT
                 (fun w => 2%Q * sin_term (Datatypes.S w) x
                           * (cos_term (Datatypes.S k) x - cos_term (k - w)%nat x))
                 (fun w => 2%Q * sin_term (Datatypes.S w) x * cos_term (Datatypes.S k) x
                           + -(2%Q * sin_term (Datatypes.S w) x
                              * cos_term (k - w)%nat x)) k).
        intros w Hw. apply piLcrt_qeqT_of_qeq. ring. }
      { apply (piLcrt_sumR_plusT
                 (fun w => 2%Q * sin_term (Datatypes.S w) x * cos_term (Datatypes.S k) x)
                 (fun w => - (2%Q * sin_term (Datatypes.S w) x
                              * cos_term (k - w)%nat x)) k). }
    - apply piLcrt_qeqT_of_qeq.
      rewrite (piLcrt_qeq_of_qeqT _ _ Hspl),
              (piLcrt_qeq_of_qeqT _ _ (piLcrt_sumR_oppT
                 (fun w => 2%Q * sin_term (Datatypes.S w) x
                           * cos_term (k - w)%nat x) k)),
              (piLcrt_qeq_of_qeqT _ _ HE2).
      ring. }
  rewrite (piLcrt_qeq_of_qeqT _ _ Hconst).
  ring.
Qed.

(* Set twin of piLc_dres_bandsep (self-sufficient body by the [dres]
   recursion and the step face). *)
Lemma piLc_dres_bandsepT : forall (k : nat) (x : Q), QeqT (piL_sin_dres k x) (piLc_bandsep k x).
Proof.
  intros k x. induction k as [| p IH].
  - apply piLcrt_qeqT_refl.
  - apply piLcrt_qeqT_trans with
      (b := piLc_bandsep p x
            + (2%Q * sin_partial p x * cos_term (Datatypes.S p) x
               + 2%Q * cos_partial p x * sin_term (Datatypes.S p) x
               + 2%Q * sin_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
               - sin_term (Datatypes.S p) (2 * x)%Q)).
    + apply piLcrt_qeqT_of_qeq. cbn [piL_sin_dres].
      rewrite (piLcrt_qeq_of_qeqT _ _ IH). ring.
    + apply piLcrt_qeqT_sym. apply piLc_bandsep_stepT.
Qed.
(* Set twin of piLc_dres_band (self-sufficient body by the separated
   representation and the band representation faces). *)
Lemma piLc_dres_bandT : forall (k : nat) (x : Q), QeqT (piL_sin_dres k x) (piLc_bandsum k (k - 1)%nat x).
Proof.
  intros k x. apply piLcrt_qeqT_trans with (b := piLc_bandsep k x).
  - apply piLc_dres_bandsepT.
  - apply piLcrt_qeqT_sym. apply piLc_bandsum_sepT.
Qed.

(* Set twin of piLc_double_sum_band (self-sufficient body via the
   stratification identity and the band representation face). *)
Lemma piLc_double_sum_bandT : forall (k : nat) (x : Q), QeqT (2%Q * sin_partial k x * cos_partial k x) (sin_partial k (2 * x)%Q + piLc_bandsum k (k - 1)%nat x).
Proof.
  intros k x.
  apply piLcrt_qeqT_trans with (b := sin_partial k (2 * x)%Q + piL_sin_dres k x).
  - apply piLcrt_double_sum_dres.
  - apply piLcrt_qeqT_of_qeq.
    rewrite (piLcrt_qeq_of_qeqT _ _ (piLc_dres_bandT k x)).
    apply Qeq_refl.
Qed.

(* ==== Section 9. Computational witnesses (auxiliary statements; trivial character declared
   explicitly) ==== *)

(* For [k=3] and [x=13/10]: the band value of the remainder agrees
   with independent exact-arithmetic recomputation (concrete-value
   faces closed by computation). *)
Lemma piLc_witness_dres3_valT : QeqT (piLc_witness_dres3) ((248270004845325853 # 18144000000000000000)%Q).
Proof. unfold QeqT, piLc_witness_dres3. vm_compute. reflexivity. Qed.

Lemma piLc_witness_dres3_bandT : QeqT (piLc_witness_dres3) (piLc_bandsum 3 2%nat (13 # 10)%Q).
Proof. unfold QeqT, piLc_witness_dres3. vm_compute. reflexivity. Qed.

Lemma piLc_witness_double3_valT : QeqT (piLc_witness_double3) ((9346034853485325853 # 18144000000000000000)%Q).
Proof. unfold QeqT, piLc_witness_double3. vm_compute. reflexivity. Qed.

Lemma piLc_witness_double3_splitT : QeqT (piLc_witness_double3)
  (sin_partial 3 (2 * (13 # 10)%Q)%Q + piLc_bandsum 3 2%nat (13 # 10)%Q).
Proof. unfold QeqT, piLc_witness_double3. vm_compute. reflexivity. Qed.
