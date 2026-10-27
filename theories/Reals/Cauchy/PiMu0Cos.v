(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)

(** * PiMu0Cos: the exponential escape-window family and the
      logarithmic window-level search bound for [pi_leibniz].

    Mission.  The window-family instance of the escape-window
      criterion at the exponential scale.  The family
      [mu0cos_e n = 8 * (1/2)^n = 2^(3-n)] replaces the linear-scale
      family [lw0m_e n = 5/(2(n+1))] of [PiSeparation] as the window
      parameterization of [pi_leibniz], and the window depth needed
      to undercut a positive margin [eps] drops from the linear
      inverse [lw0m_modulus eps = S(ceil(5/eps))] of [PiLeibnizCReal]
      to the logarithmic closed form
      [mu0cos_modulus eps = S (4 + ceil(log2(8/eps)))].  Main
      statements: [mu0_cos_hitting_bound] (the per-margin closed-form
      undercut level: the window family undercuts [eps] at a level
      bounded by the logarithmic closed form),
      [mu0_cos_q_hitting_bound] (the same bound packaged with the
      per-rational kernel margin), [mu0cos_window_exclusion_prop] (a
      window of undercut width excludes every point whose margin
      distance exceeds the width), and
      [mu0cos_escape_window_pi_prop] (the escape-window criterion
      mounted for [pi_leibniz] at the exponential family: the second
      window-family instance of the engine, whose coupling leg is
      pure arithmetic in the four-fold margin
      [8 * 2^(-n) = 4 * (2 * 2^(-n))]).  The margin source is
      consumed, not rebuilt: the distance lower bound comes from the
      Leibniz-chain kernel [leibsep_q_kernel] of [PiKernelSlack].
      The window level is a search-budget count only: it carries no
      irrationality-measure content and no uniform-in-height claim.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [ZArith.ZArith], [Arith.PeanoNat], [Lia], [Setoid]; this
      development, [ConstructiveCauchyRealsSep] (the engine),
      [PiCompareT] (the [Set]-valued [Id]/[QltT]/[NatLe]/[And]
      carriers), [PiWindowCore] (the [Id] bridges), [PiLeibnizCReal]
      ([pi_leibniz], [lw0m_xL], the read-point and symmetry
      bridges), [PiKernelSlack] ([q_pow], the kernel
      [leibsep_q_kernel], [NatLe_lift], [lw0_q_pow_pos]),
      [PiSeedSupplyShell] and [PiSeparation] (the packaged kernel
      seeds), [PiSepSearch] (the bounded search for the sample
      runs).

    References.  The repository README (Position); this development,
      [PiSeparation.v] (the linear-scale mounting of the same engine,
      mirrored statement by statement); [PiLeibnizCReal.v]
      ([lw0m_modulus]/[lw0m_modulus_bound_prop], the linear inverse
      replaced at the window level); [PiSepSearch.v] (the separator
      search the sample runs consume).

    Constructivity.  Statements are [Set]-valued: the witnesses are
      [sigT] pairs over the [Set]-carried [QltT]/[NatLe] decisions
      and the product-type conjunction; the only [Prop] occurrences
      are the [Qlt] conjuncts inside the engine's
      [creal_escape_window] face (the same rule as the engine file
      and [PiSeparation]); no decision procedure is imported;
      assumption-free.

    Build.  [coqc -native-compiler no -q -Q theories pi_leibniz -Q
      theories/Reals/Cauchy "" theories/Reals/Cauchy/PiMu0Cos.v] from
      the repository root compiles cleanly (exit 0); the first eight
      bytes of the artifact are [436f7121 00015ff4].

    This file is part of the rocq-pi-leibniz package; its interface
    may change in future releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsSep.
Require Import PiCompareT.
Require Import PiWindowCore.
Require Import PiLeibnizCReal.
Require Import PiKernelSlack.
Require Import PiSeedSupplyShell.
Require Import PiSeparation.
Require Import PiSepSearch.

(* ============================================================ *)
(* Section 0. Small [Q] bookkeeping helpers                     *)
(* ============================================================ *)

(** Positivity of the reciprocal. *)
Lemma mu0cos_qinv_pos_prop : forall b : Q, Qlt 0 b -> Qlt 0 (/ b).
Proof.
  intros b Hb. destruct b as [nb db].
  unfold Qlt in Hb. cbn [Qnum Qden] in Hb.
  rewrite Z.mul_0_l, Z.mul_1_r in Hb.
  destruct nb as [|p|p].
  - exfalso. lia.
  - cbn [Qinv]. unfold Qlt. cbn [Qnum Qden].
    rewrite Z.mul_0_l, Z.mul_1_r. exact Hb.
  - exfalso. lia.
Qed.

(** Positivity of the quotient. *)
Lemma mu0cos_qdiv_pos_prop : forall a b : Q, Qlt 0 a -> Qlt 0 b -> Qlt 0 (a / b)%Q.
Proof.
  intros a b Ha Hb. unfold Qdiv.
  apply (Qmult_lt_0_compat a (/ b)).
  - exact Ha.
  - exact (mu0cos_qinv_pos_prop b Hb).
Qed.

(** Reciprocal order reversal. *)
Lemma mu0cos_qinv_le_prop : forall a b : Q, Qlt 0 a -> Qle a b -> Qle (/ b) (/ a).
Proof.
  intros a b Ha Hab.
  assert (Hab0 : Qlt 0 b)
    by exact (Qlt_le_trans 0 a b Ha Hab).
  pose proof (mu0cos_qinv_pos_prop a Ha) as Hia.
  pose proof (mu0cos_qinv_pos_prop b Hab0) as Hib.
  assert (Hne1 : ~ a == 0%Q) by (intro Hz; apply (Qlt_not_eq 0 a Ha); exact (Qeq_sym _ _ Hz)).
  assert (Hne2 : ~ b == 0%Q) by (intro Hz; apply (Qlt_not_eq 0 b Hab0); exact (Qeq_sym _ _ Hz)).
  assert (Hkey : Qle (a * (/ a * / b))%Q (b * (/ a * / b))%Q).
  { apply (Qmult_le_compat_r a b (/ a * / b)%Q Hab).
    apply Qlt_le_weak.
    apply (Qmult_lt_0_compat (/ a) (/ b) Hia Hib). }
  assert (HL : a * (/ a * / b) == (/ b)%Q).
  { assert (Hc : (a * (/ a * / b))%Q == ((a * / a) * / b)%Q) by ring.
    rewrite Hc, (Qmult_inv_r a Hne1). apply Qmult_1_l. }
  assert (HR : b * (/ a * / b) == (/ a)%Q).
  { assert (Hc : (b * (/ a * / b))%Q == ((b * / b) * / a)%Q) by ring.
    rewrite Hc, (Qmult_inv_r b Hne2). apply Qmult_1_l. }
  rewrite HL in Hkey. rewrite HR in Hkey. exact Hkey.
Qed.

(** A positive rational is bounded by its numerator. *)
Lemma mu0cos_qle_num_prop : forall x : Q, Qlt 0 x -> Qle x (Qnum x # 1)%Q.
Proof.
  intros x Hx. unfold Qle. cbn [Qnum Qden]. rewrite Z.mul_1_r.
  assert (Hx0 : (0 <= Qnum x)%Z).
  { unfold Qlt in Hx. cbn [Qnum Qden] in Hx.
    rewrite Z.mul_0_l, Z.mul_1_r in Hx. lia. }
  assert (Hden : (1 <= Z.pos (Qden x))%Z).
  { pose proof (Pos2Z.is_pos (Qden x)) as Hp. lia. }
  assert (H2 : (1 * Qnum x <= Z.pos (Qden x) * Qnum x)%Z)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  rewrite Z.mul_1_l, (Z.mul_comm (Z.pos (Qden x)) (Qnum x)) in H2. exact H2.
Qed.

(** The nat core of the fuel adequacy: [a <= 2 ^ a]. *)
Lemma mu0cos_nat_pow2_ge : forall a : nat, (a <= 2 ^ a)%nat.
Proof.
  induction a as [|a IH].
  - apply Nat.le_0_l.
  - assert (H1 : (1 <= 2 ^ a)%nat).
    { pose proof (Nat.pow_le_mono_r 2 0 a (Nat.neq_succ_0 1) (Nat.le_0_l a)) as Hle.
      simpl in Hle. exact Hle. }
    rewrite Nat.pow_succ_r'.
    replace (S a) with (a + 1)%nat by lia.
    replace (2 * 2 ^ a)%nat with (2 ^ a + 2 ^ a)%nat by lia.
    apply (Nat.add_le_mono a (2 ^ a) 1 (2 ^ a) IH H1).
Qed.

(** Additivity of [q_pow] over the index. *)
Lemma mu0cos_q_pow_add_prop : forall (x : Q) (a b : nat),
  q_pow x (a + b)%nat == q_pow x a * q_pow x b.
Proof.
  intros x a b. induction b as [|b IH].
  - rewrite Nat.add_0_r. change (q_pow x 0) with 1%Q. rewrite Qmult_1_r. reflexivity.
  - rewrite Nat.add_succ_r, (q_pow_succ x (a + b)%nat), (q_pow_succ x b), IH. ring.
Qed.

(** The two-power product: [2^k * (1/2)^k = 1]. *)
Lemma mu0cos_two_half_mul_prop : forall k : nat,
  q_pow 2 k * q_pow (1 # 2) k == 1%Q.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - rewrite (q_pow_succ 2 k), (q_pow_succ (1 # 2) k).
    assert (Hr1 : (2 * q_pow 2 k * ((1 # 2) * q_pow (1 # 2) k))%Q
                  == (2 * (1 # 2) * (q_pow 2 k * q_pow (1 # 2) k))%Q) by ring.
    rewrite Hr1.
    assert (Hr2 : (2 * (1 # 2))%Q == 1%Q) by reflexivity.
    rewrite Hr2, Qmult_1_l. exact IH.
Qed.

(** Generic positivity of [q_pow]. *)
Lemma mu0cos_q_pow_pos_prop : forall (x : Q) (n : nat), Qlt 0 x -> Qlt 0 (q_pow x n).
Proof.
  intros x n Hx. induction n as [|n IH].
  - change (q_pow x 0) with 1%Q. unfold Qlt, Qnum, Qden; lia.
  - rewrite (q_pow_succ x n). apply (Qmult_lt_0_compat x (q_pow x n) Hx IH).
Qed.

(* ============================================================ *)
(* Section 1. The exponential window family                     *)
(* ============================================================ *)

(** [mu0cos_e n = 8 * (1/2)^n = 2^(3-n)]: the exponential window
    family.  The four-fold margin [8 * 2^(-n) = 4 * (2 * 2^(-n))]
    over the CReal resolution [2 * 2^(-n)] is the engine coupling
    condition (Section 3). *)
Definition mu0cos_e (n : nat) : Q := (8 * q_pow (1 # 2) n)%Q.

Lemma mu0cos_e_pos_prop : forall n : nat, QltT 0 (mu0cos_e n).
Proof.
  intros n. apply Qlt_to_QltT. apply (Qmult_lt_0_compat (8 # 1) (q_pow (1 # 2) n)).
  - unfold Qlt, Qnum, Qden; lia.
  - apply (mu0cos_q_pow_pos_prop (1 # 2) n).
    unfold Qlt, Qnum, Qden; lia.
Qed.

(** The exact halving step. *)
Lemma mu0cos_e_half_prop : forall n : nat,
  mu0cos_e (Datatypes.S n) == mu0cos_e n * (1 # 2)%Q.
Proof.
  intros n. unfold mu0cos_e. rewrite (q_pow_succ (1 # 2) n). ring.
Qed.

(** Strict decay. *)
Lemma mu0cos_e_decay_prop : forall n : nat,
  QltT (mu0cos_e (Datatypes.S n)) (mu0cos_e n).
Proof.
  intros n. apply Qlt_to_QltT.
  assert (Hd : (mu0cos_e n * (1 # 2) < mu0cos_e n)%Q).
  { assert (Hhalf : Qlt 0 (mu0cos_e n))
      by exact (QltT_to_Qlt 0 (mu0cos_e n) (mu0cos_e_pos_prop n)).
    assert (Hlt21 : ((1 # 2) < 1)%Q) by (unfold Qlt, Qnum, Qden; lia).
    pose proof (Qmult_lt_compat_r (1 # 2) 1 (mu0cos_e n) Hhalf Hlt21) as H0.
    assert (Hc : ((1 # 2) * mu0cos_e n)%Q == (mu0cos_e n * (1 # 2))%Q) by ring.
    assert (Hc2 : (1 * mu0cos_e n)%Q == mu0cos_e n) by ring.
    rewrite Hc, Hc2 in H0. exact H0. }
  rewrite (mu0cos_e_half_prop n). exact Hd.
Qed.

(** Antitonicity. *)
Lemma mu0cos_e_antitone_prop : forall m n : nat,
  (m <= n)%nat -> Qle (mu0cos_e n) (mu0cos_e m).
Proof.
  intros m n Hmn. induction n as [|n IH].
  - assert (Heq : m = 0%nat) by lia. subst m. apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S n)) as [Heq|Hne].
    + subst m. apply Qle_refl.
    + assert (Hmn' : (m <= n)%nat) by lia.
      apply (Qle_trans (mu0cos_e (Datatypes.S n)) (mu0cos_e n) (mu0cos_e m)).
      * apply Qlt_le_weak. apply QltT_to_Qlt. apply mu0cos_e_decay_prop.
      * exact (IH Hmn').
Qed.

(** The [Q]-level make-form of the half power (the denominator form
    used by [piL_qpow2_neg]). *)
Lemma mu0cos_qpow_half_make_prop : forall n : nat,
  q_pow (1 # 2) n == (1 # Pos.of_succ_nat (2 ^ n - 1))%Q.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite q_pow_succ, IH.
    assert (H1 : (1 <= 2 ^ n)%nat).
    { pose proof (Nat.pow_le_mono_r 2 0 n (Nat.neq_succ_0 1) (Nat.le_0_l n)) as Hle.
      simpl in Hle. exact Hle. }
    rewrite (Nat.pow_succ_r' 2 n).
    replace (2 * 2 ^ n - 1)%nat with (2 * (2 ^ n - 1) + 1)%nat by lia.
    unfold Qmult, Qeq. cbn [Qnum Qden].
    rewrite !piL_pos_succ1_prop.
    rewrite !Nat2Z.inj_add, Nat2Z.inj_mul. cbn [Z.of_nat]. lia.
Qed.

(** The bridge from the engine's [Qpower] face to the [q_pow] face. *)
Lemma mu0cos_qpow2_neg_bridge : forall n : nat,
  (2 ^ Z.opp (Z.of_nat n))%Q == q_pow (1 # 2) n.
Proof.
  intros n. rewrite (piL_qpow2_neg n), (mu0cos_qpow_half_make_prop n). reflexivity.
Qed.

(** The engine coupling leg on the engine's own [Qpower] face: the
    resolution [2 * 2^(-n)] stays below the window bound, with the
    four-fold margin. *)
Lemma mu0cos_e_coupling_prop : forall n : nat,
  Qlt (2 * 2 ^ Z.opp (Z.of_nat n))%Q (mu0cos_e n).
Proof.
  intros n. rewrite (mu0cos_qpow2_neg_bridge n).
  assert (Hhalf : Qlt 0 (1 # 2)%Q) by (unfold Qlt, Qnum, Qden; lia).
  assert (Hhalf2 : Qlt 0 (q_pow (1 # 2) n))
    by exact (mu0cos_q_pow_pos_prop (1 # 2) n Hhalf).
  assert (Hlt28 : (2 < 8)%Q) by (unfold Qlt, Qnum, Qden; lia).
  exact (Qmult_lt_compat_r 2 8 (q_pow (1 # 2) n) Hhalf2 Hlt28).
Qed.

(** The make-form of the powers of two (the fuel-adequacy anchor). *)
Lemma mu0cos_q_pow_two_make : forall a : nat,
  q_pow 2 a == (Z.of_nat (2 ^ a) # 1)%Q.
Proof.
  induction a as [|a IH].
  - reflexivity.
  - rewrite (q_pow_succ 2 a), IH.
    rewrite (Nat.pow_succ_r' 2 a), Nat2Z.inj_mul.
    unfold Qmult, Qeq. cbn [Qnum Qden]. reflexivity.
Qed.

(* ============================================================ *)
(* Section 2. The logarithmic window-depth inverse              *)
(* ============================================================ *)

(** The fuel-driven halving recursion: [mu0cos_l2c_go fuel x] counts
    the halvings of [x] until it drops to [1] (or the fuel runs out).
    The fuel is only a termination device; the spec lemma needs it
    only through [x <= q_pow 2 fuel]. *)
Fixpoint mu0cos_l2c_go (fuel : nat) (x : Q) : nat :=
  match fuel with
  | 0%nat => 0%nat
  | Datatypes.S f =>
      if Qle_bool x 1 then 0%nat else Datatypes.S (mu0cos_l2c_go f (x * (1 # 2))%Q)
  end.

Definition mu0cos_l2c_fuel (x : Q) : nat := Datatypes.S (Z.to_nat (Z.abs (Qnum x))).

(** The spec: the recursion lands on a depth whose power of two
    dominates [x]. *)
Lemma mu0cos_l2c_go_spec : forall (fuel : nat) (x : Q),
  Qlt 0 x -> Qle x (q_pow 2 fuel) ->
  Qle x (q_pow 2 (mu0cos_l2c_go fuel x)).
Proof.
  induction fuel as [|f IH]; intros x Hx0 Hle.
  - exact Hle.
  - change (mu0cos_l2c_go (Datatypes.S f) x)
      with (if Qle_bool x 1 then 0%nat else Datatypes.S (mu0cos_l2c_go f (x * (1 # 2))%Q)).
    destruct (Qle_bool x 1) eqn:E.
    + apply (QleT'_to_Qle x 1). unfold QleT'. rewrite E. apply id_refl.
    + assert (Hx2 : Qlt 0 (x * (1 # 2))%Q)
        by (apply (Qmult_lt_0_compat x (1 # 2) Hx0); unfold Qlt, Qnum, Qden; lia).
      assert (Hq2 : Qle 0 (1 # 2)%Q) by (unfold Qle, Qnum, Qden; lia).
      assert (Hsplit : Qle (x * (1 # 2)) (q_pow 2 f)).
      { pose proof (Qmult_le_compat_r x (q_pow 2 (Datatypes.S f)) (1 # 2)%Q Hle Hq2)
          as Hm.
        assert (Hcan : (q_pow 2 (Datatypes.S f) * (1 # 2))%Q == q_pow 2 f).
        { rewrite (q_pow_succ 2 f). ring. }
        rewrite Hcan in Hm. exact Hm. }
      pose proof (IH (x * (1 # 2))%Q Hx2 Hsplit) as IH2.
      assert (Hfin : Qle ((x * (1 # 2)) * 2)%Q
                       (q_pow 2 (mu0cos_l2c_go f (x * (1 # 2))) * 2)%Q).
      { assert (Hq2b : Qle 0 2%Q) by (unfold Qle, Qnum, Qden; lia).
        apply (Qmult_le_compat_r (x * (1 # 2))
                 (q_pow 2 (mu0cos_l2c_go f (x * (1 # 2)))) 2 IH2 Hq2b). }
      assert (Hx3 : x == ((x * (1 # 2)) * 2)%Q) by ring.
      assert (Hsucc : (q_pow 2 (mu0cos_l2c_go f (x * (1 # 2))%Q) * 2
                       == q_pow 2 (Datatypes.S (mu0cos_l2c_go f (x * (1 # 2))%Q)))%Q).
      { rewrite (q_pow_succ 2 (mu0cos_l2c_go f (x * (1 # 2))%Q)). ring. }
      rewrite <- Hsucc.
      apply (Qle_trans x ((x * (1 # 2)) * 2)%Q
               (q_pow 2 (mu0cos_l2c_go f (x * (1 # 2))) * 2)%Q).
      { apply QleT'_to_Qle. apply qeq_leT'. exact Hx3. }
      { exact Hfin. }
Qed.

(** The fuel adequacy. *)
Lemma mu0cos_l2c_fuel_adequate : forall x : Q,
  Qlt 0 x -> Qle x (q_pow 2 (mu0cos_l2c_fuel x)).
Proof.
  intros x Hx. unfold mu0cos_l2c_fuel. rewrite mu0cos_q_pow_two_make.
  apply (Qle_trans x (Qnum x # 1)%Q).
  - exact (mu0cos_qle_num_prop x Hx).
  - unfold Qle. cbn [Qnum Qden]. rewrite !Z.mul_1_r.
    apply Z.le_trans with (Z.of_nat (2 ^ Z.to_nat (Z.abs (Qnum x)))).
    + apply Z.le_trans with (Z.of_nat (Z.to_nat (Z.abs (Qnum x)))).
      * rewrite Z2Nat.id by apply Z.abs_nonneg.
        destruct (Qnum x) as [|p|p]; cbn [Z.abs]; lia.
      * apply Nat2Z.inj_le. apply mu0cos_nat_pow2_ge.
    + apply Nat2Z.inj_le.
      apply Nat.pow_le_mono_r; [apply Nat.neq_succ_0 | apply Nat.le_succ_diag_r].
Qed.

Definition mu0cos_log2_ceil (x : Q) : nat := mu0cos_l2c_go (mu0cos_l2c_fuel x) x.

Lemma mu0cos_log2_ceil_spec : forall x : Q,
  Qlt 0 x -> Qle x (q_pow 2 (mu0cos_log2_ceil x)).
Proof.
  intros x Hx. apply (mu0cos_l2c_go_spec (mu0cos_l2c_fuel x) x Hx).
  exact (mu0cos_l2c_fuel_adequate x Hx).
Qed.

(* ============================================================ *)
(* Section 3. The closed-form hitting bound (the rate layer)     *)
(* ============================================================ *)

(** The logarithmic window-depth modulus: the closed form
    [S (4 + ceil(log2(8/eps)))], the exponential-scale counterpart of
    the linear inverse [lw0m_modulus eps = S(ceil(5/eps))]. *)
Definition mu0cos_modulus (eps : Q) : nat :=
  Datatypes.S (4 + mu0cos_log2_ceil (8 / eps)%Q).

(** The undercut bound: the window family drops below [eps] at the
    modulus depth. *)
Lemma mu0cos_modulus_undercut_prop : forall eps : Q,
  Qlt 0 eps -> Qlt (mu0cos_e (mu0cos_modulus eps)) eps.
Proof.
  intros eps Heps. unfold mu0cos_modulus.
  assert (Hne0 : ~ eps == 0%Q) by (intro Hz; apply (Qlt_not_eq 0 eps Heps); exact (Qeq_sym _ _ Hz)).
  assert (Hdpos : Qlt 0 (8 * (/ eps))%Q).
  { apply (Qmult_lt_0_compat (8 # 1) (/ eps)).
    - unfold Qlt, Qnum, Qden; lia.
    - exact (mu0cos_qinv_pos_prop eps Heps). }
  pose proof (mu0cos_log2_ceil_spec (8 * (/ eps))%Q Hdpos) as Hspec.
  pose proof (mu0cos_two_half_mul_prop (mu0cos_log2_ceil (8 * (/ eps))%Q)) as Htwo.
  assert (Hne : ~ (q_pow 2 (mu0cos_log2_ceil (8 * (/ eps))%Q) == 0)%Q).
  { intro Hz. assert (Hp : Qlt 0 (q_pow 2 (mu0cos_log2_ceil (8 * (/ eps))%Q))).
    { apply (mu0cos_q_pow_pos_prop 2 _). unfold Qlt, Qnum, Qden; lia. }
    apply (Qlt_not_eq 0 _ Hp). symmetry. rewrite Hz. reflexivity. }
  assert (Hrec : q_pow (1 # 2) (mu0cos_log2_ceil (8 * (/ eps))%Q)
                 == (/ q_pow 2 (mu0cos_log2_ceil (8 * (/ eps))%Q))%Q).
  { apply (proj1 (Qmult_inj_l _ _ _ Hne)).
    rewrite Htwo, (Qmult_inv_r _ Hne). reflexivity. }
  assert (Hinv : Qle (/ q_pow 2 (mu0cos_log2_ceil (8 * (/ eps))%Q))
                   (eps * (1 # 8))%Q).
  { pose proof (mu0cos_qinv_le_prop (8 * (/ eps))%Q
                  (q_pow 2 (mu0cos_log2_ceil (8 * (/ eps))%Q)) Hdpos Hspec) as H0.
    assert (Hdne : ~ ((8 * (/ eps))%Q == 0)%Q)
      by (intro Hz; apply (Qlt_not_eq 0 _ Hdpos); symmetry; rewrite Hz; reflexivity).
    assert (Hne8 : ~ (8 # 1)%Q == 0%Q)
      by (intro Hz; unfold Qeq in Hz; cbn in Hz; lia).
    assert (Hie : ((/ eps) * eps)%Q == 1%Q)
      by (rewrite <- (Qmult_comm eps (/ eps)); apply (Qmult_inv_r eps Hne0)).
    assert (Hid : (/ (8 * (/ eps)))%Q == (eps * (1 # 8))%Q).
    { apply (proj1 (Qmult_inj_l _ _ _ Hdne)).
      rewrite (Qmult_inv_r _ Hdne). symmetry.
      assert (Hc8 : (1 # 8)%Q == (/ 8)%Q) by reflexivity.
      rewrite Hc8.
      rewrite <- (Qmult_assoc 8 (/ eps) (eps * (/ 8))%Q).
      rewrite (Qmult_assoc (/ eps) eps (/ 8)).
      rewrite Hie, Qmult_1_l, (Qmult_inv_r (8 # 1) Hne8). reflexivity. }
    rewrite Hid in H0. exact H0. }
  set (L := mu0cos_log2_ceil (8 * (/ eps))%Q) in *.
  assert (Hhalf : q_pow (1 # 2) 5 == (1 # 32)%Q) by reflexivity.
  assert (Hlt321 : ((1 # 32) < 1)%Q) by (unfold Qlt, Qnum, Qden; lia).
  assert (Heq1 : mu0cos_e (Datatypes.S (4 + L))
                 == ((/ q_pow 2 L) * (1 # 4))%Q).
  { unfold mu0cos_e.
    replace (Datatypes.S (4 + L)) with (5 + L)%nat by lia.
    rewrite (mu0cos_q_pow_add_prop (1 # 2) 5 L), Hhalf, Hrec.
    assert (Hc1 : 8 * ((1 # 32) * / q_pow 2 L) == ((/ q_pow 2 L) * (1 # 4))%Q) by ring.
    exact Hc1. }
  assert (Hle1 : Qle ((/ q_pow 2 L) * (1 # 4)) ((eps * (1 # 8)) * (1 # 4))%Q).
  { assert (Hq4 : Qle 0 (1 # 4)%Q) by (unfold Qle, Qnum, Qden; lia).
    exact (Qmult_le_compat_r (/ q_pow 2 L) (eps * (1 # 8))%Q (1 # 4) Hinv Hq4). }
  assert (Hlt1 : Qlt ((eps * (1 # 8)) * (1 # 4))%Q eps).
  { assert (Hc2 : ((eps * (1 # 8)) * (1 # 4))%Q == (eps * (1 # 32))%Q) by ring.
    assert (Hc3 : (eps * (1 # 32))%Q == ((1 # 32) * eps)%Q) by ring.
    assert (Ht2 : eps == (1 * eps)%Q) by ring.
    pose proof (Qmult_lt_compat_r (1 # 32) 1 eps Heps Hlt321) as H0.
    rewrite <- Hc3, <- Hc2, <- Ht2 in H0. exact H0. }
  rewrite <- Heq1 in Hle1.
  exact (Qle_lt_trans _ _ _ Hle1 Hlt1).
Qed.

(** The per-margin closed-form hitting bound (the rate-layer
    statement): the window family undercuts [eps] at a level bounded
    by the logarithmic closed form. *)
Theorem mu0_cos_hitting_bound : forall eps : Q,
  QltT 0 eps ->
  sigT (fun n0 : nat => And (QltT (mu0cos_e n0) eps) (NatLe n0 (mu0cos_modulus eps))).
Proof.
  intros eps Heps. exists (mu0cos_modulus eps). split.
  - apply Qlt_to_QltT.
    exact (mu0cos_modulus_undercut_prop eps (QltT_to_Qlt 0 eps Heps)).
  - unfold NatLe. rewrite Nat.leb_refl. apply id_refl.
Qed.

(** The per-rational packaging: the kernel margin of [q] (the
    Leibniz-chain distance lower bound, consumed from
    [leibsep_q_kernel]) together with the closed-form hitting level
    for that margin's concrete value. *)
Theorem mu0_cos_q_hitting_bound : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (sigT (fun N : nat =>
      And (forall m : nat, NatLe N m -> QltT c (Qabs (lw0m_xL m - q)%Q))
      (sigT (fun n0 : nat =>
        And (QltT (mu0cos_e n0) c) (NatLe n0 (mu0cos_modulus c))))))).
Proof.
  intros q.
  destruct (leibsep_q_kernel pi_sep_seed_halfwin_prop pi_sep_seed_dres_prop
             pi_sep_seed_dcos_prop q) as [c [Hc0 [N HN]]].
  exists c. split.
  - exact Hc0.
  - exists N. split.
    + exact HN.
    + destruct (mu0_cos_hitting_bound c Hc0) as [n0 [Hhit Hbnd]].
      exists n0. split.
      * exact Hhit.
      * exact Hbnd.
Defined.

(* ============================================================ *)
(* Section 4. Window exclusion and the second engine instance    *)
(* ============================================================ *)

(** The guarded [Q] chain for the exponential family (the mirror of
    [pi_sep_escape_conj_prop] of [PiSeparation]). *)
Lemma mu0cos_escape_conj_prop : forall (q c : Q) (n0 : nat),
  Qlt (mu0cos_e n0) c ->
  Qlt c (Qabs (lw0m_xL (2 ^ n0) - q)%Q) ->
  Qlt (mu0cos_e n0) (Qabs (q - lw0m_xL (2 ^ n0))%Q).
Proof.
  intros q c n0 He Hmargin.
  rewrite (piL_qabs_sym q (lw0m_xL (2 ^ n0))).
  exact (Qlt_trans (mu0cos_e n0) c (Qabs (lw0m_xL (2 ^ n0) - q)%Q) He Hmargin).
Qed.

(** Window exclusion (the margin-consumption leg): at a depth where
    the window family has undercut the margin and the read point is
    past the kernel threshold, the level-[n] window excludes [q]. *)
Lemma mu0cos_window_exclusion_prop : forall (q c : Q) (N n : nat),
  (forall m : nat, NatLe N m -> QltT c (Qabs (lw0m_xL m - q)%Q)) ->
  (N <= 2 ^ n)%nat ->
  QltT (mu0cos_e n) c ->
  QltT (mu0cos_e n) (Qabs (q - lw0m_xL (2 ^ n)%nat)%Q).
Proof.
  intros q c N n HN Hdepth Hunder.
  apply Qlt_to_QltT. rewrite (piL_qabs_sym q (lw0m_xL (2 ^ n))).
  apply (Qlt_trans (mu0cos_e n) c (Qabs (lw0m_xL (2 ^ n) - q)%Q)).
  - apply QltT_to_Qlt. exact Hunder.
  - apply QltT_to_Qlt. apply (HN (2 ^ n)%nat).
    exact (NatLe_lift N (2 ^ n)%nat Hdepth).
Qed.

(** The engine mounting piece at the exponential family: the second
    window-family instance of the escape-window criterion (the
    witness depth is the maximum of the kernel threshold and the
    closed-form modulus; the coupling leg is pure arithmetic). *)
Definition mu0cos_escape_window_pi_prop : creal_escape_window pi_leibniz mu0cos_e.
Proof.
  intros q.
  destruct (leibsep_q_kernel pi_sep_seed_halfwin_prop pi_sep_seed_dres_prop
             pi_sep_seed_dcos_prop q) as [c [Hc0 [N HN]]].
  exists (Nat.max N (mu0cos_modulus c)).
  split.
  - apply mu0cos_e_coupling_prop.
  - replace (seq pi_leibniz (Z.opp (Z.of_nat (Nat.max N (mu0cos_modulus c)))))
      with (pi_leibniz_seq (Z.opp (Z.of_nat (Nat.max N (mu0cos_modulus c)))))
      by reflexivity.
    rewrite (pi_leibniz_seq_negtail (Nat.max N (mu0cos_modulus c))).
    apply (mu0cos_escape_conj_prop q c (Nat.max N (mu0cos_modulus c))).
    + apply (Qle_lt_trans (mu0cos_e (Nat.max N (mu0cos_modulus c)))
               (mu0cos_e (mu0cos_modulus c)) c).
      * exact (mu0cos_e_antitone_prop (mu0cos_modulus c)
                 (Nat.max N (mu0cos_modulus c)) (Nat.le_max_r N (mu0cos_modulus c))).
      * exact (mu0cos_modulus_undercut_prop c (QltT_to_Qlt 0 c Hc0)).
    + apply QltT_to_Qlt. apply (HN (2 ^ Nat.max N (mu0cos_modulus c))%nat).
      exact (NatLe_lift N (2 ^ Nat.max N (mu0cos_modulus c))%nat
               (Nat.le_trans N (Nat.max N (mu0cos_modulus c))
                  (2 ^ Nat.max N (mu0cos_modulus c)) (Nat.le_max_l N (mu0cos_modulus c))
                  (mu0cos_nat_pow2_ge (Nat.max N (mu0cos_modulus c))))).
Defined.

(* ============================================================ *)
(* Section 5. The decidable separator and machine-checked samples *)
(* ============================================================ *)

(** The window separator on the Leibniz dyadic read points: [q]
    escapes the level-[n] window exactly when the read-point distance
    exceeds the window width (the same shape as the [sqrt2] instance
    of [PiSepSearch]). *)
Definition mu0cos_sep_dec (q : Q) (n : nat) : bool :=
  negb (Qle_bool (Qabs (q - lw0m_xL (2 ^ n)%nat)%Q) (mu0cos_e n)).

(* Window-family sample points. *)
Definition mu0cos_window_e0_val : Id (Qeq_bool (mu0cos_e 0) (8 # 1)) true.
Proof. vm_compute. exact id_refl. Qed.

Definition mu0cos_window_e3_val : Id (Qeq_bool (mu0cos_e 3) (1 # 1)) true.
Proof. vm_compute. exact id_refl. Qed.

Definition mu0cos_window_e4_val : Id (Qeq_bool (mu0cos_e 4) (1 # 2)) true.
Proof. vm_compute. exact id_refl. Qed.

(* The bounded-search samples (22/7 fires at level 13; 355/113 does
   not fire within budget 12) are transcribed by the Eval lines below
   rather than stated as constants: kernel re-checking of these
   [nsep_find] computations is prohibitively costly.  [mu0cos_sep_dec]
   stays transparent, so the values are independently recomputable. *)

Eval vm_compute in (nsep_find mu0cos_sep_dec (22 # 7) 0%nat 20%nat).
Eval vm_compute in (nsep_find mu0cos_sep_dec (355 # 113) 0%nat 12%nat).

Separate Extraction mu0cos_e mu0cos_sep_dec mu0cos_l2c_go mu0cos_l2c_fuel
  mu0cos_log2_ceil mu0cos_modulus nsep_find.

(* Assumption audit for the statements of this file. *)
Print Assumptions mu0cos_e_coupling_prop.
Print Assumptions mu0cos_log2_ceil_spec.
Print Assumptions mu0cos_modulus_undercut_prop.
Print Assumptions mu0_cos_hitting_bound.
Print Assumptions mu0_cos_q_hitting_bound.
Print Assumptions mu0cos_window_exclusion_prop.
Print Assumptions mu0cos_escape_window_pi_prop.
