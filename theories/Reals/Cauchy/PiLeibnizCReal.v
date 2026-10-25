(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)

(** * Native [CReal] construction of the Leibniz series for [pi]

    Mission.  This file gives the native [CReal] construction of the
    Leibniz series for [pi].  It is the master definition site of the
    [lp_]/[lw0m_]-family sampling sequences: the trivial rational forms
    [lp_a]/[lp_pair]/[lp_odd]/[lp_four] (inlined), the [pi_L] projection
    sequence [lw0m_xL], and the [nat]->[Z] linearization with the working
    layer that closes the [Q] order facts; the bridge layer, the
    interleaved tail bounds, the [CReal] record main jump, and the
    unified window vanishing complete the file in this order.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Qpower],
    [ZArith.ZArith], [Qround], and [ConstructiveCauchyReals]; this
    development, [PiWindowCore].  Order arithmetic goes through the
    direct [QArith] lemma chain, with no dependency on an external
    decision procedure.

    References.  This development, [S10_KVQuantTrig.v] (the
    inlined trivial rational forms of the [lp] family); this development,
    [LW0MLicBridge.v] (the migration
    sources of [lw0m_xL] and of the vanishing instance); this development,
    [LW0LeibWindow.v] (the migration source of the vanishing
    interface); this development, [maps/modulus-conversion-design.md],
    Section 3 (the family of fourteen conversion lemmas); this
    development, [ConstructiveCauchyRealsSep.v] at [:60-:87] and
    [:113-:157] (the engine styles followed by the resolution fuel and by
    the main jump).
    Statement-level migration provenance is maintained in
    [docs/statement-provenance.md]; citations in this file are by
    fully qualified name.

    Constructivity.  Statements at the [Set] level; assumption-free and
    fully proved, with no non-constructive principles; within proofs,
    [Qlt]/[Qle] occur only on the auxiliary-premise side; extractable.

    Build.  [rocq c -native-compiler no -q -Q . "" PiLeibnizCReal.v]
    compiles cleanly (exit 0); the first eight bytes of the artifact are
    [436f7121 00015ff4].

    This file is part of the rocq-pi-leibniz package; its interface
    may change in future releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Qpower.
From Stdlib Require Import ZArith.ZArith.
Require Import PiCompareT.
Require Import PiWindowCore.
From Stdlib Require Import Qround.
From Stdlib Require Import ConstructiveCauchyReals.

(* ================= Section 1. The [pi_L] sampling layer: the inlined [lp] family and [lw0m_xL]
   =================  *)

(** The odd terms [a_k := 1/(2k+1)] (trivial rational forms, inlined here rather than imported). *)
Definition lp_a (k : nat) : Q := Qdiv 1 (Qmake (Z.of_nat (2 * k + 1)) 1).

(** The even-odd pairing: [lp_pair j := a_{2j} - a_{2j+1}]. *)
Definition lp_pair (j : nat) : Q := (lp_a (2 * j) - lp_a (2 * j + 1))%Q.

(** Partial sums over the odd subsequence: [lp_odd m := lp_pair 0 + ... + lp_pair m]. *)
Fixpoint lp_odd (m : nat) : Q :=
  match m with
  | 0%nat => lp_pair 0
  | Datatypes.S p => (lp_odd p + lp_pair (Datatypes.S p))%Q
  end.

Definition lp_four : Q := (1 + 1 + 1 + 1)%Q.

(** The projection sequence of [pi_L] (the master definition; the same-named candidates of this
   development defer to this copy).  *)
Definition lw0m_xL (n : nat) : Q := lp_four * lp_odd n.

(** Canonical forms of [lp_a] at zero and at successors (the [Qdiv 1 (Qmake z 1)] shape closes
   definitionally; the [Pos] denominator normal form).  *)
Lemma piL_lp_a_0 : lp_a 0 == 1%Q.
Proof. reflexivity. Qed.

Lemma piL_lp_a_S : forall k : nat, lp_a (S k) == (1 # Pos.of_succ_nat (2 * k + 2))%Q.
Proof.
  intros k. unfold lp_a.
  replace (2 * S k + 1)%nat with (S (2 * k + 2))
    by (rewrite Nat.mul_succ_r, Nat.add_1_r; reflexivity).
  reflexivity.
Qed.

(* ================= Section 2. [nat]->[Z] linearization and the working layer that closes the [Q]
   order facts =================  *)

(** [Z.of_nat] is monotone ([<=] on [nat] lifts to [<=] on [Z]). *)
Lemma znat_le_mono_prop : forall n m : nat, (n <= m)%nat -> (Z.of_nat n <= Z.of_nat m)%Z.
Proof. intros n m H. exact (proj1 (Nat2Z.inj_le n m) H). Qed.


(** [Z.pos (Pos.of_succ_nat k)] equals [Z.of_nat k + 1] (the anchor for closing denominators lifted
   to [Z]).  *)
Lemma piL_pos_succ1_prop : forall k : nat, Z.pos (Pos.of_succ_nat k) = (Z.of_nat k + 1)%Z.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - cbn [Pos.of_succ_nat]. rewrite Pos2Z.inj_succ, Nat2Z.inj_succ, IH.
    unfold Z.succ. reflexivity.
Qed.

(** The [nat] power [2^n] is at least [1] (the fuel of the depth floor). *)
Lemma piL_nat_pow2_ge1_prop : forall n : nat, (1 <= 2 ^ n)%nat.
Proof.
  intros n. apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. discriminate.
Qed.

(* -- [Q] power bridge: [2^(-n)] equals [1/2^n] in [Pos] denominator normal form (the resolution
   anchor of the record side) --  *)

Lemma piL_qpow2_neq0_prop : ~ (2 == 0)%Q.
Proof. intro H. unfold Qeq in H. cbn in H. discriminate. Qed.

Lemma piL_qpow2_neg : forall n : nat,
  (2 ^ Z.opp (Z.of_nat n))%Q == (1 # Pos.of_succ_nat (2 ^ n - 1))%Q.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite Nat2Z.inj_succ. unfold Z.succ.
    assert (Hexp : Z.opp (Z.of_nat n + 1) = (Z.opp (Z.of_nat n) + -1)%Z) by ring.
    rewrite Hexp, (Qpower_plus 2 (Z.opp (Z.of_nat n)) (-1) piL_qpow2_neq0_prop).
    change (2 ^ (-1))%Q with (1 # 2)%Q.
    rewrite IH, (Nat.pow_succ_r 2 n (Nat.le_0_l n)).
    unfold Qeq. cbn [Qnum Qden Qmult Z.mul].
    repeat rewrite Pos2Z.inj_mul.
    repeat rewrite piL_pos_succ1_prop.
    repeat rewrite Nat2Z.inj_mul.
    repeat rewrite Nat2Z.inj_add.
    rewrite (Nat2Z.inj_sub (2 * 2 ^ n) 1 (piL_nat_pow2_ge1_prop (S n))).
    rewrite (Nat2Z.inj_sub (2 ^ n) 1 (piL_nat_pow2_ge1_prop n)).
    change (Z.of_nat 2) with 2%Z.
    change (Z.of_nat 1) with 1%Z.
    repeat rewrite Nat2Z.inj_mul.
    ring.
Qed.

(* -- Three bridges for nonnegative [Q] differences ([Qle 0 (b-a)], its converse, and order
   preservation of subtraction) --  *)

(** [a <= b] implies [0 <= b - a]. *)
Lemma qle_minus0_prop : forall a b : Q, Qle a b -> Qle 0 (b - a)%Q.
Proof.
  intros a b H.
  pose proof (Qplus_le_compat a b (- a) (- a) H (Qle_refl (- a))) as HH.
  assert (Heq1 : ((a + -a)%Q == 0)) by ring.
  assert (Heq2 : ((b + -a)%Q == b - a)) by ring.
  rewrite Heq1, Heq2 in HH. exact HH.
Qed.

(** [0 <= b - a] implies [a <= b]. *)
Lemma qle0_minus_prop : forall a b : Q, Qle 0 (b - a)%Q -> Qle a b.
Proof.
  intros a b H.
  pose proof (Qplus_le_compat 0 (b - a)%Q a a H (Qle_refl a)) as HH.
  assert (Heq1 : ((0 + a)%Q == a)) by ring.
  assert (Heq2 : (((b - a) + a)%Q == b)) by ring.
  rewrite Heq1, Heq2 in HH. exact HH.
Qed.

(** [x <= y] implies [x - z <= y - z]. *)
Lemma qle_minus_compat_prop : forall x y z : Q, Qle x y -> Qle (x - z) (y - z)%Q.
Proof.
  intros x y z H.
  pose proof (Qplus_le_compat x y (- z) (- z) H (Qle_refl (- z))) as HH.
  assert (Heq1 : ((x + -z)%Q == x - z)) by ring.
  assert (Heq2 : ((y + -z)%Q == y - z)) by ring.
  rewrite Heq1, Heq2 in HH. exact HH.
Qed.

(** [x <= y] implies [w - y <= w - x] (antitone in the right subtrahend). *)
Lemma qle_rsub_antitone_prop : forall u v w : Q, Qle u v -> Qle (w - v) (w - u)%Q.
Proof.
  intros u v w H.
  pose proof (Qopp_le_compat u v H) as HH.
  pose proof (Qplus_le_compat (- v) (- u) w w HH (Qle_refl w)) as H2.
  assert (Heq1 : ((-v + w)%Q == w - v)) by ring.
  assert (Heq2 : ((-u + w)%Q == w - u)) by ring.
  rewrite Heq1, Heq2 in H2. exact H2.
Qed.


(* -- Two-sided closure through [Qabs] (direct chain on the stdlib [Qabs_pos]/[Qabs_neg]) -- *)

(** [0 <= x <= c] implies [Qabs x <= c]. *)
Lemma piL_qabs_le_nonneg_prop : forall x c : Q, Qle 0 x -> Qle x c -> Qle (Qabs x) c.
Proof.
  intros x c H0 H1. rewrite (Qabs_pos x H0). exact H1.
Qed.


(** [Qabs (x - y)] equals [Qabs (y - x)]. *)
Lemma piL_qabs_sym : forall x y : Q, Qabs ((x - y)%Q) == Qabs ((y - x)%Q).
Proof.
  intros x y.
  assert (Hr : ((x - y)%Q == - (y - x))) by ring.
  rewrite Hr. apply Qabs_opp.
Qed.

(* ================= Section 3. Index arithmetic (the [nat] order fuel of the interleaved tail
   bounds) =================  *)


(** Index lemma, first form: [2a <= 2b] implies [a <= b] (cancelling the positive doubling in [Z]). 
      *)
Lemma piL_even_le_prop : forall a b : nat, (2 * a <= 2 * b)%nat -> (a <= b)%nat.
Proof.
  intros a b H.
  apply (proj2 (Nat2Z.inj_le a b)).
  apply (proj2 (Z.mul_le_mono_pos_l (Z.of_nat a) (Z.of_nat b) 2 (Pos2Z.is_pos 2))).
  pose proof (proj1 (Nat2Z.inj_le (2 * a) (2 * b)) H) as Hz.
  rewrite !Nat2Z.inj_mul in Hz. exact Hz.
Qed.

(** Index lemma, second form: [2a <= 2b+1] implies [a <= b] (by contradiction on [b < a]: [2(b+1) <=
   2a <= 2b+1] contradicts [2b+1 < 2b+2]).  *)
Lemma piL_even_le_odd_prop : forall a b : nat, (2 * a <= 2 * b + 1)%nat -> (a <= b)%nat.
Proof.
  intros a b H.
  destruct (Nat.le_gt_cases b a) as [Hba | Hab].
  - destruct (Nat.eq_dec a b) as [Heq | Hne].
    + rewrite Heq. apply Nat.le_refl.
    + exfalso.
      assert (Hblt : (b < a)%nat).
      { destruct (Nat.lt_ge_cases b a) as [Hx | Hx].
        - exact Hx.
        - exfalso. apply Hne. apply Nat.le_antisymm.
          + exact Hx.
          + exact Hba. }
      assert (Hs : (b + 1 <= a)%nat)
        by (rewrite Nat.add_1_r; exact Hblt).
      pose proof (Nat.mul_le_mono_l (b + 1) a 2 Hs) as H1.
      replace (2 * (b + 1))%nat with (2 * b + 2)%nat in H1
        by (rewrite Nat.mul_add_distr_l; reflexivity).
      pose proof (Nat.le_trans _ _ _ H1 H) as H3.
      assert (H4 : (2 * b + 1 < 2 * b + 2)%nat).
      { apply (Nat.add_lt_mono_l 1 2 (2 * b)). apply Nat.lt_succ_diag_r. }
      exact (Nat.lt_irrefl _ (Nat.le_lt_trans _ _ _ H3 H4)).
  - exact (Nat.lt_le_incl _ _ Hab).
Qed.

(** Index lemma, third form: [2a+1 <= 2b] implies [a < b] (by contradiction on [b <= a], which would
   give [2a+1 <= 2a]).  *)
Lemma piL_odd_le_even_prop : forall a b : nat, (2 * a + 1 <= 2 * b)%nat -> (a < b)%nat.
Proof.
  intros a b H.
  destruct (Nat.le_gt_cases b a) as [Hba | Hab].
  - exfalso.
    pose proof (Nat.mul_le_mono_l b a 2 Hba) as H1.
    pose proof (Nat.le_trans _ _ _ H H1) as H2.
    assert (H3 : (2 * a + 0 < 2 * a + 1)%nat).
    { apply (Nat.add_lt_mono_l 0 1 (2 * a)). apply Nat.lt_0_succ. }
    rewrite Nat.add_0_r in H3.
    exact (Nat.lt_irrefl _ (Nat.le_lt_trans _ _ _ H2 H3)).
  - exact Hab.
Qed.

(** Index lemma, fourth form: [2a+1 <= 2b+1] implies [a <= b] (reduces to the second form). *)
Lemma piL_odd_le_odd_prop : forall a b : nat, (2 * a + 1 <= 2 * b + 1)%nat -> (a <= b)%nat.
Proof.
  intros a b H. apply piL_even_le_odd_prop.
  apply Nat.le_trans with (2 * a + 1)%nat.
  - apply Nat.le_add_r.
  - exact H.
Qed.

(* ============ Section 4. Interleaved tail bounds -- preinstalled: the squeeze closure cores
   ============  *)

(** Squeeze closure core, first form (same direction): [x <= y <= w] and [w - x == c] imply [Qabs (y
   - x) <= c].  *)
Lemma piL_sandwich_abs_prop : forall x y w c : Q,
  Qle x y -> Qle y w -> (w - x)%Q == c -> Qle (Qabs (y - x)) c.
Proof.
  intros x y w c Hxy Hyw Hwx.
  rewrite (Qabs_pos (y - x) (qle_minus0_prop _ _ Hxy)).
  rewrite <- Hwx. apply qle_minus_compat_prop. exact Hyw.
Qed.

(** Squeeze closure core, second form (reverse direction): the shape [y <= x <= w] -- [0 <= x - y]
   and [x - y <= x - w == c].  *)
Lemma piL_sandwich_abs_neg_prop : forall x y w c : Q,
  Qle y x -> Qle w y -> (x - w)%Q == c -> Qle (Qabs (x - y)) c.
Proof.
  intros x y w c Hyx Hwy Hxw.
  rewrite (Qabs_pos (x - y) (qle_minus0_prop y x Hyx)).
  rewrite <- Hxw. apply qle_rsub_antitone_prop. exact Hwy.
Qed.

(** Two small [Qmake] literal normal-form lemmas (alignment anchors of the main bridge; conversions
   at the [reflexivity] level).  *)
Lemma piL_qmult_make4 : forall (z : Z) (p : positive), (4 * (z # p))%Q == ((4 * z) # p).
Proof. intros z p. reflexivity. Qed.

Lemma piL_qopp_make : forall (z : Z) (p : positive), (- (z # p))%Q == ((- z) # p).
Proof. intros z p. reflexivity. Qed.

(** [lp_pair (S n)] shares its value with the even-odd pair of [t] terms (in [Qmake] denominator
   normal form; a stepping lemma of the main bridge; independent of the window file).  *)
Lemma piL_pair_val : forall n : nat,
  lp_four * lp_pair (S n)%nat
    == (4 # Pos.of_succ_nat (4 * n + 4))%Q + ((-4) # Pos.of_succ_nat (4 * n + 6))%Q.
Proof.
  intros n. unfold lp_pair.
  replace (2 * S n)%nat with (S (2 * n + 1))
    by (rewrite (Nat.mul_succ_r 2 n); symmetry; apply Nat.add_succ_r).
  replace (S (2 * n + 1) + 1)%nat with (S (2 * n + 2))
    by (rewrite (Nat.add_1_r (S (2 * n + 1))); f_equal;
        apply Nat.add_succ_r).
  rewrite (piL_lp_a_S (2 * n + 1)), (piL_lp_a_S (2 * n + 2)).
  replace (2 * (2 * n + 1) + 2)%nat with ((4 * n + 4)%nat)
    by (rewrite Nat.mul_add_distr_l, Nat.mul_assoc;
        change (2 * 2)%nat with (4%nat); change (2 * 1)%nat with (2%nat);
        rewrite <- Nat.add_assoc; reflexivity).
  replace (2 * (2 * n + 2) + 2)%nat with ((4 * n + 6)%nat)
    by (rewrite Nat.mul_add_distr_l, Nat.mul_assoc;
        change (2 * 2)%nat with (4%nat);
        rewrite <- Nat.add_assoc; reflexivity).
  assert (H4 : lp_four == 4%Q) by reflexivity.
  rewrite H4. unfold Qminus.
  rewrite (piL_qopp_make 1 (Pos.of_succ_nat (4 * n + 6))).
  rewrite (Qmult_plus_distr_r 4%Q (Qmake 1 (Pos.of_succ_nat (4 * n + 4)))
            ((-1) # Pos.of_succ_nat (4 * n + 6))%Q).
  rewrite (piL_qmult_make4 1 (Pos.of_succ_nat (4 * n + 4))).
  rewrite (piL_qmult_make4 (-1) (Pos.of_succ_nat (4 * n + 6))).
  reflexivity.
Qed.

(* ============ Section 5. Depth mirroring and [Q] closure (preinstalled; independent of the window
   file) ============  *)

(** Pointwise transport of [Qeq] into [Qlt] (a [Qeq] wrapper lemma cannot be
    [rewrite]-ed inside a [Qlt] goal -- the standing restriction of the [Q]
    tool layer); the proper name is the [QArith_base] [Proper] instance
    [Qlt_compat] in interleaved argument form [x x' proof y y' proof]. *)
Lemma piL_qlt_transport_prop : forall a b c : Q, Qlt a b -> b == c -> Qlt a c.
Proof. intros a b c H Hb. exact (proj1 (Qlt_compat a a (Qeq_refl a) b c Hb) H). Qed.

(** Strict [Z] order under translation: [z < z + 5] (the trivially-true core left after the [Q]
   closure scales through by the integer).  *)
Lemma piL_zlt_add5_prop : forall z : Z, (z < z + 5)%Z.
Proof.
  intros z.
  assert (H05 : (0 < 5)%Z) by (apply Z.ltb_lt; reflexivity).
  pose proof (proj1 (Z.add_lt_mono_l 0 5 z) H05) as H.
  rewrite Z.add_0_r in H. exact H.
Qed.

(** The [Q] closure: [4/(4*2^n+5) < 2^(-n)] (the resolution overrun, third
    step of the tail bound; the comparison runs on both sides in [Qmake]
    normal form, the [2^(-n)] side reformed through [piL_qlt_transport_prop] --
    the trivially-true core [4*2^n < 4*2^n+5] leaves no numeric corner
    cases). *)
Lemma piL_qclose_exp_prop : forall n : nat,
  Qlt (Qmake 4 (Pos.of_succ_nat (4 * 2 ^ n + 4))) (2 ^ Z.opp (Z.of_nat n))%Q.
Proof.
  intros n.
  apply (piL_qlt_transport_prop _ (Qmake 1 (Pos.of_succ_nat (2 ^ n - 1)))).
  - unfold Qlt. cbn [Qnum Qden].
    rewrite piL_pos_succ1_prop, piL_pos_succ1_prop.
    rewrite (Nat2Z.inj_sub (2 ^ n) 1 (piL_nat_pow2_ge1_prop n)).
    change (Z.of_nat 1) with 1%Z.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
    change (Z.of_nat 4) with 4%Z.
    apply (proj2 (Z.compare_lt_iff _ _)).
    assert (HL : (4 * (Z.of_nat (2 ^ n) - 1 + 1) = 4 * Z.of_nat (2 ^ n))%Z) by ring.
    assert (HR : (1 * (4 * Z.of_nat (2 ^ n) + 4 + 1)
                  = 4 * Z.of_nat (2 ^ n) + 5)%Z) by ring.
    rewrite HL, HR.
    apply piL_zlt_add5_prop.
  - apply Qeq_sym. exact (piL_qpow2_neg n).
Qed.

(** Depth mirroring: [pi_leibniz_depth k := 2^|k|] (a [nat] power; the exponent dives along the
   negative half-axis; a new design piece with no counterpart in the source tree).  *)
Definition pi_leibniz_depth (k : Z) : nat := (2 ^ (Z.to_nat (Z.abs k)))%nat.

(** The depth is always positive (the [2^n >= 1] fuel). *)
Lemma pi_leibniz_depth_pos_prop : forall k : Z, (1 <= pi_leibniz_depth k)%nat.
Proof. intros k. unfold pi_leibniz_depth. apply piL_nat_pow2_ge1_prop. Qed.

(** The depth floor on the negative half-axis ([p <= k < 0] implies [pi_leibniz_depth k <=
   pi_leibniz_depth p]; [Z.abs] reverses the order, and [Z2Nat] is monotone).  *)
Lemma pi_leibniz_depth_floor_prop : forall p k : Z, (k < 0)%Z -> (p <= k)%Z ->
  (pi_leibniz_depth k <= pi_leibniz_depth p)%nat.
Proof.
  intros p k Hk Hpk.
  assert (Hp0 : (p < 0)%Z) by (apply (Z.le_lt_trans p k 0 Hpk Hk)).
  unfold pi_leibniz_depth.
  apply Nat.pow_le_mono_r.
  - apply Nat.neq_succ_0.
  - assert (Hle : (Z.abs k <= Z.abs p)%Z).
    + rewrite (Z.abs_neq k) by (apply Z.lt_le_incl; exact Hk).
      rewrite (Z.abs_neq p) by (apply Z.lt_le_incl; exact Hp0).
      exact (proj1 (Z.opp_le_mono p k) Hpk).
    + exact (proj1 (Z2Nat.inj_le (Z.abs k) (Z.abs p) (Z.abs_nonneg k) (Z.abs_nonneg p)) Hle).
Qed.

(* ============ Section 6. Interleaved tail bounds (wired to the window file) ============ *)

(** The step difference: [leiblw_S (S i) - leiblw_S i == leiblw_t i]. *)
Lemma piL_step_diff : forall i : nat,
  (leiblw_S (S i) - leiblw_S i)%Q == leiblw_t i.
Proof.
  intros i. rewrite leiblw_S_step at 1. ring.
Qed.

(** Closed forms of the even branch: the shared-value shape of
    [leiblw_t (2n+2) = leiblw_t (2(n+1))] and
    [leiblw_t (S(2n+2)) = leiblw_t (2(n+1)+1)] ([4/(4n+5) - 4/(4n+7)]) --
    the alignment anchor between the main bridge and [lp_pair]. *)
Lemma piL_t_shift : forall n : nat,
  leiblw_t (2 * n + 2) + leiblw_t (S (2 * n + 2))%nat
    == (4 # Pos.of_succ_nat (4 * n + 4))%Q + ((-4) # Pos.of_succ_nat (4 * n + 6))%Q.
Proof.
  intros n.
  replace (2 * n + 2)%nat with ((2 * (n + 1))%nat)
    by (rewrite Nat.mul_add_distr_l; reflexivity).
  replace (S (2 * (n + 1)))%nat with ((2 * (n + 1) + 1)%nat)
    by (rewrite Nat.add_1_r; reflexivity).
  rewrite (leiblw_t_even (n + 1)), (leiblw_t_odd (n + 1)).
  replace (4 * (n + 1) + 2)%nat with ((4 * n + 6)%nat)
    by (rewrite Nat.mul_add_distr_l, <- Nat.add_assoc; reflexivity).
  replace (4 * (n + 1))%nat with ((4 * n + 4)%nat)
    by (rewrite Nat.mul_add_distr_l; reflexivity).
  reflexivity.
Qed.

(** The main bridge: [lp_four * lp_odd n == leiblw_S (2n+2)] -- the hinge of the whole file. *)
Lemma leiblw_xL_eq_S : forall n : nat,
  lp_four * lp_odd n == leiblw_S (2 * n + 2)%nat.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [lp_odd].
    rewrite Qmult_plus_distr_r, IH.
    replace (2 * S n + 2)%nat with (S (S (2 * n + 2)))
      by (symmetry; rewrite (Nat.mul_succ_r 2 n), Nat.add_succ_r,
          Nat.add_succ_r, Nat.add_0_r; reflexivity).
    rewrite leiblw_S_SS, piL_pair_val.
    rewrite <- (Qplus_assoc (leiblw_S (2 * n + 2)) (leiblw_t (2 * n + 2))
                (leiblw_t (S (2 * n + 2)))).
    rewrite (piL_t_shift n).
    reflexivity.
Qed.

(** [Qabs (leiblw_t (2a)) == leiblw_S (2a+1) - leiblw_S (2a)] and [Qabs (leiblw_t (2a+1)) ==
   leiblw_S (2a+1) - leiblw_S (2a+2)] (closed forms of both branches).  *)
Lemma piL_tail_even_abs : forall a : nat,
  (leiblw_S (2 * a + 1) - leiblw_S (2 * a))%Q == Qabs (leiblw_t (2 * a)).
Proof.
  intros a.
  replace (2 * a + 1)%nat with (S (2 * a)) by (rewrite Nat.add_1_r; reflexivity).
  rewrite (piL_step_diff (2 * a)). symmetry.
  apply leiblw_qabs_id_prop. apply (Qlt_le_weak 0%Q). apply QltT_to_Qlt. apply leiblw_t_even_pos_T.
Qed.

Lemma piL_tail_odd_abs : forall a : nat,
  (leiblw_S (2 * a + 1) - leiblw_S (2 * a + 2))%Q == Qabs (leiblw_t (2 * a + 1)).
Proof.
  intros a.
  assert (Hn : Qle (leiblw_t (2 * a + 1)) 0%Q)
    by (apply (Qlt_le_weak _ _); apply leiblw_t_odd_neg_prop).
  replace (2 * a + 2)%nat with (S (2 * a + 1)) by (symmetry; apply Nat.add_succ_r).
  rewrite (Qabs_neg _ Hn), <- (piL_step_diff (2 * a + 1)).
  ring.
Qed.

(** The four-case shells. *)
Lemma piL_tail_ee_prop : forall a b : nat, (a <= b)%nat ->
  Qle (Qabs ((leiblw_S (2 * b) - leiblw_S (2 * a))%Q)) (Qabs (leiblw_t (2 * a))).
Proof.
  intros a b Hab.
  apply (piL_sandwich_abs_prop (leiblw_S (2 * a)) (leiblw_S (2 * b))
                          (leiblw_S (2 * a + 1)) (Qabs (leiblw_t (2 * a)))).
  - apply QleT'_to_Qle. apply leiblw_mono_even_T. apply NatLe_lift. exact Hab.
  - apply (Qle_trans _ (leiblw_S (2 * b + 2))).
    + apply qle0_minus_prop. apply (Qlt_le_weak 0%Q). apply QltT_to_Qlt. apply leiblw_step_even_pos_T.
    + apply (Qle_trans _ (leiblw_S (2 * b + 1))).
      * apply QleT'_to_Qle. apply leiblw_interlace_T.
      * apply QleT'_to_Qle. apply leiblw_mono_odd_T. apply NatLe_lift. exact Hab.
  - apply piL_tail_even_abs.
Qed.

Lemma piL_tail_eo_prop : forall a b : nat, (a <= b)%nat ->
  Qle (Qabs ((leiblw_S (2 * b + 1) - leiblw_S (2 * a))%Q)) (Qabs (leiblw_t (2 * a))).
Proof.
  intros a b Hab.
  apply (piL_sandwich_abs_prop (leiblw_S (2 * a)) (leiblw_S (2 * b + 1))
                          (leiblw_S (2 * a + 1)) (Qabs (leiblw_t (2 * a)))).
  - apply (Qle_trans _ (leiblw_S (2 * b))).
    + apply QleT'_to_Qle. apply leiblw_mono_even_T. apply NatLe_lift. exact Hab.
    + apply qle0_minus_prop. apply (Qlt_le_weak 0%Q).
      replace (2 * b + 1)%nat with (S (2 * b)) by (rewrite Nat.add_1_r; reflexivity).
      rewrite (piL_step_diff (2 * b)). apply QltT_to_Qlt. apply leiblw_t_even_pos_T.
  - apply QleT'_to_Qle. apply leiblw_mono_odd_T. apply NatLe_lift. exact Hab.
  - apply piL_tail_even_abs.
Qed.

Lemma piL_tail_oe_prop : forall a b : nat, (a < b)%nat ->
  Qle (Qabs ((leiblw_S (2 * b) - leiblw_S (2 * a + 1))%Q)) (Qabs (leiblw_t (2 * a + 1))).
Proof.
  intros a b Hab.
  rewrite (piL_qabs_sym (leiblw_S (2 * b)) (leiblw_S (2 * a + 1))).
  apply (piL_sandwich_abs_neg_prop (leiblw_S (2 * a + 1)) (leiblw_S (2 * b))
                              (leiblw_S (2 * a + 2)) (Qabs (leiblw_t (2 * a + 1)))).
  - apply (Qle_trans _ (leiblw_S (2 * b + 1))).
    + apply qle0_minus_prop. apply (Qlt_le_weak 0%Q).
      replace (2 * b + 1)%nat with (S (2 * b)) by (rewrite Nat.add_1_r; reflexivity).
      rewrite (piL_step_diff (2 * b)). apply QltT_to_Qlt. apply leiblw_t_even_pos_T.
    + apply QleT'_to_Qle. apply leiblw_mono_odd_T. apply NatLe_lift. exact (Nat.lt_le_incl _ _ Hab).
  - replace (2 * a + 2)%nat with (2 * S a)%nat
      by (rewrite (Nat.mul_succ_r 2 a); reflexivity).
    apply QleT'_to_Qle. apply leiblw_mono_even_T. apply NatLe_lift. exact Hab.
  - apply piL_tail_odd_abs.
Qed.

Lemma piL_tail_oo_prop : forall a b : nat, (a <= b)%nat ->
  Qle (Qabs ((leiblw_S (2 * b + 1) - leiblw_S (2 * a + 1))%Q)) (Qabs (leiblw_t (2 * a + 1))).
Proof.
  intros a b Hab.
  rewrite (piL_qabs_sym (leiblw_S (2 * b + 1)) (leiblw_S (2 * a + 1))).
  apply (piL_sandwich_abs_neg_prop (leiblw_S (2 * a + 1)) (leiblw_S (2 * b + 1))
                              (leiblw_S (2 * a + 2)) (Qabs (leiblw_t (2 * a + 1)))).
  - apply QleT'_to_Qle. apply leiblw_mono_odd_T. apply NatLe_lift. exact Hab.
  - apply (Qle_trans _ (leiblw_S (2 * S b))).
    + replace (2 * a + 2)%nat with (2 * S a)%nat
        by (rewrite (Nat.mul_succ_r 2 a); reflexivity).
      apply QleT'_to_Qle. apply leiblw_mono_even_T. apply NatLe_lift. apply (proj1 (Nat.succ_le_mono a b)). exact Hab.
    + replace (2 * S b)%nat with (2 * b + 2)%nat
        by (rewrite (Nat.mul_succ_r 2 b); reflexivity).
      apply QleT'_to_Qle. apply leiblw_interlace_T.
  - apply piL_tail_odd_abs.
Qed.

(** The interleaved tail-bound main lemma: [Qabs (leiblw_S k - leiblw_S n) <= Qabs (leiblw_t n)] (a
   four-case squeeze; proved anew, with no precedent case lemmas).  *)
Lemma leiblw_S_tail_bound_prop : forall n k : nat, (n <= k)%nat ->
  Qle (Qabs ((leiblw_S k - leiblw_S n)%Q)) (Qabs (leiblw_t n)).
Proof.
  intros n k Hnk.
  destruct (leiblw_par_decomp_prop n) as [[a Ha]|[a Ha]];
  destruct (leiblw_par_decomp_prop k) as [[b Hb]|[b Hb]]; subst.
  - apply piL_tail_ee_prop. apply piL_even_le_prop. exact Hnk.
  - apply piL_tail_eo_prop. apply piL_even_le_odd_prop. exact Hnk.
  - apply piL_tail_oe_prop. apply piL_odd_le_even_prop. exact Hnk.
  - apply piL_tail_oo_prop. apply piL_odd_le_odd_prop. exact Hnk.
Qed.

(** Shared by both legs: [D <= d] implies [Qabs (leiblw_S (2D+2) - leiblw_S (2d+2)) <= Qabs
   (leiblw_t (2D+2))].  *)
Lemma piL_seq_pair_bound_prop : forall a b : nat, (a <= b)%nat ->
  Qle (Qabs ((leiblw_S (2 * a + 2) - leiblw_S (2 * b + 2))%Q))
      (Qabs (leiblw_t (2 * a + 2))).
Proof.
  intros a b Hab.
  rewrite (piL_qabs_sym (leiblw_S (2 * a + 2)) (leiblw_S (2 * b + 2))).
  apply (leiblw_S_tail_bound_prop (2 * a + 2) (2 * b + 2)).
  apply Nat.add_le_mono.
  - apply Nat.mul_le_mono_l. exact Hab.
  - apply Nat.le_refl.
Qed.

(* ============ Section 7. Depth sampling and the main convergence (the [CReal] record main jump)
   ============  *)

(** The sampling sequence of [pi_L]: exponential depth mirroring on the negative half-axis
   ([pi_leibniz_seq k := leiblw_S (2*2^|k|+2)]).  *)
Definition pi_leibniz_seq (k : Z) : Q :=
  leiblw_S (2 * pi_leibniz_depth k + 2)%nat.

(** The read-off bridge: [pi_leibniz_seq (-n) == lp_four * lp_odd (2^n)] (the negative tail lands
   definitionally).  *)
Lemma pi_leibniz_seq_negtail : forall n : nat,
  pi_leibniz_seq (Z.opp (Z.of_nat n)) == lp_four * lp_odd (2 ^ n)%nat.
Proof.
  intros n. unfold pi_leibniz_seq, pi_leibniz_depth.
  rewrite Z.abs_opp, (Z.abs_eq (Z.of_nat n) (Nat2Z.is_nonneg n)), Nat2Z.id.
  rewrite <- leiblw_xL_eq_S. reflexivity.
Qed.

(** Closed form of the even branch of [t] in the [+2] index form: [leiblw_t (2m+2) == 4/(4m+5)] --
   aligned with the denominator normal form of the [Q] closure.  *)
Lemma piL_t_2p2_even : forall m : nat,
  leiblw_t (2 * m + 2) == (4 # Pos.of_succ_nat (4 * m + 4))%Q.
Proof.
  intros m. replace (2 * m + 2)%nat with (2 * S m)%nat
    by (symmetry; rewrite (Nat.mul_succ_r 2 m); reflexivity).
  rewrite (leiblw_t_even (S m)).
  replace (4 * S m)%nat with ((4 * m + 4)%nat)
    by (rewrite (Nat.mul_succ_r 4 m); reflexivity).
  reflexivity.
Qed.

(** The antitone core of the even branch of [t] (in the [2j] form): [i <= j] implies [Qabs (leiblw_t
   (2j)) <= Qabs (leiblw_t (2i))].  *)
Lemma piL_t_even_antitone_prop : forall i j : nat, (i <= j)%nat ->
  Qle (Qabs (leiblw_t (2 * j))) (Qabs (leiblw_t (2 * i))).
Proof.
  intros i j Hij.
  rewrite (leiblw_qabs_id_prop (leiblw_t (2 * j))
            (Qlt_le_weak 0%Q _ (leiblw_t_even_pos_prop j))).
  rewrite (leiblw_qabs_id_prop (leiblw_t (2 * i))
            (Qlt_le_weak 0%Q _ (leiblw_t_even_pos_prop i))).
  rewrite (leiblw_t_even j), (leiblw_t_even i).
  apply (proj2 (leiblw_qmake_le_prop 4 4
            (Pos.of_succ_nat (4 * j)) (Pos.of_succ_nat (4 * i)))).
  rewrite piL_pos_succ1_prop, piL_pos_succ1_prop.
  apply (proj1 (Z.mul_le_mono_pos_l (Z.of_nat (4*i) + 1) (Z.of_nat (4*j) + 1) 4
            (Pos2Z.is_pos 4))).
  apply (Zplus_le_compat_r (Z.of_nat (4*i)) (Z.of_nat (4*j)) 1).
  apply znat_le_mono_prop. apply Nat.mul_le_mono_l. exact Hij.
Qed.

(** The even branch of [t] is antitone in the [+2] index form: [i <= j] implies [Qabs (leiblw_t
   (2j+2)) <= Qabs (leiblw_t (2i+2))].  *)
Lemma piL_tail2_antitone_prop : forall i j : nat, (i <= j)%nat ->
  Qle (Qabs (leiblw_t (2 * j + 2))) (Qabs (leiblw_t (2 * i + 2))).
Proof.
  intros i j Hij.
  replace (2 * i + 2)%nat with (2 * S i)%nat
    by (symmetry; rewrite (Nat.mul_succ_r 2 i); reflexivity).
  replace (2 * j + 2)%nat with (2 * S j)%nat
    by (symmetry; rewrite (Nat.mul_succ_r 2 j); reflexivity).
  apply (piL_t_even_antitone_prop (S i) (S j)).
  apply (proj1 (Nat.succ_le_mono i j)). exact Hij.
Qed.

(** The resolution overrun: [Qabs (leiblw_t (2*2^n+2)) < 2^(-n)] (the trivially-true core [4*2^n <
   4*2^n+5]).  *)
Lemma piL_tail2_qclose_prop : forall n : nat,
  Qlt (Qabs (leiblw_t (2 * 2 ^ n + 2))) (2 ^ Z.opp (Z.of_nat n))%Q.
Proof.
  intros n.
  assert (Hp0 : Qlt 0%Q (4 # Pos.of_succ_nat (4 * 2 ^ n + 4))%Q)
    by (unfold Qlt; cbn; reflexivity).
  rewrite piL_t_2p2_even, (leiblw_qabs_id_prop _ (Qlt_le_weak 0%Q _ Hp0)).
  apply piL_qclose_exp_prop.
Qed.

(** The [Q] power floor: [0 <= z] implies [1 <= 2^z] (the resolution fuel of the [k >= 0] branch; a
   miniature of the engine lines [:60-:87]).  *)
Lemma piL_qpow2_ge1_prop : forall z : Z, (0 <= z)%Z -> Qle 1 (2 ^ z)%Q.
Proof.
  intros z Hz.
  replace z with (Z.of_nat (Z.to_nat z)) by (apply Z2Nat.id; exact Hz).
  induction (Z.to_nat z) as [|m IH].
  - apply Qle_refl.
  - assert (Hstep : (2 ^ Z.of_nat (S m))%Q == ((2 ^ Z.of_nat m) * (2 ^ 1))%Q).
    { replace (Z.of_nat (S m))%Z with (Z.of_nat m + 1)%Z
        by (rewrite Nat2Z.inj_succ; reflexivity).
      apply Qpower_plus. exact piL_qpow2_neq0_prop. }
    assert (H02 : Qle 0 2) by (unfold Qle; cbn; apply Z.leb_le; reflexivity).
    assert (H12 : Qle 1 2) by (unfold Qle; cbn; apply Z.leb_le; reflexivity).
    pose proof (Qmult_le_compat_r 1 (2 ^ Z.of_nat m) 2 IH H02) as HM1.
    rewrite Qmult_1_l in HM1.
    rewrite Hstep.
    exact (Qle_trans _ _ _ H12 HM1).
Qed.

(** Resolution on the [k < 0] branch: [2^n <= dp] implies [Qabs (leiblw_t (2*dp+2)) < 2^(-n)]. *)
Lemma piL_cauchy_neg_prop : forall (n dp : nat), (2 ^ n <= dp)%nat ->
  Qlt (Qabs (leiblw_t (2 * dp + 2))) (2 ^ Z.opp (Z.of_nat n))%Q.
Proof.
  intros n dp Hdn.
  apply (Qle_lt_trans _ (Qabs (leiblw_t (2 * 2 ^ n + 2)))).
  - apply piL_tail2_antitone_prop. exact Hdn.
  - apply piL_tail2_qclose_prop.
Qed.

(** Resolution on the [k >= 0] branch: [1 <= dp] implies [Qabs (leiblw_t (2*dp+2)) < 1] (sharpened
   to [1/2] in use).  *)
Lemma piL_cauchy_pos_prop : forall dp : nat, (1 <= dp)%nat ->
  Qlt (Qabs (leiblw_t (2 * dp + 2))) 1%Q.
Proof.
  intros dp Hdp1.
  assert (Hp08 : Qlt 0%Q (4 # Pos.of_succ_nat (4 * 1 + 4))%Q)
    by (unfold Qlt; cbn; reflexivity).
  assert (Hlt08 : Qlt (4 # Pos.of_succ_nat (4 * 1 + 4)) 1%Q)
    by (unfold Qlt; cbn; reflexivity).
  pose proof (piL_tail2_antitone_prop 1 dp Hdp1) as Hanti.
  rewrite (piL_t_2p2_even 1) in Hanti.
  rewrite (leiblw_qabs_id_prop _ (Qlt_le_weak 0%Q _ Hp08)) in Hanti.
  exact (Qle_lt_trans _ _ _ Hanti Hlt08).
Qed.

(** The main jump: [pi_leibniz_seq] is Cauchy (uniform tail control over all of [Z]) -- the flagship
   delivery, proved in the named-chain style of the engine lines [:113-:157].  *)
Lemma pi_leibniz_cauchy : QCauchySeq pi_leibniz_seq.
Proof.
  intros k p q Hp Hq.
  unfold pi_leibniz_seq.
  destruct (Z.lt_ge_cases k 0) as [Hk0 | Hk0].
  - (* k < 0: both depths are at least [2^|k|]; the smaller depth squeezes. *)
    destruct (Nat.le_gt_cases (pi_leibniz_depth p) (pi_leibniz_depth q)) as [Hle | Hgt].
    + assert (Hr0 : Z.of_nat (Z.to_nat (Z.abs k)) = Z.opp k).
      { rewrite (Z2Nat.id (Z.abs k) (Z.abs_nonneg k)).
        exact (Z.abs_neq k (Z.lt_le_incl _ _ Hk0)). }
      pose proof (piL_seq_pair_bound_prop (pi_leibniz_depth p) (pi_leibniz_depth q) Hle) as Hb.
      pose proof (piL_cauchy_neg_prop (Z.to_nat (Z.abs k)) (pi_leibniz_depth p)
                    (pi_leibniz_depth_floor_prop p k Hk0 Hp)) as Hr.
      rewrite Hr0, Z.opp_involutive in Hr.
      exact (Qle_lt_trans _ _ _ Hb Hr).
    + assert (Hr0 : Z.of_nat (Z.to_nat (Z.abs k)) = Z.opp k).
      { rewrite (Z2Nat.id (Z.abs k) (Z.abs_nonneg k)).
        exact (Z.abs_neq k (Z.lt_le_incl _ _ Hk0)). }
      rewrite (piL_qabs_sym (leiblw_S (2 * pi_leibniz_depth p + 2))
                (leiblw_S (2 * pi_leibniz_depth q + 2))).
      pose proof (piL_seq_pair_bound_prop (pi_leibniz_depth q) (pi_leibniz_depth p)
                    (Nat.lt_le_incl _ _ Hgt)) as Hb.
      pose proof (piL_cauchy_neg_prop (Z.to_nat (Z.abs k)) (pi_leibniz_depth q)
                    (pi_leibniz_depth_floor_prop q k Hk0 Hq)) as Hr.
      rewrite Hr0, Z.opp_involutive in Hr.
      exact (Qle_lt_trans _ _ _ Hb Hr).
  - (* k >= 0: the value-range difference is at most [1/2] < [1] <= [2^k]. *)
    assert (H1 : Qle 1 (2 ^ k)%Q) by (apply piL_qpow2_ge1_prop; exact Hk0).
    destruct (Nat.le_gt_cases (pi_leibniz_depth p) (pi_leibniz_depth q)) as [Hle | Hgt].
    + pose proof (piL_seq_pair_bound_prop (pi_leibniz_depth p) (pi_leibniz_depth q) Hle) as Hb.
      exact (Qlt_le_trans _ _ _ (Qle_lt_trans _ _ _ Hb (piL_cauchy_pos_prop _ (pi_leibniz_depth_pos_prop p))) H1).
    + rewrite (piL_qabs_sym (leiblw_S (2 * pi_leibniz_depth p + 2))
                (leiblw_S (2 * pi_leibniz_depth q + 2))).
      pose proof (piL_seq_pair_bound_prop (pi_leibniz_depth q) (pi_leibniz_depth p)
                    (Nat.lt_le_incl _ _ Hgt)) as Hb.
      exact (Qlt_le_trans _ _ _ (Qle_lt_trans _ _ _ Hb (piL_cauchy_pos_prop _ (pi_leibniz_depth_pos_prop q))) H1).
Qed.


(* -- The [bound] field: the value range satisfies [0 <= S <= 4 < 2^3] -- *)
Definition pi_leibniz_scale : Z := 3%Z.

Lemma pi_leibniz_bound : QBound pi_leibniz_seq pi_leibniz_scale.
Proof.
  unfold QBound, pi_leibniz_scale. intros k. unfold pi_leibniz_seq.
  assert (Hge : Qle 0%Q (leiblw_S (2 * pi_leibniz_depth k + 2)))
    by (apply leiblw_S_ge0_prop).
  assert (Hle : Qle (leiblw_S (2 * pi_leibniz_depth k + 2)) 4%Q)
    by (apply leiblw_S_le4_prop).
  rewrite (leiblw_qabs_id_prop _ Hge).
  apply (Qle_lt_trans _ 4%Q).
  - exact Hle.
  - unfold Qlt. cbn. reflexivity.
Qed.

(** The record packing: [pi_leibniz : CReal] (the four fields of the engine's record maker;
   isomorphic to the engine file at line [:66]).  *)
Definition pi_leibniz : CReal := {|
  seq := pi_leibniz_seq; scale := pi_leibniz_scale;
  cauchy := pi_leibniz_cauchy; bound := pi_leibniz_bound |}.

(* ============ Section 8. The e family (on the unified window carrier) ============ *)

(** The definition of the e family, keeping its name under the carrier swap: the e family is five
   times the [leiblw_nivwin] window.  *)
Definition lw0m_e (n : nat) : Q := 5 * leiblw_nivwin n.


(** The [leiblw_nivwin] window is antitone: [a <= b] implies [leiblw_nivwin b <= leiblw_nivwin a]. 
      *)
Lemma nivwin_antitone_prop : forall a b : nat, (a <= b)%nat ->
  Qle (leiblw_nivwin b) (leiblw_nivwin a)%Q.
Proof.
  intros a b Hab. unfold leiblw_nivwin.
  apply (proj2 (leiblw_qmake_le_prop 1 1
            (Pos.of_succ_nat (b + b + 1)) (Pos.of_succ_nat (a + a + 1)))).
  rewrite piL_pos_succ1_prop, piL_pos_succ1_prop.
  apply (proj1 (Z.mul_le_mono_pos_l (Z.of_nat (a + a + 1) + 1)
            (Z.of_nat (b + b + 1) + 1) 1 (Pos2Z.is_pos 1))).
  apply (Zplus_le_compat_r (Z.of_nat (a + a + 1)) (Z.of_nat (b + b + 1)) 1).
  apply znat_le_mono_prop.
  apply Nat.add_le_mono; [apply Nat.add_le_mono; exact Hab | apply Nat.le_refl].
Qed.

(** The add-one bridge for [inject_Z] (on the [Q] side, in product form;
    the reforming lemma of the two split steps).  Two facts of note in
    this file: the stdlib [ConstructiveCauchyReals] declares an
    [inject_Z] of type [Z -> CReal] that shadows the [QArith_base]
    version of type [Z -> Q], so every occurrence must stay fully
    qualified when both are in play; and [inject_Z c + 1] is not
    interchangeable with [inject_Z (c + 1)] -- this lemma is the bridge,
    closed by [ring] on the [Qeq] level. *)
Lemma piL_inject_add1 : forall k : Z,
  (QArith_base.inject_Z k + 1)%Q == QArith_base.inject_Z (k + 1).
Proof. intros k. unfold inject_Z, Qplus, Qeq. cbn. ring. Qed.

Lemma piL_e_split2_prop : forall (eps : Q) (c z : Z),
  Qle 0%Q eps -> (c + 1 <= z)%Z ->
  Qle (eps * (QArith_base.inject_Z c + 1)%Q) (eps * QArith_base.inject_Z z).
Proof.
  intros eps c z H0e Hcz.
  rewrite Zle_Qle in Hcz.
  rewrite <- piL_inject_add1 in Hcz.
  rewrite (Qmult_comm eps (QArith_base.inject_Z c + 1)).
  rewrite (Qmult_comm eps (QArith_base.inject_Z z)).
  apply (Qmult_le_compat_r (QArith_base.inject_Z c + 1) (QArith_base.inject_Z z) eps).
  - exact Hcz.
  - exact H0e.
Qed.

(** The reciprocal form of [inject_Z] at a successor (the reforming lemma
    of the modulus-bound chain). *)
Lemma piL_qinv_inject_succ : forall k : nat,
  / (QArith_base.inject_Z (Z.of_nat (S k))) == (1 # Pos.of_succ_nat k)%Q.
Proof. intros k. unfold inject_Z, Qinv, Qeq. cbn. f_equal. Qed.

(** The modulus definition (calibrated directly to the five-series window; the rescaling detour of
   the earlier four-series modulus is eliminated).  *)
Definition lw0m_modulus (eps : Q) : nat := S (Z.to_nat (Qceiling (5 / eps))).

(* The modulus bound: [lw0m_e (lw0m_modulus eps) < eps] (a [Q]-level chain with no decision
   procedure anywhere).  *)
(** Right cancellation for [Q] multiplication on the strict side (the closing lemma of the modulus
   bound).  *)
Lemma piL_qmult_cancel_prop : forall (a b : Q), Qlt 0%Q b -> ((a * b) * / b == a)%Q.
Proof.
  intros a b Hb0.
  rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
  - reflexivity.
  - exact (Qnot_eq_sym 0 b (Qlt_not_eq 0 b Hb0)).
Qed.

(** The first split step: [eps * (QArith_base.inject_Z (Qceiling
    (5 / eps)) + 1)] exceeds [5] -- in the shape
    [eps * QArith_base.inject_Z (Qceiling (5 / eps)) + eps >= 5 + eps > 5]. *)
Lemma piL_e_split1_prop : forall eps : Q, Qlt 0%Q eps ->
  Qlt 5 (eps * (QArith_base.inject_Z (Qceiling (5 / eps)) + 1)%Q).
Proof.
  intros eps Hpos.
  assert (Hne0 : ~ (eps == 0)%Q)
    by (apply Qnot_eq_sym; apply (Qlt_not_eq 0 eps); exact Hpos).
  assert (H0eps : Qle 0 eps) by (apply (Qlt_le_weak 0%Q); exact Hpos).
  assert (Hc5 : ((5 / eps) * eps == 5)%Q).
  { unfold Qdiv.
    rewrite (Qmult_comm (5 * / eps) eps), (Qmult_comm 5 (/ eps)), Qmult_assoc,
            Qmult_inv_r.
    - reflexivity.
    - exact Hne0. }
  pose proof (Qle_ceiling (5 / eps)) as Hceil.
  assert (HcM : Qle 5 (eps * QArith_base.inject_Z (Qceiling (5 / eps)))).
  { pose proof (Qmult_le_compat_r (5 / eps) (QArith_base.inject_Z (Qceiling (5 / eps))) eps
                  Hceil H0eps) as HM.
    rewrite Hc5 in HM.
    rewrite (Qmult_comm (QArith_base.inject_Z (Qceiling (5 / eps))) eps) in HM.
    exact HM. }
  apply (Qlt_le_trans _ (eps * QArith_base.inject_Z (Qceiling (5 / eps)) + eps * 1)%Q).
  - apply (Qlt_le_trans _ (5 + eps)%Q).
    + rewrite (Qplus_comm 5 eps).
      apply (proj2 (Qplus_lt_l 0 eps 5)). exact Hpos.
    + apply (Qplus_le_compat 5 (eps * QArith_base.inject_Z (Qceiling (5 / eps))) eps (eps * 1)).
      * exact HcM.
      * rewrite Qmult_1_r. apply Qle_refl.
  - rewrite <- (Qmult_plus_distr_r eps (QArith_base.inject_Z (Qceiling (5 / eps))) 1).
    apply Qle_refl.
Qed.

(** The modulus bound proper: with [eps > 0],
    [lw0m_e (lw0m_modulus eps)] undercuts [eps] -- the [inject_Z] argument
    moves monotonically under multiplication by [eps] (the second split
    step) on top of the first split step. *)
Lemma lw0m_modulus_bound_prop : forall eps : Q, Qlt 0%Q eps ->
  Qlt (lw0m_e (lw0m_modulus eps)) eps.
Proof.
  intros eps Hpos.
  assert (Hs1 := piL_e_split1_prop eps Hpos).
  assert (Hc0 : (0 <= Qceiling (5 / eps))%Z).
  { pose proof (Qle_ceiling (5 / eps)) as Hceil.
    assert (H05 : Qlt 0 5) by (unfold Qlt; cbn; reflexivity).
    assert (Hpos5 : Qlt 0%Q (5 / eps)%Q).
    { unfold Qdiv. apply Qmult_lt_0_compat.
      - exact H05.
      - apply Qinv_lt_0_compat. exact Hpos. }
    apply Z.lt_le_incl. rewrite Zlt_Qlt.
    apply (Qlt_le_trans 0%Q (5 / eps) (QArith_base.inject_Z (Qceiling (5 / eps)))
              Hpos5 Hceil). }
  set (t := Z.to_nat (Qceiling (5 / eps))) in *.
  assert (Htz : (Qceiling (5 / eps) <= Z.of_nat t)%Z)
    by (unfold t; rewrite Z2Nat.id by exact Hc0; apply Z.le_refl).
  pose proof (piL_qinv_inject_succ (S t + S t + 1)) as Hbinv.
  assert (HleA : (Qceiling (5 / eps) <= Z.of_nat (S t + S t + 1))%Z).
  { apply (Z.le_trans _ (Z.of_nat (Z.to_nat (Qceiling (5 / eps))))).
    - rewrite Z2Nat.id by exact Hc0. apply Z.le_refl.
    - apply znat_le_mono_prop. apply Nat.le_trans with (S t).
      + apply Nat.le_succ_diag_r.
      + rewrite <- Nat.add_assoc. apply Nat.le_add_r. }
  assert (Hcz : (Qceiling (5 / eps) + 1 <= Z.of_nat (S (S t + S t + 1)))%Z).
  { rewrite Nat2Z.inj_succ. unfold Z.succ.
    apply Z.add_le_mono.
    - exact HleA.
    - apply Z.le_refl. }

  assert (H0eps : Qle 0 eps) by (apply (Qlt_le_weak 0%Q); exact Hpos).
  assert (Hs2 := piL_e_split2_prop eps (Qceiling (5 / eps))
                (Z.of_nat (S (S t + S t + 1))) H0eps Hcz).
  assert (Hcore : Qlt 5 (eps * QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1))))).
  { apply (Qlt_le_trans _ (eps * (QArith_base.inject_Z (Qceiling (5 / eps)) + 1)%Q)).
    - exact Hs1.
    - exact Hs2. }
  assert (Hbpos : Qlt 0%Q (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1))))).
  { change 0%Q with (QArith_base.inject_Z 0). rewrite <- Zlt_Qlt.
    apply (proj1 (Nat2Z.inj_lt 0 (S (S t + S t + 1)))). apply Nat.lt_0_succ. }
  assert (Hbne0 : ~ (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1)))) == 0%Q).
  { apply Qnot_eq_sym. apply (Qlt_not_eq 0 _). exact Hbpos. }
  assert (Hmid : Qlt (5 * / (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1))))) eps).
  { apply (piL_qlt_transport_prop (5 * / (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1))))) ((eps * (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1))))) * / (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1))))) eps).
    - apply (Qmult_lt_compat_r 5 (eps * (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1))))) (/ (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1)))))).
      + exact Hbpos.
      + exact Hcore.
    - apply (piL_qmult_cancel_prop eps (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1))))).
      exact Hbpos. }
  assert (HeqA : (5 * leiblw_nivwin (S t))%Q == (5 * / (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1)))))%Q).
  { unfold leiblw_nivwin. rewrite Hbinv. reflexivity. }
  exact (proj2 (Qlt_compat (5 * leiblw_nivwin (S t))
              (5 * / (QArith_base.inject_Z (Z.of_nat (S (S t + S t + 1))))) HeqA
              eps eps (Qeq_refl eps)) Hmid).
Qed.

(* ============ Section 9. Unified window vanishing (the independently carried [lic_vanish] form)
   ============  *)

(** The type carrier of the vanishing interface (the decision carried by [QltT], at the [Set] level;
   the [Id]-style carriers of the source statement are replaced by [QltT]).  *)
Definition leiblw_lic_vanish (e : nat -> Q) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, (N <= n)%nat -> QltT (e n) eps).

(** The unified window vanishing instance: [lw0m_vanish_pi_prop] (the modulus family of this file
   replaces the earlier family wholesale).  *)
Definition lw0m_vanish_pi_prop : leiblw_lic_vanish lw0m_e.
Proof.
  intros eps Heps.
  assert (H05 : Qle 0 5) by (unfold Qle; cbn; apply Z.leb_le; reflexivity).
  exists (lw0m_modulus eps).
  intros n Hn.
  apply Qlt_to_QltT.
  unfold lw0m_e.
  rewrite (Qmult_comm 5 (leiblw_nivwin n)).
  assert (Hmid2 : Qle (leiblw_nivwin n * 5) (leiblw_nivwin (lw0m_modulus eps) * 5)).
  { apply (Qmult_le_compat_r (leiblw_nivwin n) (leiblw_nivwin (lw0m_modulus eps)) 5).
    + apply nivwin_antitone_prop. exact Hn.
    + exact H05. }
  pose proof (lw0m_modulus_bound_prop eps (QltT_to_Qlt 0 eps Heps)) as Hmb.
  rewrite (Qmult_comm 5 (leiblw_nivwin (lw0m_modulus eps))) in Hmb.
  apply (Qle_lt_trans _ (leiblw_nivwin (lw0m_modulus eps) * 5)).
  - apply (Qmult_le_compat_r (leiblw_nivwin n) (leiblw_nivwin (lw0m_modulus eps)) 5).
    + apply nivwin_antitone_prop. exact Hn.
    + exact H05.
  - exact Hmb.
Defined.

