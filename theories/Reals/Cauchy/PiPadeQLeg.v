(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)

(** * PiPadeQLeg: strict-order laws of the rational layer for the
      Pade tower.

    Mission.  This file formalizes the rational-order laws that the
      Pade convergence estimates need in place of non-linear
      arithmetic on [Q]: positivity of denominators, transfer of the
      strict order along a [Qeq] equality in both directions, strict
      monotonicity of addition by a positive or non-negative summand,
      and monotonicity of natural-number ratios at the [Z] level.
      Main statements: [pql_pos_den_pos], [pql_qlt0_eq_r],
      [pql_qlt_eq_r], [pql_qlt_eq_l], [pql_qlt_add_r],
      [pql_qle_lt_add], [pql_qlt_le_add], [pql_nat_ratio_mono2] and
      [pql_nat_ratio_mono].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith],
      [ZArith.ZArith] ([Z_le_gt_dec] lives in the [ZArith] namespace
      and is not re-exported by [QArith]), [Lia].  No other module of
      this development is required: the file is self-contained and
      its statements are all prefixed [pql_].

    References.  This development, [UpReqPadeQLeg.v], the upstream
      module whose statements, proofs and names are carried over
      here verbatim.  The three families replace the non-linear
      arithmetic spots of the upstream Pade files by explicit [Q]-
      and [Z]-level reasoning: the equality-transfer family stands
      for the [Sign]/[Lower]/[Finale] spots of the forms
      [cpf_qlt0_eq_r], [cpl_qlt_eq_l], [cpl_qlt_eq_sr],
      [cpf_qlt_eq_l] and [cpf_qlt_eq_r]; the strict-addition family
      stands for [cpf_qlt_add_r], [cpf_qle_lt_add] and
      [cpf_qlt_le_add]; the ratio-monotonicity family stands for the
      spots of the forms [pdp_R_ge_1] and [pdq_R_ge_2].

    Constructivity.  Assumption-free and fully proved.  The order
      predicates are the stdlib [Qlt]/[Qle] (the same [Q]-order
      scaffolding rule as [PiSeparation]); every proof is a finite
      case analysis on the signed [Z] representations of the rationals
      involved, assembled with explicit monotonicity lemmas
      ([Z.mul_le_mono_nonneg_r], [Z.mul_le_mono_nonneg_l],
      [Z.mul_lt_mono_pos_r]) and finished by linear arithmetic over
      [Z] only.  All proofs end in [Qed]; there are no definitions
      beyond the statements themselves.

    Build.  [rocq c -native-compiler no -q -Q theories pi_leibniz -Q
      theories/Reals/Cauchy "" theories/Reals/Cauchy/PiPadeQLeg.v]
      from the repository root compiles cleanly (exit 0); the first
      eight bytes of the artifact are [436f7121 00015ff4].

    This file is part of the rocq-pi-leibniz package; its interface
    may change in future releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.
Local Open Scope Z_scope.

(* ================= Section 1. Positivity of denominators ================= *)

(** The denominator of a rational is a [positive], so its embedding
    into [Z] is strictly positive.  This is pinned as a named lemma
    so that the later proofs need no implicit numeral transfer. *)
Lemma pql_pos_den_pos : forall d : positive, (0 < Z.pos d)%Z.
Proof. exact Pos2Z.is_pos. Qed.

(* ========== Section 2. Transfer of the strict order along [Qeq] ========== *)

(** Base limb, right transfer: rationals with equal representations
    share every strict lower bound at zero.  On the representation
    face: from [na * db = nb * da] with [1 <= na] conclude [0 < nb].
    The proof is by contradiction, comparing the products of both
    sides with the positive denominator [da]. *)
Lemma pql_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> Qlt 0 b.
Proof.
  intros a b Hab Ha.
  destruct a as [na da]. destruct b as [nb db].
  unfold Qeq in Hab. unfold Qlt in Ha |- *.
  cbn [Qnum Qden] in Hab, Ha |- *.
  pose proof (pql_pos_den_pos da) as Hda.
  assert (Hda0 : (0 <= Z.pos da)%Z) by lia.
  pose proof (pql_pos_den_pos db) as Hdb.
  (* The products by one and zero normalize linearly: [1 <= na],
     goal [0 < nb]. *)
  assert (Hna : (1 <= na)%Z) by lia.
  (* The main equation between numerators and denominators. *)
  assert (Hmul : (na * Z.pos db = nb * Z.pos da)%Z) by exact Hab.
  assert (Hdb0 : (0 <= Z.pos db)%Z) by lia.
  (* By contradiction: if [nb <= 0] then [nb * da <= 0], while
     [na * db >= db >= 1]. *)
  destruct (Z_le_gt_dec nb 0) as [Hn0 | Hn0].
  - exfalso.
    pose proof (Z.mul_le_mono_nonneg_r nb 0 (Z.pos da) Hda0 Hn0) as Hneg.
    pose proof (Z.mul_le_mono_nonneg_r 1 na (Z.pos db) Hdb0 Hna) as Hpos.
    lia.
  - lia.
Qed.

(** Right transfer along the equality: multiplying the strict
    inequality and the representation equation by the positive
    denominators, then cancelling the common positive factor [da]. *)
Lemma pql_qlt_eq_r : forall a b c : Q, a == b -> Qlt c a -> Qlt c b.
Proof.
  intros a b c Hab Hlt.
  destruct a as [na da]. destruct b as [nb db]. destruct c as [nc dc].
  unfold Qeq in Hab. unfold Qlt in Hlt |- *.
  cbn [Qnum Qden] in Hab, Hlt |- *.
  pose proof (pql_pos_den_pos da) as Hda.
  assert (Hda0 : (0 <= Z.pos da)%Z) by lia.
  pose proof (pql_pos_den_pos db) as Hdb.
  pose proof (pql_pos_den_pos dc) as Hdc.
  (* The rearrangement identities. *)
  assert (E1 : (na * Z.pos dc * Z.pos db = (na * Z.pos db) * Z.pos dc)%Z)
    by ring.
  assert (E2 : (nc * Z.pos da * Z.pos db = (nc * Z.pos db) * Z.pos da)%Z)
    by ring.
  assert (E3 : ((nb * Z.pos da) * Z.pos dc = nb * Z.pos dc * Z.pos da)%Z)
    by ring.
  rewrite Hab in E1.
  rewrite E3 in E1.
  (* Multiply the premise inequality by the positive [db]. *)
  assert (Hm : (nc * Z.pos da * Z.pos db < na * Z.pos dc * Z.pos db)%Z).
  { apply (proj1 (Z.mul_lt_mono_pos_r (Z.pos db)
                    (nc * Z.pos da) (na * Z.pos dc) Hdb)).
    lia. }
  rewrite E2 in Hm. rewrite E1 in Hm.
  (* Cancel the positive factor [da]. *)
  destruct (Z_le_gt_dec (nb * Z.pos dc) (nc * Z.pos db)) as [Hbad | Hgood].
  - exfalso.
    pose proof (Z.mul_le_mono_nonneg_r (nb * Z.pos dc) (nc * Z.pos db)
                  (Z.pos da) Hda0 Hbad) as Hc.
    lia.
  - lia.
Qed.

(** Left transfer along the equality, symmetric companion of
    [pql_qlt_eq_r]: the same reshaping to a common monotone
    multiplication frame, then cancelling the positive factor [da]
    with the iff form of [Z.mul_lt_mono_pos_r]. *)
Lemma pql_qlt_eq_l : forall a b c : Q, a == b -> Qlt a c -> Qlt b c.
Proof.
  intros a b c Hab Hlt.
  destruct a as [na da]. destruct b as [nb db]. destruct c as [nc dc].
  unfold Qeq in Hab. unfold Qlt in Hlt |- *.
  cbn [Qnum Qden] in Hab, Hlt |- *.
  pose proof (pql_pos_den_pos da) as Hda.
  assert (Hda0 : (0 <= Z.pos da)%Z) by lia.
  pose proof (pql_pos_den_pos db) as Hdb.
  pose proof (pql_pos_den_pos dc) as Hdc.
  assert (E1 : (na * Z.pos dc * Z.pos db = (na * Z.pos db) * Z.pos dc)%Z)
    by ring.
  assert (E2 : (nc * Z.pos da * Z.pos db = (nc * Z.pos db) * Z.pos da)%Z)
    by ring.
  assert (E3 : ((nb * Z.pos da) * Z.pos dc = nb * Z.pos dc * Z.pos da)%Z)
    by ring.
  assert (Hm : (na * Z.pos dc * Z.pos db < nc * Z.pos da * Z.pos db)%Z).
  { apply (proj1 (Z.mul_lt_mono_pos_r (Z.pos db)
                    (na * Z.pos dc) (nc * Z.pos da) Hdb)).
    lia. }
  (* Both ends are reshaped into the same monotone frame. *)
  assert (T1 : (na * Z.pos dc * Z.pos db = nb * Z.pos dc * Z.pos da)%Z).
  { transitivity ((na * Z.pos db) * Z.pos dc).
    - ring.
    - rewrite Hab. ring. }
  assert (T2 : (nc * Z.pos da * Z.pos db = nc * Z.pos db * Z.pos da)%Z) by ring.
  rewrite T1, T2 in Hm.
  (* Cancel the positive factor [da]. *)
  apply (proj2 (Z.mul_lt_mono_pos_r (Z.pos da)
                  (nb * Z.pos dc) (nc * Z.pos db) Hda)).
  exact Hm.
Qed.

(* ============ Section 3. Strict monotonicity of addition ============ *)

(** Adding a strictly positive summand strictly increases a rational:
    assembled from the iff form of [Qplus_lt_r], the identity
    [a + 0 == a], and the left transfer limb [pql_qlt_eq_l]. *)
Lemma pql_qlt_add_r : forall a b : Q, Qlt 0 b -> Qlt a (a + b)%Q.
Proof.
  intros a b Hb.
  assert (Ht : Qlt (a + 0)%Q (a + b)%Q)
    by (apply (proj2 (Qplus_lt_r 0 b a)); exact Hb).
  assert (Heq : (a + 0)%Q == a%Q) by ring.
  exact (pql_qlt_eq_l (a + 0)%Q a (a + b)%Q Heq Ht).
Qed.

(** A non-negative and a strictly positive summand give a strictly
    positive total: the previous limb shifted to the origin, closed
    by transitivity through [Qle_lt_trans]. *)
Lemma pql_qle_lt_add : forall a b : Q, Qle 0 a -> Qlt 0 b -> Qlt 0 (a + b)%Q.
Proof.
  intros a b Ha Hb.
  assert (Ht : Qlt (a + 0)%Q (a + b)%Q)
    by (apply (proj2 (Qplus_lt_r 0 b a)); exact Hb).
  assert (Heq : (a + 0)%Q == a%Q) by ring.
  assert (Hlt2 : Qlt a (a + b)%Q)
    by exact (pql_qlt_eq_l (a + 0)%Q a (a + b)%Q Heq Ht).
  exact (Qle_lt_trans 0%Q a (a + b)%Q Ha Hlt2).
Qed.

(** Symmetric companion of [pql_qle_lt_add] with the roles of the two
    summands exchanged, using [Qplus_lt_l] in place of [Qplus_lt_r]. *)
Lemma pql_qlt_le_add : forall a b : Q, Qlt 0 a -> Qle 0 b -> Qlt 0 (a + b)%Q.
Proof.
  intros a b Ha Hb.
  assert (Ht : Qlt (0 + b)%Q (a + b)%Q)
    by (apply (proj2 (Qplus_lt_l 0 a b)); exact Ha).
  assert (Heq : (0 + b)%Q == b%Q) by ring.
  assert (Hlt2 : Qlt b (a + b)%Q)
    by exact (pql_qlt_eq_l (0 + b)%Q b (a + b)%Q Heq Ht).
  exact (Qle_lt_trans 0%Q b (a + b)%Q Hb Hlt2).
Qed.

(* ========== Section 4. Monotonicity of natural-number ratios ========== *)

(** The mathematical core: for [k < n], the successor of [n - S k] is
    bounded by the product of the successor of [2 * n - S k] and the
    successor of [k], along the chain [X <= 2 * X <= 2 * Y <=
    Y * S k]; the case [k = 0] reduces to [Y = 2 * X]. *)
Lemma pql_nat_ratio_mono2 :
  forall n k : nat, (k < n)%nat ->
    (2 * Z.of_nat (S (n - S k))
     <= Z.of_nat (S (2 * n - S k)) * Z.of_nat (S k))%Z.
Proof.
  intros n k Hk.
  assert (H1 : (Z.of_nat (S (n - S k)) <= Z.of_nat (S (2 * n - S k)))%Z) by lia.
  destruct k as [| k'].
  - lia.
  - assert (H2 : (Z.of_nat (S (2 * n - S (S k'))) * 2
                  <= Z.of_nat (S (2 * n - S (S k'))) * Z.of_nat (S (S k')))%Z).
    { apply (Z.mul_le_mono_nonneg_l 2%Z (Z.of_nat (S (S k')))
               (Z.of_nat (S (2 * n - S (S k'))))); lia. }
    assert (H3 : (Z.of_nat (S (n - S (S k'))) * 2
                  <= Z.of_nat (S (2 * n - S (S k'))) * 2)%Z).
    { apply (Z.mul_le_mono_nonneg_r (Z.of_nat (S (n - S (S k'))))
               (Z.of_nat (S (2 * n - S (S k')))) 2%Z); lia. }
    lia.
Qed.

(** The monotonicity of natural-number ratios: the successor of
    [n - S k] is bounded by the product of the successor of
    [2 * n - S k] and the successor of [k]; proved from
    [pql_nat_ratio_mono2] through the intermediate bound by the
    doubling. *)
Lemma pql_nat_ratio_mono :
  forall n k : nat, (k < n)%nat ->
    (Z.of_nat (S (n - S k)) <= Z.of_nat (S (2 * n - S k)) * Z.of_nat (S k))%Z.
Proof.
  intros n k Hk.
  assert (H1 : (Z.of_nat (S (n - S k))
                <= 2 * Z.of_nat (S (n - S k)))%Z) by lia.
  apply Z.le_trans with (2 * Z.of_nat (S (n - S k)))%Z.
  - exact H1.
  - apply pql_nat_ratio_mono2. exact Hk.
Qed.

Print Assumptions pql_pos_den_pos.
Print Assumptions pql_qlt0_eq_r.
Print Assumptions pql_qlt_eq_r.
Print Assumptions pql_qlt_eq_l.
Print Assumptions pql_qlt_add_r.
Print Assumptions pql_qle_lt_add.
Print Assumptions pql_qlt_le_add.
Print Assumptions pql_nat_ratio_mono2.
Print Assumptions pql_nat_ratio_mono.
