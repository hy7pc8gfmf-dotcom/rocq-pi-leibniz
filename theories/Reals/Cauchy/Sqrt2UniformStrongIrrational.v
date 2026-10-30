(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import QExtra.
From Stdlib Require Import Qpower.
From Stdlib Require Import ConstructiveCauchyReals.
From Stdlib Require Import ConstructiveCauchyRealsMult.
From Stdlib Require Import Extraction.
Require Import PiCompareT.
Require Import PiCRealAppartT.
Require Import PiKernelSlack.

(** * Sqrt2UniformStrongIrrational: a uniform constructive strong
    irrationality lower bound for the square root of two.

    Mission.  A constructive Cauchy real [sqrt2_cr] together with the
    uniform strong irrationality bound: for every rational number
    [a # b] (any numerator [a : Z], any denominator height
    [b : positive]), the strict distance between [sqrt2_cr] and the
    embedded rational [inject_Q (a # b)] exceeds the single margin
    [sqrt2_uniform_margin b == 1 / (3 * b^2)] — a rational number
    depending on the denominator height [b] alone, with no search
    over the numerator.  The statement face is the two-sided
    [CRealLtT] sum of [PiCRealAppartT] (the Set-carried strict-order
    witness), so each margin certificate is a computable pair (witness
    index, decision identity) and the whole statement extracts to
    executable code.  Companion results: the defining square property
    [sqrt2_cr * sqrt2_cr == inject_Q 2], the positivity of the margin,
    and the apartness corollaries in the statement shapes of
    [PiSeparation].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith],
    [Lia], [QExtra], [ConstructiveCauchyReals],
    [ConstructiveCauchyRealsMult]; package modules [PiCompareT] (the
    reflected rational strict-order decision [QltT]),
    [PiCRealAppartT] (the Set-carried strict-order witness
    [CRealLtT] and its interchange bridges), and [PiKernelSlack]
    (the decision-bridge family between the [Qlt]/[Qle] statements
    and their reflected [QltT]/[QleT'] forms).

    References.  E. Bishop and D. Bridges, "Constructive Analysis"
    (1985), the uniform lower bound [1/(3*b^2)] for the square root
    of two: a prior constructive strong-irrationality result, stated
    there as a mathematical proof and carried here as a Set-valued
    sigma-type statement with an executable margin function of the
    denominator alone.

    Constructivity.  All statements are [Set]-valued; the predicate
    positions carry the reflected decision [QltT] (inside [CRealLtT])
    and the [Qlt] witnesses of the mirrored [CRealLt] form.  The real
    object is a rational bisection sequence with an exact width
    identity; no classical logic and no axioms are used anywhere, and
    the main statement closes by explicit rational arithmetic chains
    (case analysis on the integer gap [a^2 = 2*b^2], which is nonzero
    by the parity descent of Section 1).

    Build.  [coqc -native-compiler no -q -Q . ""
    Sqrt2UniformStrongIrrational.v] compiles cleanly (exit 0); the
    first eight bytes of the artifact are [436f7121 00015ff4].

    This file is part of the rocq-pi-leibniz package; its interface
    may change in future releases. *)

(* ================= Section 1. No rational square root of two ============ *)

(* Parity descent: an integer whose square is even is itself even. *)
Lemma sqrt2_even_of_sq_even : forall z : Z, Z.even (z * z) = true -> Z.even z = true.
Proof.
  intros z H. pose proof (Z.even_mul z z) as HM. rewrite HM in H.
  apply Bool.orb_true_iff in H. destruct H as [H | H]; exact H.
Qed.

(* Absolute value on the nonpositive half-axis. *)
Lemma sqrt2_zabs_nonpos : forall z : Z, (z <= 0)%Z -> Z.abs z = (- z)%Z.
Proof.
  intros z Hz.
  rewrite <- (Z.abs_opp z), (Z.abs_eq (- z) ltac:(lia)). reflexivity.
Qed.

(* The descent proper: no nonzero integer [b] admits [a^2 = 2*b^2].
   From such an equation both [a] and [b] are even, and halving both
   produces a strictly smaller solution — impossible by induction on
   the size of [b]. *)
Lemma sqrt2_no_sqrtZ : forall a b : Z, (0 < b)%Z -> (a * a = 2 * (b * b))%Z -> False.
Proof.
  assert (Hgen : forall n : nat, forall a b : Z, (0 < b)%Z ->
    (a * a = 2 * (b * b))%Z -> (Z.to_nat b <= n)%nat -> False).
  { induction n as [|n IH]; intros a b Hb Heq Hn.
    - assert (Hb0 : (b = 0)%Z).
      { pose proof (Z2Nat.id b (ltac:(lia))) as Hzz.
        apply Nat.le_0_r in Hn. rewrite Hn in Hzz. cbn in Hzz.
        symmetry. exact Hzz. }
      lia.
    - assert (Hae : Z.even a = true).
      { apply sqrt2_even_of_sq_even. rewrite Heq.
        rewrite Z.even_mul, Z.even_mul. cbn [Z.even]. reflexivity. }
      apply (proj1 (Z.even_spec a)) in Hae. destruct Hae as [a1 Ha1].
      assert (Hbb : (b * b = 2 * (a1 * a1))%Z) by lia.
      assert (Hbe : Z.even b = true).
      { apply sqrt2_even_of_sq_even. rewrite Hbb.
        rewrite Z.even_mul, Z.even_mul. cbn [Z.even]. reflexivity. }
      apply (proj1 (Z.even_spec b)) in Hbe. destruct Hbe as [b1 Hb1].
      apply (IH a1 b1).
      + lia.
      + rewrite Hb1 in Hbb.
        replace ((2 * b1) * (2 * b1))%Z with (4 * (b1 * b1))%Z in Hbb by ring.
        lia.
      + pose proof (Z2Nat.inj_mul b b1 (ltac:(lia)) (ltac:(lia))) as Hmm.
        pose proof (Z2Nat.id b (ltac:(lia))) as Hz1.
        pose proof (Z2Nat.id b1 (ltac:(lia))) as Hz2.
        lia. }
  intros a b Hb Heq.
  apply (Hgen (Z.to_nat b) a b Hb Heq (Nat.le_refl _)).
Qed.

(* The rational form: no rational squares to two. *)
Lemma sqrt2_no_sqrtQ : forall q : Q, ~ (q * q == 2%Q).
Proof.
  intros q Hq. destruct q as [a b].
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Heq : (a * a = 2 * (Z.pos b * Z.pos b))%Z).
  { unfold Qeq, Qmult in Hq. cbn in Hq.
    assert (Hb1 : (Z.pos (b * b) = Z.pos b * Z.pos b)%Z) by apply Pos2Z.inj_mul.
    assert (Hb2 : (Z.pos (b * b)~0 = 2 * Z.pos (b * b))%Z) by reflexivity.
    lia. }
  exact (sqrt2_no_sqrtZ a (Z.pos b) Hb Heq).
Qed.

(* The integer gap: [a^2 - 2*b^2] never vanishes, hence its absolute
   value is at least one — the algebraic core of the uniform bound. *)
Lemma sqrt2_int_gap_nonzero : forall (a : Z) (b : positive),
  (a * a <> 2 * (Z.pos b * Z.pos b))%Z.
Proof.
  intros a b Hc. apply (sqrt2_no_sqrtZ a (Z.pos b)).
  - apply Pos2Z.is_pos.
  - exact Hc.
Qed.

Lemma sqrt2_int_gap_ge1 : forall (a : Z) (b : positive),
  (1 <= Z.abs (a * a - 2 * (Z.pos b * Z.pos b)))%Z.
Proof.
  intros a b.
  assert (Hne : (a * a - 2 * (Z.pos b * Z.pos b) <> 0)%Z).
  { intro Hc. apply (sqrt2_int_gap_nonzero a b). lia. }
  destruct (Z_lt_le_dec 0 (a * a - 2 * (Z.pos b * Z.pos b))) as [Hpos | Hnonpos].
  - rewrite (Z.abs_eq _ (Z.lt_le_incl _ _ Hpos)). lia.
  - rewrite (Z.abs_neq _ Hnonpos). lia.
Qed.

(* Square monotonicity on the nonnegative side, in both directions. *)
Lemma sqrt2_sq_mono : forall u v : Q, Qle 0 v -> Qle v u -> Qle (v * v) (u * u).
Proof.
  intros u v Hv0 Hvu.
  assert (Hu0 : Qle 0 u) by (apply (Qle_trans 0 v u); [exact Hv0 | exact Hvu]).
  apply (Qle_trans _ (u * v)).
  - apply (Qmult_le_compat_r v u v); assumption.
  - rewrite (Qmult_comm u v).
    apply (Qmult_le_compat_r v u u); assumption.
Qed.

Lemma sqrt2_sq_lt_inv : forall u v : Q, Qle 0 u -> Qlt (v * v) (u * u) -> Qlt v u.
Proof.
  intros u v Hu0 Hlt.
  destruct (Qlt_le_dec v u) as [H | Hle].
  - exact H.
  - exfalso. apply (Qlt_not_le (v * v) (u * u) Hlt).
    apply (sqrt2_sq_mono v u Hu0 Hle).
Qed.

(* ================= Section 2. The rational bisection bracket ============ *)

(* One bisection step on the bracket [l, u]: the midpoint [m] either
   has [m^2 < 2] (move the lower end up) or [2 < m^2] (move the upper
   end down); the middle case [m^2 == 2] is impossible for rational
   [m] by Section 1. *)
Lemma sqrt2_qlt_bool_false_le : forall x y : Q, Qlt_bool x y = false -> Qle y x.
Proof.
  intros x y H. unfold Qlt_bool in H.
  destruct (x ?= y)%Q eqn:E; cbn in H.
  - assert (Hxy : x == y) by (apply (proj2 (Qeq_alt x y)); exact E).
    rewrite Hxy. apply Qle_refl.
  - discriminate H.
  - assert (Hyx : (y ?= x) = Lt).
    { rewrite <- (Qcompare_antisym x y), E. reflexivity. }
    apply Qlt_le_weak. exact (proj1 (Qlt_alt y x) Hyx).
Qed.

Fixpoint sqrt2_l (n : nat) : Q :=
  match n with
  | O => 1%Q
  | S m =>
      let lm := sqrt2_l m in
      let um := sqrt2_u m in
      let md := ((lm + um) * (1 # 2))%Q in
      if Qlt_bool (md * md) 2%Q then md else lm
  end
with sqrt2_u (n : nat) : Q :=
  match n with
  | O => (3 # 2)%Q
  | S m =>
      let lm := sqrt2_l m in
      let um := sqrt2_u m in
      let md := ((lm + um) * (1 # 2))%Q in
      if Qlt_bool (md * md) 2%Q then um else md
  end.

(* The strict-order Boolean spec lemmas (both directions). *)
Lemma sqrt2_qlt_bool_true_lt : forall x y : Q, Qlt_bool x y = true -> Qlt x y.
Proof.
  intros x y H. unfold Qlt_bool in H.
  destruct (x ?= y)%Q eqn:E; cbn in H.
  - discriminate H.
  - apply (proj1 (Qlt_alt x y)). exact E.
  - discriminate H.
Qed.

(* Small rational-order bookkeeping helpers. *)
Lemma sqrt2_qle_transport_r : forall a b c : Q, Qle a b -> b == c -> Qle a c.
Proof. intros a b c H Hbc. rewrite <- Hbc. exact H. Qed.

Lemma sqrt2_qle_sub_r : forall x y z : Q, Qle x y -> Qle (x - z) (y - z).
Proof. intros x y z H. exact (Qplus_le_compat x y (- z) (- z) H (Qle_refl _)). Qed.

Lemma sqrt2_qle_lsub : forall u v w : Q, Qle u v -> Qle (w - v) (w - u).
Proof.
  intros u v w H.
  apply (proj2 (Qle_minus_iff (w - v) (w - u))).
  assert (Hid : ((w - u) - (w - v) == v - u)%Q) by ring.
  rewrite Hid.
  exact (proj1 (Qle_minus_iff u v) H).
Qed.

Lemma sqrt2_qopp_le : forall u v : Q, Qle u v -> Qle (- v) (- u).
Proof.
  intros u v H.
  apply (proj2 (Qle_minus_iff (- v) (- u))).
  assert (Hid : ((- u) - (- v) == v - u)%Q) by ring.
  rewrite Hid.
  exact (proj1 (Qle_minus_iff u v) H).
Qed.

(* Bracketed values have a bracketed difference. *)
Lemma sqrt2_abs_diff_le : forall A B x y : Q,
  Qle A x -> Qle x B -> Qle A y -> Qle y B -> Qle (Qabs (x - y)) (B - A).
Proof.
  intros A B x y HAx HxB HAy HyB.
  assert (Hge : Qle (A - B) (x - y)%Q).
  { apply (Qle_trans _ (A - y)).
    - apply sqrt2_qle_lsub. exact HyB.
    - apply sqrt2_qle_sub_r. exact HAx. }
  assert (Hle : Qle (x - y) (B - A)%Q).
  { apply (Qle_trans _ (B - y)).
    - apply sqrt2_qle_sub_r. exact HxB.
    - apply sqrt2_qle_lsub. exact HAy. }
  destruct (Qlt_le_dec 0 (x - y)) as [Hs | Hs].
  - rewrite (Qabs_pos _ (Qlt_le_weak 0 _ Hs)). exact Hle.
  - rewrite (Qabs_neg _ Hs).
    apply (sqrt2_qle_transport_r _ ((-(A - B))%Q) _).
    + apply sqrt2_qopp_le. exact Hge.
    + ring.
Qed.

(* The bracket invariants, by induction on the bisection depth. *)
Lemma sqrt2_l_sq_lt : forall n : nat, Qlt (sqrt2_l n * sqrt2_l n) 2%Q.
Proof.
  induction n as [|n IH]; cbn [sqrt2_l sqrt2_u] in *.
  - unfold Qlt, Qmult. cbn. lia.
  - set (md := ((sqrt2_l n + sqrt2_u n) * (1 # 2))%Q).
    destruct (Qlt_bool (md * md) 2%Q) eqn:E.
    + apply sqrt2_qlt_bool_true_lt. exact E.
    + exact IH.
Qed.

Lemma sqrt2_u_sq_gt : forall n : nat, Qlt 2%Q (sqrt2_u n * sqrt2_u n).
Proof.
  induction n as [|n IH]; cbn [sqrt2_l sqrt2_u] in *.
  - unfold Qlt, Qmult. cbn. lia.
  - set (md := ((sqrt2_l n + sqrt2_u n) * (1 # 2))%Q).
    destruct (Qlt_bool (md * md) 2%Q) eqn:E.
    + exact IH.
    + pose proof (sqrt2_qlt_bool_false_le _ _ E) as Hle.
      assert (Hne : ~ (md * md == 2%Q)) by apply sqrt2_no_sqrtQ.
      destruct (Qle_lt_or_eq 2%Q (md * md) Hle) as [Hlt | Heq].
      * exact Hlt.
      * apply False_ind. apply Hne. apply (Qeq_sym _ _ Heq).
Qed.

(* Midpoint order facts: the midpoint of a bracket lies between the ends. *)
Lemma sqrt2_mid_le_u : forall l u : Q, Qle l u -> Qle ((l + u) * (1 # 2)) u.
Proof.
  intros l u H.
  assert (Hid : ((u + u) * (1 # 2) == u)%Q) by ring.
  apply (Qle_trans _ ((u + u) * (1 # 2))).
  - apply Qmult_le_compat_r.
    + apply (Qplus_le_compat l u u u); [exact H | apply Qle_refl].
    + unfold Qle. cbn. lia.
  - exact (sqrt2_qle_transport_r ((u + u) * (1 # 2)) ((u + u) * (1 # 2)) u
            (Qle_refl _) Hid).
Qed.

Lemma sqrt2_mid_ge_l : forall l u : Q, Qle l u -> Qle l ((l + u) * (1 # 2)).
Proof.
  intros l u H.
  assert (Hid : (l == (l + l) * (1 # 2))%Q) by ring.
  apply (Qle_trans l ((l + l) * (1 # 2)) _).
  - exact (sqrt2_qle_transport_r l l ((l + l) * (1 # 2)) (Qle_refl l) Hid).
  - apply Qmult_le_compat_r.
    + apply (Qplus_le_compat l l l u); [apply Qle_refl | exact H].
    + unfold Qle. cbn. lia.
Qed.

(* The width denominator: [2^(n+1)] as a positive, by a plain recursion. *)
Fixpoint sqrt2_den (n : nat) : positive :=
  match n with
  | O => 2%positive
  | S m => (sqrt2_den m * 2)%positive
  end.

(* The exact width identity: the bracket halves at every step. *)
Lemma sqrt2_width : forall n : nat,
  (sqrt2_u n - sqrt2_l n)%Q == (1 # sqrt2_den n)%Q.
Proof.
  induction n as [|n IH]; cbn [sqrt2_l sqrt2_u] in *.
  - reflexivity.
  - set (md := ((sqrt2_l n + sqrt2_u n) * (1 # 2))%Q).
    destruct (Qlt_bool (md * md) 2%Q) eqn:E.
    + assert (Hstep : (sqrt2_u n - md == (sqrt2_u n - sqrt2_l n) * (1 # 2))%Q)
        by (unfold md; ring).
      rewrite Hstep, IH.
      unfold Qeq, Qmult, Qminus. cbn [Qnum Qden Qplus Qopp sqrt2_den]. ring.
    + assert (Hstep : (md - sqrt2_l n == (sqrt2_u n - sqrt2_l n) * (1 # 2))%Q)
        by (unfold md; ring).
      rewrite Hstep, IH.
      unfold Qeq, Qmult, Qminus. cbn [Qnum Qden Qplus Qopp sqrt2_den]. ring.
Qed.

(* Monotonicity: the lower end climbs, the upper end sinks. *)
Lemma sqrt2_l_le_u : forall n : nat, Qle (sqrt2_l n) (sqrt2_u n).
Proof.
  induction n as [|n IH]; cbn [sqrt2_l sqrt2_u] in *.
  - unfold Qle. cbn. lia.
  - set (md := ((sqrt2_l n + sqrt2_u n) * (1 # 2))%Q).
    destruct (Qlt_bool (md * md) 2%Q) eqn:E.
    + apply (sqrt2_mid_le_u (sqrt2_l n) (sqrt2_u n)). exact IH.
    + apply (sqrt2_mid_ge_l (sqrt2_l n) (sqrt2_u n)). exact IH.
Qed.

Lemma sqrt2_l_step_mono : forall n : nat, Qle (sqrt2_l n) (sqrt2_l (S n)).
Proof.
  intros n. cbn [sqrt2_l sqrt2_u].
  set (md := ((sqrt2_l n + sqrt2_u n) * (1 # 2))%Q).
  destruct (Qlt_bool (md * md) 2%Q) eqn:E.
  - apply (sqrt2_mid_ge_l (sqrt2_l n) (sqrt2_u n)). apply sqrt2_l_le_u.
  - apply Qle_refl.
Qed.

Lemma sqrt2_u_step_anti : forall n : nat, Qle (sqrt2_u (S n)) (sqrt2_u n).
Proof.
  intros n. cbn [sqrt2_l sqrt2_u].
  set (md := ((sqrt2_l n + sqrt2_u n) * (1 # 2))%Q).
  destruct (Qlt_bool (md * md) 2%Q) eqn:E.
  - apply Qle_refl.
  - apply (sqrt2_mid_le_u (sqrt2_l n) (sqrt2_u n)). apply sqrt2_l_le_u.
Qed.

Lemma sqrt2_l_mono : forall p q : nat, (p <= q)%nat -> Qle (sqrt2_l p) (sqrt2_l q).
Proof.
  intros p q H. induction H as [|q Hle IH].
  - apply Qle_refl.
  - apply (Qle_trans _ (sqrt2_l q)).
    + exact IH.
    + apply sqrt2_l_step_mono.
Qed.

Lemma sqrt2_u_anti : forall p q : nat, (p <= q)%nat -> Qle (sqrt2_u q) (sqrt2_u p).
Proof.
  intros p q H. induction H as [|q Hle IH].
  - apply Qle_refl.
  - apply (Qle_trans _ (sqrt2_u q)).
    + apply sqrt2_u_step_anti.
    + exact IH.
Qed.

(* The bracket endpoints stay in [1, 3/2]. *)
Lemma sqrt2_l_lb : forall n : nat, Qle 1%Q (sqrt2_l n).
Proof.
  intros n. apply (Qle_trans _ (sqrt2_l 0)).
  - unfold Qle. cbn. lia.
  - apply sqrt2_l_mono. apply Nat.le_0_l.
Qed.

Lemma sqrt2_u_ub : forall n : nat, Qle (sqrt2_u n) (3 # 2)%Q.
Proof.
  intros n. apply (Qle_trans _ (sqrt2_u 0)).
  - apply sqrt2_u_anti. apply Nat.le_0_l.
  - apply Qle_refl.
Qed.

(* Difference bounds inside the bracket (the Cauchy modulus workhorse). *)
Lemma sqrt2_l_diff_le : forall p q : nat, (p <= q)%nat ->
  Qle (sqrt2_l q - sqrt2_l p) (sqrt2_u p - sqrt2_l p)%Q.
Proof.
  intros p q H.
  apply sqrt2_qle_sub_r.
  apply (Qle_trans _ (sqrt2_u q)).
  - apply sqrt2_l_le_u.
  - apply sqrt2_u_anti. exact H.
Qed.

Lemma sqrt2_u_diff_le : forall p q : nat, (p <= q)%nat ->
  Qle (sqrt2_u p - sqrt2_u q) (sqrt2_u p - sqrt2_l p)%Q.
Proof.
  intros p q H.
  apply (sqrt2_qle_lsub (sqrt2_l p) (sqrt2_u q) (sqrt2_u p)).
  apply (Qle_trans _ (sqrt2_l q)).
  - apply sqrt2_l_mono. exact H.
  - apply sqrt2_l_le_u.
Qed.

(* ================= Section 3. The constructive real object ============ *)

(* Strict-order transport at the [Qlt] level. *)
Lemma sqrt2_qlt_transport_r : forall a b c : Q, Qlt a b -> b == c -> Qlt a c.
Proof. intros a b c H Hbc. rewrite <- Hbc. exact H. Qed.

(* The width undercuts the power of two: [1/2^(n+1) < 2^(-n)]. *)
Lemma sqrt2_wQ_lt_pow : forall n : nat,
  Qlt ((1 # sqrt2_den n)%Q) (2 ^ (Z.opp (Z.of_nat n)))%Q.
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn. lia.
  - assert (Hne2 : ~ (2 == 0)%Q) by (unfold Qeq; cbn; discriminate).
    assert (Hpos : Qlt 0%Q (1 # 2)%Q) by (unfold Qlt; cbn; lia).
    assert (Hstep : (2 ^ (Z.opp (Z.of_nat (S n))))%Q
                    == (2 ^ (Z.opp (Z.of_nat n)))%Q * (1 # 2)%Q).
    { replace (Z.opp (Z.of_nat (S n)))%Z
        with (Z.opp (Z.of_nat n) + (-1))%Z
        by (rewrite Nat2Z.inj_succ; unfold Z.pred; lia).
      rewrite Qpower_plus by exact Hne2.
      assert (H21 : (2 ^ (-1))%Q == (1 # 2)%Q) by reflexivity.
      rewrite H21. reflexivity. }
    apply (sqrt2_qlt_transport_r _ ((2 ^ (Z.opp (Z.of_nat n)))%Q * (1 # 2)%Q)).
    + assert (Hid : ((1 # sqrt2_den (S n))%Q
                      == (1 # sqrt2_den n)%Q * (1 # 2)%Q)).
      { unfold Qeq, Qmult. cbn [Qnum Qden sqrt2_den]. ring. }
      rewrite Hid.
      apply (Qmult_lt_compat_r _ _ _ Hpos IH).
    + symmetry. exact Hstep.
Qed.

(* The Z-indexed sampling sequence: at depth [|k|] on the negative
   half-axis (the form in which the Cauchy condition reads the
   sequence), the upper bracket end is read off. *)
Definition sqrt2_seq (k : Z) : Q := sqrt2_u (Z.to_nat (Z.abs k)).

(* The read-off bridge: the negative tail lands on the nat sequence. *)
Lemma sqrt2_seq_negtail : forall n : nat,
  sqrt2_seq (Z.opp (Z.of_nat n)) == sqrt2_u n.
Proof.
  intros n. unfold sqrt2_seq.
  rewrite Z.abs_opp, (Z.abs_eq _ (Nat2Z.is_nonneg _)).
  rewrite Nat2Z.id.
  reflexivity.
Qed.

(* Every sampled value lies in (0, 2) in absolute value. *)
Lemma sqrt2_u_abs_lt : forall n : nat, Qlt (Qabs (sqrt2_u n)) 2%Q.
Proof.
  intros n.
  assert (Hge : Qle 0 (sqrt2_u n)).
  { apply (Qle_trans _ (sqrt2_l n)).
    - apply (Qle_trans _ 1%Q); [unfold Qle; cbn; lia | apply sqrt2_l_lb].
    - apply sqrt2_l_le_u. }
  rewrite (Qabs_pos _ Hge).
  apply (Qle_lt_trans _ (3 # 2)%Q).
  - apply sqrt2_u_ub.
  - unfold Qlt. cbn. lia.
Qed.

(* The [bound] field: values within [2^1]. *)
Definition sqrt2_scale : Z := 1%Z.

Lemma sqrt2_seq_bound : QBound sqrt2_seq sqrt2_scale.
Proof.
  unfold QBound, sqrt2_scale, sqrt2_seq. intros k.
  apply sqrt2_u_abs_lt.
Qed.

(* The [cauchy] field: the tail is controlled by the bracket width. *)
Lemma sqrt2_seq_cauchy : QCauchySeq sqrt2_seq.
Proof.
  unfold QCauchySeq. intros k p q Hp Hq.
  destruct (Z_le_gt_dec k 0) as [Hk0 | Hkpos].
  - (* deep tail: the widths at the shallowest depth dominate *)
    assert (Hp0 : (p <= 0)%Z) by (apply (Z.le_trans p k 0 Hp Hk0)).
    assert (Hq0 : (q <= 0)%Z) by (apply (Z.le_trans q k 0 Hq Hk0)).
    assert (Hpk : (Z.abs k <= Z.abs p)%Z).
    { rewrite (sqrt2_zabs_nonpos p Hp0), (sqrt2_zabs_nonpos k Hk0).
      exact (proj1 (Z.opp_le_mono p k) Hp). }
    assert (Hqk : (Z.abs k <= Z.abs q)%Z).
    { rewrite (sqrt2_zabs_nonpos q Hq0), (sqrt2_zabs_nonpos k Hk0).
      exact (proj1 (Z.opp_le_mono q k) Hq). }
    assert (Haklep : (Z.to_nat (Z.abs k) <= Z.to_nat (Z.abs p))%nat).
    { apply (proj1 (Z2Nat.inj_le _ _ (Z.abs_nonneg _) (Z.abs_nonneg _))). exact Hpk. }
    assert (Hakaq : (Z.to_nat (Z.abs k) <= Z.to_nat (Z.abs q))%nat).
    { apply (proj1 (Z2Nat.inj_le _ _ (Z.abs_nonneg _) (Z.abs_nonneg _))). exact Hqk. }
    assert (Hbnd : Qle (Qabs (sqrt2_u (Z.to_nat (Z.abs p))
                              - sqrt2_u (Z.to_nat (Z.abs q))))
                  ((1 # sqrt2_den (Z.to_nat (Z.abs k)))%Q)).
    { rewrite <- (sqrt2_width (Z.to_nat (Z.abs k))).
      exact (sqrt2_abs_diff_le (sqrt2_l (Z.to_nat (Z.abs k)))
             (sqrt2_u (Z.to_nat (Z.abs k)))
             (sqrt2_u (Z.to_nat (Z.abs p))) (sqrt2_u (Z.to_nat (Z.abs q)))
             (Qle_trans (sqrt2_l (Z.to_nat (Z.abs k)))
                (sqrt2_l (Z.to_nat (Z.abs p))) (sqrt2_u (Z.to_nat (Z.abs p)))
                (sqrt2_l_mono (Z.to_nat (Z.abs k)) (Z.to_nat (Z.abs p)) Haklep)
                (sqrt2_l_le_u (Z.to_nat (Z.abs p))))
             (sqrt2_u_anti (Z.to_nat (Z.abs k)) (Z.to_nat (Z.abs p)) Haklep)
             (Qle_trans (sqrt2_l (Z.to_nat (Z.abs k)))
                (sqrt2_l (Z.to_nat (Z.abs q))) (sqrt2_u (Z.to_nat (Z.abs q)))
                (sqrt2_l_mono (Z.to_nat (Z.abs k)) (Z.to_nat (Z.abs q)) Hakaq)
                (sqrt2_l_le_u (Z.to_nat (Z.abs q))))
             (sqrt2_u_anti (Z.to_nat (Z.abs k)) (Z.to_nat (Z.abs q)) Hakaq)). }
    assert (Hkform : (k = Z.opp (Z.of_nat (Z.to_nat (Z.abs k))))%Z).
    { symmetry. rewrite (sqrt2_zabs_nonpos k Hk0).
      rewrite (Z2Nat.id (- k) ltac:(lia)). lia. }
    rewrite Hkform.
    apply (Qle_lt_trans _ ((1 # sqrt2_den (Z.to_nat (Z.abs k)))%Q)).
    + exact Hbnd.
    + apply sqrt2_wQ_lt_pow.
  - (* shallow cap: all values in [1, 3/2], so the difference is at most 1/2 *)
    assert (Hbnd : Qle (Qabs (sqrt2_u (Z.to_nat (Z.abs p))
                              - sqrt2_u (Z.to_nat (Z.abs q))))
                  ((3 # 2) - (1 # 1))%Q).
    exact (sqrt2_abs_diff_le (1 # 1) (3 # 2)
             (sqrt2_u (Z.to_nat (Z.abs p))) (sqrt2_u (Z.to_nat (Z.abs q)))
             (Qle_trans (1 # 1) (sqrt2_l (Z.to_nat (Z.abs p)))
                (sqrt2_u (Z.to_nat (Z.abs p)))
                (sqrt2_l_lb (Z.to_nat (Z.abs p)))
                (sqrt2_l_le_u (Z.to_nat (Z.abs p))))
             (sqrt2_u_ub (Z.to_nat (Z.abs p)))
             (Qle_trans (1 # 1) (sqrt2_l (Z.to_nat (Z.abs q)))
                (sqrt2_u (Z.to_nat (Z.abs q)))
                (sqrt2_l_lb (Z.to_nat (Z.abs q)))
                (sqrt2_l_le_u (Z.to_nat (Z.abs q))))
             (sqrt2_u_ub (Z.to_nat (Z.abs q)))).
    assert (Hid : ((3 # 2) - (1 # 1) == (1 # 2))%Q) by ring.
    apply (Qle_lt_trans _ ((1 # 2)%Q)).
    + exact Hbnd.
    + apply (Qlt_le_trans _ 2%Q).
      * unfold Qlt. cbn. lia.
      * assert (H12 : Qle 1 2) by (unfold Qle; cbn; lia).
        replace (2)%Q with ((2 ^ 1)%Q) by reflexivity.
        apply Qpower_le_compat_l.
        -- lia.
        -- exact H12.
Qed.

(* The record packing: [sqrt2_cr : CReal]. *)
Definition sqrt2_cr : CReal := {|
  seq := sqrt2_seq; scale := sqrt2_scale;
  cauchy := sqrt2_seq_cauchy; bound := sqrt2_seq_bound |}.

(* ================= Section 4. The defining square property ============ *)

(* The width denominator strictly dominates the power of two. *)
Lemma sqrt2_pow_lt_den : forall n : nat,
  Qlt (2 ^ (Z.of_nat n))%Q ((Z.pos (sqrt2_den n) # 1)%Q).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn. lia.
  - assert (Hne2 : ~ (2 == 0)%Q) by (unfold Qeq; cbn; discriminate).
    replace (Z.of_nat (S n))%Z with (Z.of_nat n + 1)%Z
      by (rewrite Nat2Z.inj_succ; unfold Z.succ; lia).
    rewrite Qpower_plus by exact Hne2.
    assert (H21 : (2 ^ 1%Z)%Q == (2 # 1)%Q) by reflexivity.
    rewrite H21.
    assert (Hid : ((Z.pos (sqrt2_den n) # 1)%Q * (2 # 1)%Q
                   == (Z.pos (sqrt2_den (S n)) # 1)%Q)).
    { unfold Qeq, Qmult. cbn [Qnum Qden sqrt2_den].
      rewrite (Pos2Z.inj_mul (sqrt2_den n) 2). reflexivity. }
    rewrite <- Hid.
    apply (Qmult_lt_compat_r _ _ (2 # 1)%Q).
    + unfold Qlt. cbn. lia.
    + exact IH.
Qed.

(* The bracket width is below the resolution scale. *)
Lemma sqrt2_wQ_le_pow : forall n : nat,
  Qle ((1 # sqrt2_den n)%Q) ((1 # 1) / (2 ^ (Z.of_nat n))%Q).
Proof.
  intros n.
  assert (Hpow0 : Qlt 0%Q (2 ^ (Z.of_nat n))%Q)
    by (apply Qpower_0_lt; unfold Qlt; cbn; lia).
  assert (Hden0 : Qlt 0%Q ((Z.pos (sqrt2_den n) # 1)%Q)) by (unfold Qlt; cbn; lia).
  apply Qlt_le_weak.
  unfold Qdiv. rewrite Qmult_1_l.
  exact (proj1 (Qinv_lt_contravar (2 ^ (Z.of_nat n))%Q
                  ((Z.pos (sqrt2_den n) # 1)%Q) Hpow0 Hden0)
           (sqrt2_pow_lt_den n)).
Qed.

(* Right-cancellative multiplication by a positive rational. *)
Lemma sqrt2_qmult_le_reg_r : forall a b c : Q,
  Qle (a * c) (b * c) -> Qlt 0 c -> Qle a b.
Proof.
  intros a b c H Hc0.
  assert (Hcne : ~ (c == 0)%Q)
    by exact (Qnot_eq_sym 0 c (Qlt_not_eq 0 c Hc0)).
  assert (Hid : forall x : Q, (x * c) * (/ c) == x).
  { intros x. rewrite <- Qmult_assoc.
    rewrite (Qmult_inv_r c Hcne). apply Qmult_1_r. }
  assert (Hm : Qle (a * c * (/ c)) (b * c * (/ c)))
    by (apply (Qmult_le_compat_r _ _ (/ c));
          [exact H | apply (Qinv_le_0_compat _ (Qlt_le_weak _ _ Hc0))]).
  rewrite (Hid a), (Hid b) in Hm. exact Hm.
Qed.


Lemma sqrt2_sq_prop : (sqrt2_cr * sqrt2_cr == inject_Q 2)%CReal.
Proof.
  apply (proj2 (CRealEq_diff (sqrt2_cr * sqrt2_cr) (inject_Q 2))).
  intros n.
  unfold CReal_mult, CReal_mult_seq.
  cbn [seq scale sqrt2_cr].
  replace (n - sqrt2_scale - 1)%Z with (n - 2)%Z by (unfold sqrt2_scale; ring).
  unfold sqrt2_seq, inject_Q. cbn [seq].
  set (m := Z.to_nat (Z.abs (n - 2))).
  set (um := sqrt2_u m).
  assert (Hum2 : Qlt 2%Q (um * um)) by exact (sqrt2_u_sq_gt m).
  assert (Hpos2 : Qle 0 (um * um - 2)%Q)
    by (apply (Qlt_le_weak 0 _);
          exact (proj2 (Qplus_lt_l 2%Q (um * um) (-2)%Q) Hum2)).
  rewrite (Qabs_pos _ Hpos2).
  destruct (Z_le_gt_dec 0 n) as [Hn0 | Hn1].
  - (* nonnegative cap index: the crude bound [u <= 3/2] suffices *)
    assert (Hub : Qle (um * um) ((3 # 2) * (3 # 2))%Q).
    { apply (sqrt2_sq_mono (3 # 2)%Q um).
      - apply (Qle_trans _ (sqrt2_l m)).
        + apply (Qle_trans _ 1%Q); [unfold Qle; cbn; lia | apply sqrt2_l_lb].
        + apply sqrt2_l_le_u.
      - exact (sqrt2_u_ub m). }
    apply (Qle_trans _ ((1 # 4)%Q)).
    + apply (Qle_trans _ ((3 # 2) * (3 # 2) - 2)%Q).
      * apply (sqrt2_qle_sub_r _ _ 2%Q). exact Hub.
      * assert (Hid : ((3 # 2) * (3 # 2) - 2 == (1 # 4))%Q) by ring.
        rewrite Hid. apply Qle_refl.
    + apply (Qle_trans _ (2 * 2 ^ (Z.of_nat 0))%Q).
      * unfold Qle. cbn. lia.
      * assert (Hp : Qle (2 ^ (Z.of_nat 0))%Q (2 ^ n)%Q)
          by (apply (Qpower_le_compat_l 2%Q); [exact Hn0 | unfold Qle; cbn; lia]).
        rewrite (Qmult_comm 2 (2 ^ (Z.of_nat 0))), (Qmult_comm 2 (2 ^ n)).
        apply (Qmult_le_compat_r _ _ (2 # 1)%Q); [exact Hp | unfold Qle; cbn; lia].
  - (* negative cap index: the width chain with the exact exponent *)
    assert (Hm : (Z.of_nat m = 2 - n)%Z).
    { unfold m.
      rewrite (sqrt2_zabs_nonpos (n - 2)) by lia.
      rewrite (Z2Nat.id (-(n - 2))%Z) by lia.
      lia. }
    assert (Hw3 : Qle (um * um - 2) (3 * (1 # sqrt2_den m))%Q).
    { apply (Qle_trans _ (um * um - sqrt2_l m * sqrt2_l m)).
      - apply (sqrt2_qle_lsub (sqrt2_l m * sqrt2_l m) 2%Q (um * um)).
        apply (Qlt_le_weak _ _ (sqrt2_l_sq_lt m)).
      - assert (Hid1 : (um * um - sqrt2_l m * sqrt2_l m
                        == (um - sqrt2_l m) * (um + sqrt2_l m))%Q) by ring.
        rewrite Hid1.
        apply (Qle_trans _ ((um - sqrt2_l m) * 3%Q)).
        + rewrite (Qmult_comm (um - sqrt2_l m) (um + sqrt2_l m)),
            (Qmult_comm (um - sqrt2_l m) 3%Q).
          apply (Qmult_le_compat_r _ _ (um - sqrt2_l m)%Q).
          * apply (Qle_trans _ ((3 # 2) + (3 # 2))%Q).
            -- apply (Qplus_le_compat _ _ _ _ (sqrt2_u_ub m)).
               apply (Qle_trans _ (sqrt2_u m)).
               ++ apply sqrt2_l_le_u.
               ++ apply sqrt2_u_ub.
            -- assert (Hid0 : ((3 # 2) + (3 # 2) == 3%Q)) by ring.
               rewrite Hid0. apply Qle_refl.
          * exact (proj1 (Qle_minus_iff (sqrt2_l m) um) (sqrt2_l_le_u m)).
        + assert (Hw : (um - sqrt2_l m)%Q == (1 # sqrt2_den m)%Q)
            by (apply sqrt2_width).
          rewrite Hw.
          assert (Hid2 : ((1 # sqrt2_den m)%Q * 3
                          == 3 * (1 # sqrt2_den m)%Q)) by ring.
          rewrite Hid2. apply Qle_refl. }
    assert (Hbridge := sqrt2_wQ_le_pow m).
    assert (Hstep1 : Qle (3 * (1 # sqrt2_den m)%Q)
                       (3 * ((1 # 1) / (2 ^ (Z.of_nat m))%Q))).
    { rewrite (Qmult_comm 3 ((1 # sqrt2_den m)%Q)).
      rewrite (Qmult_comm 3 ((1 # 1) / (2 ^ (Z.of_nat m))%Q)).
      apply (Qmult_le_compat_r _ _ 3%Q).
      - exact Hbridge.
      - unfold Qle. cbn. lia. }
    apply (Qle_trans _ (3 * ((1 # 1) / (2 ^ (Z.of_nat m))%Q))).
    + apply (Qle_trans _ (3 * (1 # sqrt2_den m)%Q)).
      * exact Hw3.
      * exact Hstep1.
    + apply (sqrt2_qmult_le_reg_r _ _ (2 ^ (Z.of_nat m))%Q).
      * (* the multiplied form: 3 on the left, 2^(n+1+m) = 2^3 = 16 on the right *)
        assert (Hcancel : forall X : Q, ~ (X == 0%Q) -> ((1 # 1) / X) * X == 1%Q).
        { intros X HX. unfold Qdiv. rewrite <- Qmult_assoc.
          rewrite (Qmult_comm (/ X) X). rewrite (Qmult_inv_r X HX).
          rewrite Qmult_1_r. reflexivity. }
        assert (Hpowm0 : Qlt 0%Q (2 ^ (Z.of_nat m))%Q)
          by (apply Qpower_0_lt; unfold Qlt; cbn; lia).
        assert (Hpowmne : ~ ((2 ^ (Z.of_nat m))%Q == 0%Q))
          by (intro Hc; exact (Qlt_not_eq 0 _ Hpowm0 (Qeq_sym _ _ Hc))).
        assert (Hne2 : ~ (2 == 0)%Q) by (unfold Qeq; cbn; discriminate).
        rewrite <- Qmult_assoc.
        rewrite (Hcancel (2 ^ (Z.of_nat m)) Hpowmne).
        rewrite Qmult_1_r.
        rewrite <- Qmult_assoc.
        rewrite <- (Qpower_plus 2 n (Z.of_nat m) Hne2).
        assert (Hexp : (n + Z.of_nat m)%Z = 2%Z) by (rewrite Hm; lia).
        rewrite Hexp.
        unfold Qle. cbn. lia.
      * (* the multiplier is positive *)
        assert (Hpowm0 : Qlt 0%Q (2 ^ (Z.of_nat m))%Q)
          by (apply Qpower_0_lt; unfold Qlt; cbn; lia).
        exact Hpowm0.
Qed.

(* ================= Section 5. The uniform margin chains ============ *)

(* The margin: Bishop's bound, a function of the denominator height alone. *)
Definition sqrt2_uniform_margin (b : positive) : Q := (1 # (3 * b * b))%Q.

Lemma sqrt2_margin_pos : forall b : positive, QltT 0 (sqrt2_uniform_margin b).
Proof.
  intros b. unfold QltT, Qlt_bool, sqrt2_uniform_margin. cbn. reflexivity.
Qed.

(* Right cancellation of a positive factor, as an equation. *)
Lemma sqrt2_qmult_cancel_r : forall x S : Q, Qlt 0 S -> (x * S) * (/ S) == x.
Proof.
  intros x S H0.
  rewrite <- Qmult_assoc, (Qmult_inv_r S (Qnot_eq_sym 0 S (Qlt_not_eq 0 S H0))),
    Qmult_1_r.
  reflexivity.
Qed.

(* A rational whose square stays below two stays below [17/12]. *)
Lemma sqrt2_qlt_17_12_gen : forall q : Q, Qlt (q * q) 2%Q -> Qlt q (17 # 12)%Q.
Proof.
  intros q H.
  apply (sqrt2_sq_lt_inv (17 # 12)%Q q).
  - unfold Qle. cbn. lia.
  - apply (Qlt_trans _ 2%Q).
    + exact H.
    + unfold Qlt. cbn. lia.
Qed.

(* The rational square read-off: [(a # b)^2] compares as [a^2] against [2]. *)
Lemma sqrt2_qsq_lt : forall (a : Z) (b : positive),
  (a * a < 2 * (Z.pos b * Z.pos b))%Z -> Qlt ((a # b) * (a # b)) 2%Q.
Proof.
  intros a b H. unfold Qlt, Qmult. cbn [Qnum Qden].
  rewrite Pos2Z.inj_mul. lia.
Qed.

Lemma sqrt2_qsq_gt : forall (a : Z) (b : positive),
  (2 * (Z.pos b * Z.pos b) < a * a)%Z -> Qlt 2%Q ((a # b) * (a # b)).
Proof.
  intros a b H. unfold Qlt, Qmult. cbn [Qnum Qden].
  rewrite Pos2Z.inj_mul. lia.
Qed.


(* Integer square monotonicity on the nonnegative side. *)
Lemma sqrt2_zsq_le_inv : forall x y : Z,
  (0 <= x)%Z -> (0 <= y)%Z -> (y * y <= x * x)%Z -> (y <= x)%Z.
Proof.
  intros x y Hx0 Hy0 H.
  destruct (Z_le_gt_dec y x) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    assert (Hsq : (x * x < y * y)%Z) by (apply Z.mul_lt_mono_nonneg; lia).
    lia.
Qed.

(* Below-side rational placement: [a^2 < 2*b^2] puts [a # b] under [17/12]. *)
Lemma sqrt2_qlt_17_12 : forall (a : Z) (b : positive),
  (a * a < 2 * (Z.pos b * Z.pos b))%Z -> Qlt (a # b) (17 # 12)%Q.
Proof.
  intros a b Hlt.
  apply sqrt2_qlt_17_12_gen.
  apply sqrt2_qsq_lt.
  exact Hlt.
Qed.

(* The bracket width undercuts [1/(210*b^2)] at depth [2*b+7]:
   the denominator reaches [2^(n+1)] there. *)

Lemma sqrt2_den_zpow : forall n : nat,
  (Z.pos (sqrt2_den n) = (2 ^ Z.of_nat n) * 2)%Z.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [sqrt2_den].
    rewrite Pos2Z.inj_mul, IH.
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    lia.
Qed.

Lemma sqrt2_pow2_ge_nat : forall n : nat, (n <= 2 ^ n)%nat.
Proof.
  induction n as [|n IH]; simpl.
  - lia.
  - assert (H1 : (1 <= 2 ^ n)%nat) by (apply (Nat.pow_le_mono_r 2 0 n); lia).
    lia.
Qed.

(* The width denominator dominates [210*b^2] once the depth reaches
   [2*b+7]: it equals [2^(n+1)] there, and [2^(2*b+8) >= 210*b^2]. *)
Lemma sqrt2_den_210_nat : forall (n tn : nat),
  (2 * tn + 7 <= n)%nat -> (210 * tn * tn <= Pos.to_nat (sqrt2_den n))%nat.
Proof.
  intros n tn Hn.
  assert (Hden : (Pos.to_nat (sqrt2_den n) = 2 ^ (S n))%nat).
  { clear tn Hn.
    induction n as [|n IH].
    - reflexivity.
    - cbn [sqrt2_den].
      rewrite Pos2Nat.inj_mul, IH.
      replace (Pos.to_nat 2)%nat with 2%nat by reflexivity.
      replace (2 ^ S (S n))%nat with (2 * 2 ^ S n)%nat by reflexivity.
      lia. }
  rewrite Hden.
  assert (Hge : (tn <= 2 ^ tn)%nat) by apply sqrt2_pow2_ge_nat.
  apply (Nat.le_trans _ (2 ^ (2 * tn + 8))%nat).
  - replace (2 * tn + 8)%nat with (tn + (tn + 8))%nat by lia.
    rewrite Nat.pow_add_r.
    replace (tn + 8)%nat with (8 + tn)%nat by lia.
    rewrite Nat.pow_add_r.
    replace (2 ^ 8)%nat with 256%nat by reflexivity.
    assert (Hsq : (tn * tn <= 2 ^ tn * 2 ^ tn)%nat)
      by (apply (Nat.mul_le_mono tn (2 ^ tn) tn (2 ^ tn)); exact Hge).
    lia.
  - apply Nat.pow_le_mono_r.
    + lia.
    + lia.
Qed.

Lemma sqrt2_wQ_le_210 : forall (n : nat) (b : positive),
  (2 * Z.to_nat (Z.pos b) + 7 <= n)%nat ->
  Qle ((1 # sqrt2_den n)%Q) ((1 # (210 * b * b))%Q).
Proof.
  intros n b Hn.
  rewrite Z2Nat.inj_pos in Hn.
  assert (H210 := sqrt2_den_210_nat n (Pos.to_nat b) Hn).
  assert (Hz : (Z.pos (210 * b * b) <= Z.pos (sqrt2_den n))%Z).
  { rewrite <- (positive_nat_Z (210 * b * b)), <- (positive_nat_Z (sqrt2_den n)).
    apply (proj1 (Nat2Z.inj_le _ _)).
    rewrite (Pos2Nat.inj_mul (210 * b) b), (Pos2Nat.inj_mul 210 b).
    replace (Pos.to_nat 210)%nat with 210%nat by reflexivity.
    exact H210. }
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* Below case: the bracket's upper end keeps the margin plus the
   strictness slack above the rational, at every depth. *)
Lemma sqrt2_below_gap : forall (a : Z) (b : positive) (m : nat),
  (a * a < 2 * (Z.pos b * Z.pos b))%Z ->
  Qlt ((12 # (35 * b * b))%Q) (sqrt2_u m - (a # b))%Q.
Proof.
  intros a b m Hlt.
  assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Hgap : (1 <= 2 * (Z.pos b * Z.pos b) - a * a)%Z).
  { assert (Hne := sqrt2_int_gap_nonzero a b). lia. }
  assert (Hq2 : Qlt ((a # b) * (a # b)) 2%Q) by (apply sqrt2_qsq_lt; exact Hlt).
  assert (Hq17 : Qlt (a # b) (17 # 12)%Q) by (apply sqrt2_qlt_17_12; exact Hlt).
  assert (Hum2 : Qlt 2%Q (sqrt2_u m * sqrt2_u m)) by apply sqrt2_u_sq_gt.
  assert (Hum0 : Qle 0 (sqrt2_u m)).
  { apply (Qle_trans _ (sqrt2_l m)).
    + apply (Qle_trans _ 1%Q); [unfold Qle; cbn; lia | apply sqrt2_l_lb].
    + apply sqrt2_l_le_u. }
  assert (HS0 : Qlt 0 (sqrt2_u m + (a # b))%Q).
  { destruct (Qlt_le_dec 0 (a # b)) as [Hq0 | Hqn].
    - apply (Qlt_le_trans _ (sqrt2_u m)).
      + apply (Qlt_le_trans _ (1 # 1)%Q).
        * unfold Qlt. cbn. lia.
        * apply (Qle_trans _ (sqrt2_l m)).
          -- apply (Qle_trans _ 1%Q); [unfold Qle; cbn; lia | apply sqrt2_l_lb].
          -- apply sqrt2_l_le_u.
      + assert (Hle0 : Qle (sqrt2_u m + 0) (sqrt2_u m + (a # b))).
        { apply (Qplus_le_compat _ _ _ _ (Qle_refl _)).
          apply (Qlt_le_weak 0 _ Hq0). }
        rewrite Qplus_0_r in Hle0. exact Hle0.
    - assert (Hid2 : ((- (a # b)) * (- (a # b)) == (a # b) * (a # b))%Q) by ring.
      assert (Hnq2 : Qlt ((- (a # b)) * (- (a # b))) (sqrt2_u m * sqrt2_u m)).
      { rewrite Hid2. apply (Qlt_trans _ 2%Q); assumption. }
      assert (Hnqum : Qlt (- (a # b)) (sqrt2_u m))
        by (apply (sqrt2_sq_lt_inv (sqrt2_u m) (- (a # b)));
            [exact Hum0 | exact Hnq2]).
      assert (Hid3 : (sqrt2_u m + (a # b) == sqrt2_u m - (- (a # b)))%Q) by ring.
      rewrite Hid3.
      apply (proj1 (Qlt_minus_iff (- (a # b)) (sqrt2_u m))). exact Hnqum. }
  assert (HSlt : Qlt (sqrt2_u m + (a # b)) (35 # 12)%Q).
  { apply (sqrt2_qlt_transport_r _ ((3 # 2) + (17 # 12))%Q).
    - apply (Qle_lt_trans _ ((3 # 2) + (a # b))%Q).
      + apply (Qplus_le_compat _ _ _ _ (sqrt2_u_ub m)). apply Qle_refl.
      + apply (proj2 (Qplus_lt_r (a # b) (17 # 12) (3 # 2))). exact Hq17.
    - assert (Hid0 : ((3 # 2) + (17 # 12) == (35 # 12))%Q) by ring.
      exact Hid0. }
  assert (Hid : ((sqrt2_u m - (a # b)) * (sqrt2_u m + (a # b))
                 == sqrt2_u m * sqrt2_u m - (a # b) * (a # b))%Q) by ring.
  assert (HDS : Qlt ((1 # (b * b))%Q)
                  ((sqrt2_u m - (a # b)) * (sqrt2_u m + (a # b)))%Q).
  { rewrite Hid.
    apply (Qle_lt_trans _ (2 - (a # b) * (a # b))%Q).
    - assert (Hqq : ((a # b) * (a # b) == (a * a # (b * b)))%Q) by reflexivity.
      rewrite Hqq.
      assert (Hid4 : (2 - (a * a # (b * b))
                      == ((2 * (Z.pos b * Z.pos b) - a * a) # (b * b)))%Q).
      { unfold Qminus, Qopp, Qeq. cbn [Qnum Qden Qplus]. rewrite ?Pos2Z.inj_mul. ring. }
      rewrite Hid4.
      unfold Qle, Qmult. cbn [Qnum Qden].
      apply (Z.mul_le_mono_nonneg_r 1 (2 * (Z.pos b * Z.pos b) - a * a) (Z.pos (b * b))).
      + pose proof (Pos2Z.is_pos (b * b)); lia.
      + exact Hgap.
    - apply (Qplus_lt_le_compat _ _ _ _ Hum2 (Qle_refl _)). }
  assert (HDS0 : Qlt 0%Q
                  ((sqrt2_u m - (a # b)) * (sqrt2_u m + (a # b)))%Q).
  { apply (Qlt_trans _ ((1 # (b * b))%Q)).
    - unfold Qlt. cbn. lia.
    - exact HDS. }
  assert (HinvS0 : Qlt 0%Q (/ (sqrt2_u m + (a # b)))).
  { apply Qinv_lt_0_compat. exact HS0. }
  assert (HinvS : Qlt ((12 # 35)%Q) (/ (sqrt2_u m + (a # b)))).
  { assert (Hpre : Qlt (/ (35 # 12)) (/ (sqrt2_u m + (a # b)))).
    { apply (Qinv_lt_contravar (sqrt2_u m + (a # b)) (35 # 12)%Q).
      - exact HS0.
      - unfold Qlt. cbn. lia.
      - exact HSlt. }
    assert (Hidq : (/(35 # 12) == (12 # 35))%Q) by reflexivity.
    rewrite Hidq in Hpre. exact Hpre. }
  assert (Hid5 : ((1 # (b * b)) * (12 # 35) == (12 # (35 * b * b)))%Q).
  { unfold Qeq, Qmult. cbn [Qnum Qden].
    rewrite ?Pos2Z.inj_mul. ring. }
  apply (sqrt2_qlt_transport_r _ (((sqrt2_u m - (a # b))
                                    * (sqrt2_u m + (a # b)))
                                  * (/ (sqrt2_u m + (a # b))))%Q).
  + apply (Qlt_trans _ ((1 # (b * b)) * / (sqrt2_u m + (a # b)))%Q).
    * rewrite <- Hid5.
      rewrite (Qmult_comm (1 # (b * b)) (12 # 35)).
      rewrite (Qmult_comm (1 # (b * b)) (/ (sqrt2_u m + (a # b)))).
      apply (Qmult_lt_compat_r _ _ _).
      -- unfold Qlt. cbn. lia.
      -- exact HinvS.
    * apply (Qmult_lt_compat_r _ _ _).
      -- exact HinvS0.
      -- exact HDS.
  + apply sqrt2_qmult_cancel_r. exact HS0.
Qed.

(* Below case, negative numerator: the distance exceeds two. *)
Lemma sqrt2_below_gap_neg : forall (a : Z) (b : positive) (m : nat),
  (2 * (Z.pos b * Z.pos b) < a * a)%Z -> (a <= 0)%Z ->
  Qlt ((sqrt2_uniform_margin b) + (5 # 6)%Q) (sqrt2_u m - (a # b))%Q.
Proof.
  intros a b m Habove Han.
  assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Hab : (a <= - Z.pos b)%Z).
  { destruct (Z_le_gt_dec (- Z.pos b) a) as [Hle | Hgt].
    - exfalso.
      assert (Hna0 : (0 <= - a)%Z) by lia.
      assert (Hsq : ((- a) * (- a) <= Z.pos b * Z.pos b)%Z)
        by (apply Z.mul_le_mono_nonneg; lia).
      assert (Hidr : (a * a = (- a) * (- a))%Z) by ring.
      rewrite Hidr in Habove. lia.
    - lia. }
  assert (Hq1 : Qle (a # b) (- (1 # 1))%Q).
  { unfold Qle, Qmult. cbn [Qnum Qden Qopp]. lia. }
  assert (Hum1 : Qle (1 # 1) (sqrt2_u m))
    by (apply (Qle_trans _ (sqrt2_l m)); [apply sqrt2_l_lb | apply sqrt2_l_le_u]).
  assert (Hge : Qle 2%Q (sqrt2_u m - (a # b))%Q).
  { apply (proj2 (Qle_minus_iff 2%Q (sqrt2_u m - (a # b)))).
    assert (Hid : ((sqrt2_u m - (a # b)) - 2
                    == (sqrt2_u m - (1 # 1)) + ((- (1 # 1)) - (a # b)))%Q) by ring.
    rewrite Hid.
    apply (Qplus_le_compat 0%Q _ 0%Q _).
    - apply (proj1 (Qle_minus_iff (1 # 1) (sqrt2_u m))). exact Hum1.
    - apply (proj1 (Qle_minus_iff (a # b) (- (1 # 1)))). exact Hq1. }
  apply (Qlt_le_trans _ 2%Q).
  - assert (Hm : Qle (sqrt2_uniform_margin b) (1 # 3)%Q).
    { unfold Qle, sqrt2_uniform_margin. cbn [Qnum Qden]. rewrite ?Pos2Z.inj_mul. nia. }
    apply (Qle_lt_trans _ ((1 # 3) + (5 # 6))%Q).
    + apply (Qplus_le_compat _ _ _ _ Hm (Qle_refl _)).
    + assert (Hid0 : ((1 # 3) + (5 # 6) == (7 # 6))%Q) by ring.
      rewrite Hid0. unfold Qlt. cbn. lia.
  - exact Hge.
Qed.

(* Above case, far branch: beyond [3/2] the distance exceeds [1/(2*b)]. *)
Lemma sqrt2_above_gap_far : forall (a : Z) (b : positive) (m : nat),
  (0 < a)%Z -> (2 * (Z.pos b * Z.pos b) < a * a)%Z -> (3 * Z.pos b < 2 * a)%Z ->
  Qle ((sqrt2_uniform_margin b) + (1 # (6 * b * b))%Q)
      ((a # b) - sqrt2_u m)%Q.
Proof.
  intros a b m Hap Habove Hfar.
  assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (HumUb : Qle (sqrt2_u m) (3 # 2)%Q) by apply sqrt2_u_ub.
  assert (Hstep : Qle ((sqrt2_uniform_margin b) + (1 # (6 * b * b))%Q)
                    ((a # b) - (3 # 2))%Q).
  { unfold Qle, Qminus, Qmult, sqrt2_uniform_margin.
    cbn [Qnum Qden Qplus Qopp].
    rewrite ?Pos2Z.inj_mul.
    assert (Hb1 : (1 <= Z.pos b)%Z) by lia.
    assert (Hd1 : (1 <= a * 2 + - (3) * Z.pos b)%Z) by lia.
    assert (Hpr : (Z.pos b * 1 <= Z.pos b * (a * 2 + - (3) * Z.pos b))%Z)
      by (apply Z.mul_le_mono_nonneg_l; lia).
    nia. }
  apply (Qle_trans _ ((a # b) - (3 # 2))%Q).
  - exact Hstep.
  - apply (sqrt2_qle_lsub _ _ _ HumUb).
Qed.

(* Above case, near branch: between the root and [3/2] the conjugate
   identity carries the margin, with the bracket width as the only
   depth-dependent correction. *)
Lemma sqrt2_above_gap_near : forall (a : Z) (b : positive) (m : nat),
  (0 < a)%Z -> (2 * (Z.pos b * Z.pos b) < a * a)%Z -> (2 * a <= 3 * Z.pos b)%Z ->
  (2 * Z.to_nat (Z.pos b) + 7 <= m)%nat ->
  Qlt ((sqrt2_uniform_margin b) + (1 # (210 * b * b))%Q)
      ((a # b) - sqrt2_u m)%Q.
Proof.
  intros a b m Hap Habove Hnear Hm.
  assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Hq2 : Qlt 2%Q ((a # b) * (a # b))) by (apply sqrt2_qsq_gt; exact Habove).
  assert (Hq32 : Qle (a # b) (3 # 2)%Q).
  { unfold Qle, Qmult. cbn [Qnum Qden Qopp]. lia. }
  assert (Hl2 : Qlt (sqrt2_l m * sqrt2_l m) 2%Q) by apply sqrt2_l_sq_lt.
  assert (Hl17 : Qlt (sqrt2_l m) (17 # 12)%Q) by (apply sqrt2_qlt_17_12_gen; exact Hl2).
  assert (Hl0 : Qle 0 (sqrt2_l m))
    by (apply (Qle_trans _ 1%Q); [unfold Qle; cbn; lia | apply sqrt2_l_lb]).
  assert (Hgap : (1 <= a * a - 2 * (Z.pos b * Z.pos b))%Z).
  { assert (Hne := sqrt2_int_gap_nonzero a b). lia. }
  assert (Hq0 : Qlt 0 (a # b)) by (unfold Qlt; cbn; lia).
  assert (Hlpos : Qlt 0 ((a # b) + sqrt2_l m)%Q).
  { apply (Qlt_le_trans _ (a # b)).
    - exact Hq0.
    - assert (Hle0 : Qle ((a # b) + 0) ((a # b) + sqrt2_l m)).
      { apply (Qplus_le_compat _ _ _ _ (Qle_refl _)). exact Hl0. }
      rewrite Qplus_0_r in Hle0. exact Hle0. }
  assert (Hid : (((a # b) - sqrt2_l m) * ((a # b) + sqrt2_l m)
                 == (a # b) * (a # b) - sqrt2_l m * sqrt2_l m)%Q) by ring.
  assert (HQ : Qlt ((1 # (b * b))%Q)
                 ((a # b) * (a # b) - sqrt2_l m * sqrt2_l m)%Q).
  { apply (Qle_lt_trans _ ((a # b) * (a # b) - 2%Q)).
    - assert (Hqq : ((a # b) * (a # b) == (a * a # (b * b)))%Q) by reflexivity.
      rewrite Hqq.
      assert (Hid4 : ((a * a # (b * b)) - 2
                      == ((a * a - 2 * (Z.pos b * Z.pos b)) # (b * b)))%Q).
      { unfold Qminus, Qopp, Qeq. cbn [Qnum Qden Qplus]. rewrite ?Pos2Z.inj_mul. ring. }
      rewrite Hid4.
      unfold Qle, Qmult. cbn [Qnum Qden].
      apply (Z.mul_le_mono_nonneg_r 1 (a * a - 2 * (Z.pos b * Z.pos b)) (Z.pos (b * b))).
      + pose proof (Pos2Z.is_pos (b * b)); lia.
      + exact Hgap.
    - assert (Hr1 : ((a # b) * (a # b) - 2%Q
                     == (a # b) * (a # b) + (-2)%Q)%Q) by ring.
      rewrite Hr1.
      assert (Hr2 : ((a # b) * (a # b) - sqrt2_l m * sqrt2_l m
                     == (a # b) * (a # b) + (- (sqrt2_l m * sqrt2_l m))%Q)) by ring.
      rewrite Hr2.
      apply (proj2 (Qplus_lt_r (-2)%Q (-(sqrt2_l m * sqrt2_l m))%Q
                      ((a # b) * (a # b))%Q)).
      apply (Qopp_lt_compat _ _ Hl2). }
  assert (HDS : Qlt ((1 # (b * b))%Q)
                  (((a # b) - sqrt2_l m) * ((a # b) + sqrt2_l m))%Q).
  { apply (sqrt2_qlt_transport_r _ ((a # b) * (a # b) - sqrt2_l m * sqrt2_l m)%Q).
    - exact HQ.
    - exact (Qeq_sym _ _ Hid). }
  assert (Hlsum : Qle ((a # b) + sqrt2_l m) (35 # 12)%Q).
  { apply (Qle_trans _ ((3 # 2) + (17 # 12))%Q).
    - apply (Qplus_le_compat _ _ _ _ Hq32 (Qlt_le_weak _ _ Hl17)).
    - assert (Hid0 : ((3 # 2) + (17 # 12) == (35 # 12))%Q) by ring.
      rewrite Hid0. apply Qle_refl. }
  assert (HD' : Qlt ((12 # (35 * b * b))%Q) ((a # b) - sqrt2_l m)%Q).
  { apply (sqrt2_qlt_transport_r _ (((a # b) - sqrt2_l m)
                                      * ((a # b) + sqrt2_l m)
                                    * (/ ((a # b) + sqrt2_l m)))%Q).
    + apply (Qlt_trans _ ((1 # (b * b)) * / ((a # b) + sqrt2_l m))%Q).
      * assert (HinvS : Qlt ((12 # 35)%Q) (/ ((a # b) + sqrt2_l m))).
        { assert (Hpre : Qlt (/ (35 # 12)) (/ ((a # b) + sqrt2_l m))).
          { apply (Qinv_lt_contravar ((a # b) + sqrt2_l m) (35 # 12)%Q).
            - exact Hlpos.
            - unfold Qlt. cbn. lia.
            - assert (Hst : Qlt (sqrt2_l m + (a # b)) ((17 # 12) + (3 # 2))%Q)
                by (apply (Qplus_lt_le_compat _ _ _ _ Hl17 Hq32)).
              assert (Hidc1 : (sqrt2_l m + (a # b) == (a # b) + sqrt2_l m)%Q) by ring.
              assert (Hidc2 : ((17 # 12) + (3 # 2) == (35 # 12))%Q) by ring.
              rewrite Hidc1 in Hst. rewrite Hidc2 in Hst. exact Hst. }
          assert (Hidq : (/(35 # 12) == (12 # 35))%Q) by reflexivity.
          rewrite Hidq in Hpre. exact Hpre. }
        assert (Hid5 : ((1 # (b * b)) * (12 # 35) == (12 # (35 * b * b)))%Q).
        { unfold Qeq, Qmult. cbn [Qnum Qden].
          rewrite ?Pos2Z.inj_mul. ring. }
        rewrite <- Hid5.
        rewrite (Qmult_comm (1 # (b * b)) (12 # 35)).
        rewrite (Qmult_comm (1 # (b * b)) (/ ((a # b) + sqrt2_l m))).
        apply (Qmult_lt_compat_r _ _ _).
        -- unfold Qlt. cbn. lia.
        -- exact HinvS.
      * apply (Qmult_lt_compat_r _ _ _).
        -- apply Qinv_lt_0_compat. exact Hlpos.
        -- exact HDS.
    + apply sqrt2_qmult_cancel_r. exact Hlpos. }
  assert (Hw210 := sqrt2_wQ_le_210 m b Hm).
  assert (Hsub : Qlt ((12 # (35 * b * b))%Q - (1 # sqrt2_den m)%Q)
                   (((a # b) - sqrt2_l m) - (1 # sqrt2_den m)%Q)).
  { apply (proj2 (Qlt_minus_iff _ _)).
    assert (Hid8 : (((a # b) - sqrt2_l m) - (1 # sqrt2_den m)
                    - ((12 # (35 * b * b)) - (1 # sqrt2_den m))
                    == ((a # b) - sqrt2_l m) - (12 # (35 * b * b)))%Q) by ring.
    rewrite Hid8.
    exact (proj1 (Qlt_minus_iff (12 # (35 * b * b))%Q
                  ((a # b) - sqrt2_l m)%Q) HD'). }
  apply (Qle_lt_trans _ ((12 # (35 * b * b))%Q - (1 # sqrt2_den m)%Q)).
  - apply (Qle_trans _ ((12 # (35 * b * b))%Q - (1 # (210 * b * b))%Q)).
    + assert (Hid6 : ((sqrt2_uniform_margin b) + (1 # (210 * b * b))
                      == (12 # (35 * b * b)) - (1 # (210 * b * b)))%Q)
        by (unfold sqrt2_uniform_margin, Qeq, Qminus, Qmult;
            cbn [Qnum Qden Qplus Qopp];
            rewrite ?Pos2Z.inj_mul; ring).
      rewrite Hid6. apply Qle_refl.
    + apply (sqrt2_qle_lsub (1 # sqrt2_den m)%Q (1 # (210 * b * b))%Q
               (12 # (35 * b * b))%Q).
      exact Hw210.
  - apply (Qlt_le_trans _ (((a # b) - sqrt2_l m) - (1 # sqrt2_den m))%Q).
    + exact Hsub.
    + rewrite <- (sqrt2_width m).
      assert (Hid7 : (((a # b) - sqrt2_l m) - (sqrt2_u m - sqrt2_l m)
                      == (a # b) - sqrt2_u m)%Q) by ring.
      rewrite Hid7. apply Qle_refl.
Qed.

(* ================= Section 6. The uniform strong irrationality ============ *)

(* The minus-sequence read-off equations (the witness bridge). *)
Lemma sqrt2_seq_minus_r : forall (q : Q) (n : Z),
  seq (CReal_minus sqrt2_cr (inject_Q q)) n == sqrt2_seq (n - 1) - q.
Proof.
  intros q n.
  unfold CReal_minus, CReal_plus.
  cbn [seq].
  unfold CReal_opp, CReal_plus_seq, CReal_opp_seq.
  cbn [seq].
  rewrite Qred_correct. reflexivity.
Qed.

Lemma sqrt2_seq_minus_l : forall (q : Q) (n : Z),
  seq (CReal_minus (inject_Q q) sqrt2_cr) n == q - sqrt2_seq (n - 1).
Proof.
  intros q n.
  unfold CReal_minus, CReal_plus.
  cbn [seq].
  unfold CReal_opp, CReal_plus_seq, CReal_opp_seq.
  cbn [seq].
  rewrite Qred_correct. reflexivity.
Qed.

(* The halved-index step: a strict margin at index [n] persists at
   [n - 1] with the doubled resolution. *)
Lemma sqrt2_index_step : forall (X : Q) (n : Z),
  Qlt (2 * 2 ^ n) X -> Qlt (2 * 2 ^ (n - 1)) X.
Proof.
  intros X n H.
  apply (Qlt_le_trans _ (2 * 2 ^ n)%Q).
  - assert (Hid : (2 * 2 ^ (n - 1) == 2 ^ n)%Q).
    { replace (2 * 2 ^ (n - 1))%Q with (2 ^ 1 * 2 ^ (n - 1))%Q by reflexivity.
      rewrite <- Qpower_plus by (unfold Qeq; cbn; discriminate).
      replace (1 + (n - 1))%Z with n%Z by lia.
      reflexivity. }
    rewrite Hid.
    rewrite <- (Qmult_1_l (2 ^ n)) at 1.
    apply (Qmult_lt_compat_r 1 2 (2 ^ n)).
    + apply Qpower_0_lt; unfold Qlt; cbn; lia.
    + unfold Qlt. cbn. lia.
  - exact (Qlt_le_weak _ _ H).
Qed.

(* The archimedean witness depth: for every positive rational [X]
   there is a depth [m] with [2 * 2^(1-m) < X] — the CRealLt threshold
   at the shifted index [1 - m].  The archimedean index [j] of [X]
   itself provides the depth: below the shift the threshold matches
   [2 ^ j] exactly, and past the shift the depth-zero threshold
   [2 * 2^1 = 4] is already below [X].  The premise is carried by the
   reflected decision [QltT]; the statement face is Set-carried
   throughout. *)
Lemma sqrt2_witness_depth : forall X : Q, QltT 0 X ->
  sigT (fun m : nat => QltT (2 * 2 ^ (1 - Z.of_nat m)) X).
Proof.
  intros X HX0T.
  assert (HX0 : Qlt 0 X) by (apply QltT_to_Qlt; exact HX0T).
  destruct (QarchimedeanLowExp2_Z X HX0) as [j Hj].
  destruct (Z_le_gt_dec 2 j) as [Hbig | Hsmall].
  - (* [2 <= j]: the depth-zero threshold [2 * 2^1] is below [X] *)
    exists 0%nat.
    apply Qlt_to_QltT.
    assert (Hid : (2 * 2 ^ (1 - Z.of_nat 0) == 2 ^ 2)%Q).
    { replace (2)%Q with (2 ^ 1)%Q by reflexivity.
      rewrite <- Qpower_plus by (unfold Qeq; cbn; discriminate).
      replace (1 + (1 - Z.of_nat 0))%Z with 2%Z by (cbn; lia).
      reflexivity. }
    rewrite Hid.
    assert (Hpow : Qle (2 ^ 2)%Q (2 ^ j)%Q)
      by (apply Qpower_le_compat_l; [lia | unfold Qle; cbn; lia]).
    apply (Qle_lt_trans _ (2 ^ j)%Q); [exact Hpow | exact Hj].
  - (* [j < 2]: the shifted depth [2 - j] lands on [2 ^ j] exactly *)
    exists (Z.to_nat (2 - j)).
    assert (Hm : (Z.of_nat (Z.to_nat (2 - j)) = 2 - j)%Z)
      by (apply Z2Nat.id; lia).
    apply Qlt_to_QltT.
    replace (1 - Z.of_nat (Z.to_nat (2 - j)))%Z with (j - 1)%Z
      by (rewrite Hm; lia).
    replace (2)%Q with (2 ^ 1)%Q by reflexivity.
    rewrite <- Qpower_plus by (unfold Qeq; cbn; discriminate).
    replace (1 + (j - 1))%Z with j%Z by lia.
    exact Hj.
Qed.

(* The four margin witnesses, one per rational placement branch.
   The placement side conditions are carried by the reflected
   decisions [QltT]/[QleT'] (Set-carried statement faces); the proofs
   recover the integer comparisons locally, feeding the [Z]-faced
   gap lemmas of Section 5. *)
Lemma sqrt2_margin_below_witness : forall (a : Z) (b : positive),
  QltT ((a # b) * (a # b)) 2%Q ->
  CRealLtT (inject_Q (sqrt2_uniform_margin b))
           (CReal_minus sqrt2_cr (inject_Q (a # b))).
Proof.
  intros a b HabT.
  assert (Hlt : (a * a < 2 * (Z.pos b * Z.pos b))%Z).
  { apply QltT_to_Qlt in HabT. unfold Qlt in HabT. cbn in HabT.
    rewrite Z.mul_1_r in HabT. exact HabT. }
  assert (HX0T : QltT 0 ((1 # (105 * b * b))%Q))
    by (apply Qlt_to_QltT; unfold Qlt; cbn; lia).
  destruct (sqrt2_witness_depth ((1 # (105 * b * b))%Q) HX0T) as [m Hm].
  assert (Hgap := sqrt2_below_gap a b m Hlt).
  exists (1 - Z.of_nat m)%Z.
  apply Qlt_to_QltT.
  rewrite sqrt2_seq_minus_r.
  cbn [seq inject_Q].
  replace (1 - Z.of_nat m - 1)%Z with (- Z.of_nat m)%Z by ring.
  rewrite sqrt2_seq_negtail.
  cbn [seq inject_Q].
  assert (Hle : Qle (sqrt2_uniform_margin b + (1 # (105 * b * b))%Q)
                  (sqrt2_u m - (a # b))%Q).
  { apply (proj2 (Qle_minus_iff (sqrt2_uniform_margin b + (1 # (105 * b * b))%Q)
                  (sqrt2_u m - (a # b))%Q)).
    assert (HidR : ((sqrt2_u m - (a # b)) - (sqrt2_uniform_margin b + (1 # (105 * b * b)))
                    == (sqrt2_u m - (a # b)) - (12 # (35 * b * b)))%Q)
      by (unfold sqrt2_uniform_margin, Qeq, Qminus, Qmult;
          cbn [Qnum Qden Qplus Qopp];
          rewrite ?Pos2Z.inj_mul; ring).
    rewrite HidR.
    apply (Qlt_le_weak _ _).
    exact (proj1 (Qlt_minus_iff (12 # (35 * b * b))%Q
                  (sqrt2_u m - (a # b))%Q) Hgap). }
  apply (Qlt_le_trans _ ((1 # (105 * b * b))%Q)).
  - apply QltT_to_Qlt. exact Hm.
  - apply (proj2 (Qle_minus_iff (1 # (105 * b * b))%Q
                  ((sqrt2_u m - (a # b)) - sqrt2_uniform_margin b)%Q)).
    assert (HidR2 : (((sqrt2_u m - (a # b)) - sqrt2_uniform_margin b)
                     - (1 # (105 * b * b))
                     == (sqrt2_u m - (a # b))
                        - (sqrt2_uniform_margin b + (1 # (105 * b * b))))%Q) by ring.
    rewrite HidR2.
    exact (proj1 (Qle_minus_iff (sqrt2_uniform_margin b + (1 # (105 * b * b))%Q)
                  (sqrt2_u m - (a # b))%Q) Hle).
Qed.

Lemma sqrt2_margin_below_neg_witness : forall (a : Z) (b : positive),
  QltT 2%Q ((a # b) * (a # b)) -> QleT' (a # b) 0%Q ->
  CRealLtT (inject_Q (sqrt2_uniform_margin b))
           (CReal_minus sqrt2_cr (inject_Q (a # b))).
Proof.
  intros a b HabT HanT.
  assert (Habove : (2 * (Z.pos b * Z.pos b) < a * a)%Z).
  { apply QltT_to_Qlt in HabT. unfold Qlt in HabT. cbn in HabT.
    rewrite !Z.mul_1_r in HabT. exact HabT. }
  assert (Han : (a <= 0)%Z).
  { apply QleT'_to_Qle in HanT. unfold Qle in HanT. cbn in HanT. lia. }
  assert (HX0T : QltT 0 (5 # 6)%Q)
    by (apply Qlt_to_QltT; unfold Qlt; cbn; lia).
  destruct (sqrt2_witness_depth (5 # 6)%Q HX0T) as [m Hm].
  assert (Hgap := sqrt2_below_gap_neg a b m Habove Han).
  exists (1 - Z.of_nat m)%Z.
  apply Qlt_to_QltT.
  rewrite sqrt2_seq_minus_r.
  cbn [seq inject_Q].
  replace (1 - Z.of_nat m - 1)%Z with (- Z.of_nat m)%Z by ring.
  rewrite sqrt2_seq_negtail.
  cbn [seq inject_Q].
  apply (Qlt_le_trans _ (5 # 6)%Q).
  - apply QltT_to_Qlt. exact Hm.
  - apply (proj2 (Qle_minus_iff (5 # 6)%Q
                    ((sqrt2_u m - (a # b)) - sqrt2_uniform_margin b)%Q)).
    assert (HidR : (((sqrt2_u m - (a # b)) - sqrt2_uniform_margin b) - (5 # 6)
                    == (sqrt2_u m - (a # b))
                       - (sqrt2_uniform_margin b + (5 # 6)))%Q) by ring.
    rewrite HidR.
    apply (Qlt_le_weak _ _).
    exact (proj1 (Qlt_minus_iff (sqrt2_uniform_margin b + (5 # 6)%Q)
                  (sqrt2_u m - (a # b))%Q) Hgap).
Qed.

Lemma sqrt2_margin_above_far_witness : forall (a : Z) (b : positive),
  QltT 0 (a # b) -> QltT 2%Q ((a # b) * (a # b)) ->
  QltT (3 # 2)%Q (a # b) ->
  CRealLtT (inject_Q (sqrt2_uniform_margin b))
           (CReal_minus (inject_Q (a # b)) sqrt2_cr).
Proof.
  intros a b HapT HabT HfarT.
  assert (Hap : (0 < a)%Z).
  { apply QltT_to_Qlt in HapT. unfold Qlt in HapT. cbn in HapT.
    rewrite Z.mul_1_r in HapT. exact HapT. }
  assert (Habove : (2 * (Z.pos b * Z.pos b) < a * a)%Z).
  { apply QltT_to_Qlt in HabT. unfold Qlt in HabT. cbn in HabT.
    rewrite !Z.mul_1_r in HabT. exact HabT. }
  assert (Hfar : (3 * Z.pos b < 2 * a)%Z).
  { apply QltT_to_Qlt in HfarT. unfold Qlt in HfarT. cbn in HfarT. lia. }
  assert (HX0T : QltT 0 ((1 # (6 * b * b))%Q))
    by (apply Qlt_to_QltT; unfold Qlt; cbn; lia).
  destruct (sqrt2_witness_depth ((1 # (6 * b * b))%Q) HX0T) as [m Hm].
  assert (Hgap := sqrt2_above_gap_far a b m Hap Habove Hfar).
  exists (1 - Z.of_nat m)%Z.
  apply Qlt_to_QltT.
  rewrite sqrt2_seq_minus_l.
  cbn [seq inject_Q].
  replace (1 - Z.of_nat m - 1)%Z with (- Z.of_nat m)%Z by ring.
  rewrite sqrt2_seq_negtail.
  cbn [seq inject_Q].
  apply (Qlt_le_trans _ (1 # (6 * b * b))%Q).
  - apply QltT_to_Qlt. exact Hm.
  - apply (proj2 (Qle_minus_iff (1 # (6 * b * b))%Q
                    ((a # b) - sqrt2_u m - sqrt2_uniform_margin b)%Q)).
    assert (HidR : (((a # b) - sqrt2_u m - sqrt2_uniform_margin b) - (1 # (6 * b * b))
                    == (a # b) - sqrt2_u m
                       - (sqrt2_uniform_margin b + (1 # (6 * b * b))))%Q)
      by ring.
    rewrite HidR.
    exact (proj1 (Qle_minus_iff (sqrt2_uniform_margin b + (1 # (6 * b * b))%Q)
                  ((a # b) - sqrt2_u m)%Q) Hgap).
Qed.

Lemma sqrt2_margin_above_near_witness : forall (a : Z) (b : positive),
  QltT 0 (a # b) -> QltT 2%Q ((a # b) * (a # b)) ->
  QleT' (a # b) (3 # 2)%Q ->
  CRealLtT (inject_Q (sqrt2_uniform_margin b))
           (CReal_minus (inject_Q (a # b)) sqrt2_cr).
Proof.
  intros a b HapT HabT HnearT.
  assert (Hap : (0 < a)%Z).
  { apply QltT_to_Qlt in HapT. unfold Qlt in HapT. cbn in HapT.
    rewrite Z.mul_1_r in HapT. exact HapT. }
  assert (Habove : (2 * (Z.pos b * Z.pos b) < a * a)%Z).
  { apply QltT_to_Qlt in HabT. unfold Qlt in HabT. cbn in HabT.
    rewrite !Z.mul_1_r in HabT. exact HabT. }
  assert (Hnear : (2 * a <= 3 * Z.pos b)%Z).
  { apply QleT'_to_Qle in HnearT. unfold Qle in HnearT. cbn in HnearT. lia. }
  assert (HX0T : QltT 0 ((1 # (210 * b * b))%Q))
    by (apply Qlt_to_QltT; unfold Qlt; cbn; lia).
  destruct (sqrt2_witness_depth ((1 # (210 * b * b))%Q) HX0T) as [m0 Hm0].
  assert (Hm1 : (2 * Z.to_nat (Z.pos b) + 7
                 <= Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0)%nat) by apply Nat.le_max_l.
  assert (Hm2 : (m0 <= Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0)%nat) by apply Nat.le_max_r.
  assert (Hgap := sqrt2_above_gap_near a b (Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0)
                    Hap Habove Hnear Hm1).
  exists (1 - Z.of_nat (Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0))%Z.
  apply Qlt_to_QltT.
  rewrite sqrt2_seq_minus_l.
  cbn [seq inject_Q].
  replace (1 - Z.of_nat (Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0) - 1)%Z
    with (- Z.of_nat (Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0))%Z by ring.
  rewrite sqrt2_seq_negtail.
  cbn [seq inject_Q].
  apply (Qlt_le_trans _ (1 # (210 * b * b))%Q).
  - apply (Qle_lt_trans _ (2 * 2 ^ (1 - Z.of_nat m0))%Q).
    + rewrite (Qmult_comm 2 (2 ^ (1 - Z.of_nat (Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0)))).
      rewrite (Qmult_comm 2 (2 ^ (1 - Z.of_nat m0))).
      apply (Qmult_le_compat_r _ _ (2 # 1)%Q).
      * apply Qpower_le_compat_l; [lia | unfold Qle; cbn; lia].
      * unfold Qle. cbn. lia.
    + apply QltT_to_Qlt. exact Hm0.
  - apply (proj2 (Qle_minus_iff (1 # (210 * b * b))%Q
                    ((a # b) - sqrt2_u (Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0)
                       - sqrt2_uniform_margin b)%Q)).
    assert (HidR : (((a # b) - sqrt2_u (Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0)
                       - sqrt2_uniform_margin b) - (1 # (210 * b * b))
                    == (a # b) - sqrt2_u (Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0)
                       - (sqrt2_uniform_margin b + (1 # (210 * b * b))))%Q)
      by ring.
    rewrite HidR.
    apply (Qlt_le_weak _ _).
    exact (proj1 (Qlt_minus_iff (sqrt2_uniform_margin b + (1 # (210 * b * b))%Q)
                  ((a # b) - sqrt2_u (Nat.max (2 * Z.to_nat (Z.pos b) + 7) m0))%Q) Hgap).
Qed.

(* The main statement: the margin [sqrt2_uniform_margin b] — a function
   of the denominator height [b] alone — strictly undercuts the distance
   between [sqrt2_cr] and every embedded rational [a # b], on one of the
   two sides (a Set-carried sum; no order decision on the reals is used). *)
Theorem sqrt2_uniform_strong_irrationality :
  forall (a : Z) (b : positive),
    (CRealLtT (inject_Q (sqrt2_uniform_margin b))
              (CReal_minus sqrt2_cr (inject_Q (a # b)))
     + CRealLtT (inject_Q (sqrt2_uniform_margin b))
              (CReal_minus (inject_Q (a # b)) sqrt2_cr))%type.
Proof.
  intros a b.
  destruct (Z_lt_ge_dec (a * a) (2 * (Z.pos b * Z.pos b))) as [Hbelow | Habove].
  - left. apply (sqrt2_margin_below_witness a b).
    apply Qlt_to_QltT. apply sqrt2_qsq_lt. exact Hbelow.
  - assert (Habove' : (2 * (Z.pos b * Z.pos b) < a * a)%Z).
    { destruct (Z.eq_dec (a * a) (2 * (Z.pos b * Z.pos b))) as [Heq | Hne].
      - exact (False_ind _ (sqrt2_int_gap_nonzero a b Heq)).
      - lia. }
    assert (HabT : QltT 2%Q ((a # b) * (a # b))).
    { apply Qlt_to_QltT. apply sqrt2_qsq_gt. exact Habove'. }
    destruct (Z_le_gt_dec a 0) as [Han | Hap].
    + left. apply (sqrt2_margin_below_neg_witness a b); [exact HabT |].
      apply Qle_to_QleT'. unfold Qle. cbn. lia.
    + destruct (Z_lt_ge_dec (3 * Z.pos b) (2 * a)) as [Hfar | Hnear].
      * right. apply (sqrt2_margin_above_far_witness a b).
        -- apply Qlt_to_QltT. unfold Qlt. cbn. lia.
        -- exact HabT.
        -- apply Qlt_to_QltT. unfold Qlt. cbn. lia.
      * right. apply (sqrt2_margin_above_near_witness a b).
        -- apply Qlt_to_QltT. unfold Qlt. cbn. lia.
        -- exact HabT.
        -- apply Qle_to_QleT'. unfold Qle. cbn. lia.
Defined.

(* The apartness corollary in the shape of [PiSeparation]: the margin
   witness doubles as an apartness certificate. *)
Corollary sqrt2_cr_appart_all_Q :
  forall q : Q, CReal_appart sqrt2_cr (inject_Q q).
Proof.
  intros q. destruct q as [qn qd].
  assert (Hpos : Qlt 0%Q (sqrt2_uniform_margin qd))
    by (apply QltT_to_Qlt, sqrt2_margin_pos).
  destruct (sqrt2_uniform_strong_irrationality qn qd) as [H | H].
  - right.
    destruct H as [n Hn].
    apply QltT_to_Qlt in Hn.
    rewrite sqrt2_seq_minus_r in Hn.
    exists (n - 1)%Z.
    apply (Qlt_trans _ (sqrt2_seq (n - 1) - (qn # qd) - sqrt2_uniform_margin qd)%Q).
    + apply (sqrt2_index_step _ n). exact Hn.
    + apply (proj2 (Qlt_minus_iff (sqrt2_seq (n - 1) - (qn # qd)
                                      - sqrt2_uniform_margin qd)%Q
                      (sqrt2_seq (n - 1) - (qn # qd))%Q)).
      assert (HidC : ((sqrt2_seq (n - 1) - (qn # qd))
                      - ((sqrt2_seq (n - 1) - (qn # qd))
                         - sqrt2_uniform_margin qd)
                      == sqrt2_uniform_margin qd)%Q) by ring.
      rewrite HidC. exact Hpos.
  - left.
    destruct H as [n Hn].
    apply QltT_to_Qlt in Hn.
    rewrite sqrt2_seq_minus_l in Hn.
    exists (n - 1)%Z.
    apply (Qlt_trans _ ((qn # qd) - sqrt2_seq (n - 1) - sqrt2_uniform_margin qd)%Q).
    + apply (sqrt2_index_step _ n). exact Hn.
    + apply (proj2 (Qlt_minus_iff ((qn # qd) - sqrt2_seq (n - 1)
                                      - sqrt2_uniform_margin qd)%Q
                      ((qn # qd) - sqrt2_seq (n - 1))%Q)).
      assert (HidC2 : (((qn # qd) - sqrt2_seq (n - 1))
                       - (((qn # qd) - sqrt2_seq (n - 1))
                          - sqrt2_uniform_margin qd)
                       == sqrt2_uniform_margin qd)%Q) by ring.
      rewrite HidC2. exact Hpos.
Qed.

(* The strong irrationality statement in the exact shape of
   [PiSeparation]'s main theorem. *)
Theorem sqrt2_strong_irrational_prop :
  forall a b : Q, b <> 0 -> CReal_appart sqrt2_cr (inject_Q (a / b)).
Proof.
  intros a b _. apply sqrt2_cr_appart_all_Q.
Defined.

(* ================= Section 7. Kernel evaluation transcript ============ *)

(* The margin values at the sample denominator heights. *)
Eval vm_compute in (sqrt2_uniform_margin 1, sqrt2_uniform_margin 2,
                    sqrt2_uniform_margin 7, sqrt2_uniform_margin 113).

(* The witness sides at the sample rationals: [1/2] below the
   root (b = 2), [3/2] above (b = 2), [22/7] above (b = 7),
   [355/113] above (b = 113). *)
Eval vm_compute in
  (match sqrt2_uniform_strong_irrationality 1 2 with
   | inl _ => true | inr _ => false end,
   match sqrt2_uniform_strong_irrationality 3 2 with
   | inl _ => true | inr _ => false end,
   match sqrt2_uniform_strong_irrationality 22 7 with
   | inl _ => true | inr _ => false end,
   match sqrt2_uniform_strong_irrationality 355 113 with
   | inl _ => true | inr _ => false end).

(* The witness index and the kernel-verified distance comparisons at
   that index are deliberately NOT evaluated here: the index is a
   CRealLtT witness component produced behind the opaque archimedean
   search [QarchimedeanLowExp2_Z], so [vm_compute] cannot reduce it.
   Its certificate is carried by the TYPE [CRealLtT] (the reflected
   [QltT] threshold comparison), which is the honest interface — the
   closedness of the four witness lemmas above (Print Assumptions:
   Closed under the global context) certifies it without computation. *)

(* The defining square property spot check: the bracket end at depth 5
   squares to within the width of two. *)
Eval vm_compute in
  (Qlt_bool (Qabs (sqrt2_u 5 * sqrt2_u 5 - 2)) (1 # 8)).

(* ================= Section 8. Extraction ============ *)

Separate Extraction sqrt2_uniform_strong_irrationality sqrt2_cr sqrt2_uniform_margin sqrt2_seq sqrt2_l sqrt2_u sqrt2_sq_prop sqrt2_cr_appart_all_Q sqrt2_strong_irrational_prop.
