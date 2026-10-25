(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * A uniform upper bound for the constructive [exp] partial-sum
    series

    Mission.  A uniform upper-bound witness for the [exp] partial-sum
    series in [Q] rational arithmetic: for [0 <= B] a constant
    [C >= 1] is constructed with [exp_series n B <= C] for every [n]
    (after instantiating the Archimedean witness at [N0], the value is
    capped by a tail-sum / geometric-sum chain:
    [exp_tail_abs <= (A^m/m!) * geo_sum <= (A^m/m!) * 2], with the
    closed form [geo_sum = (1+1) * (1 - (1/2)^n) <= 2]).

    Dependencies.  [PiCompareT] (the [Set]-reflected form [QleT']);
    [PiKernelSlack] ([q_pow]/[q_fact], the [Set]-carried [And] and
    [NatLe] with the [NatLe_drop]/[NatLe_lift] bridges,
    [QleT'_to_Qle]/[Qle_to_QleT'], [qeq_leT'], [Qle_plus_nonneg_rT],
    [q_le_div_leT], [q_fact_pos], [q_pow_nonnegT], [q_fact_succ]);
    [PiExpTrigSeries] (the [exp_series] series and its monotonicity,
    [q_pow_fact_nonnegT]/[q_pow_fact2_nonnegT], [Qle_0_1_prop]); stdlib
    [QArith], [Qfield], [ZArith], [PeanoNat], [Lia], [Setoid],
    [Morphisms].

    References.  This development, [S03_QExp.v
    :30/:84/:159-:278/:292/:304/:315-:329/:403/:519/:545/:811/:941/
    :1129] (statements and proofs transcribed verbatim from the source
    passages; one closing step of [geo_sum_le_two_prop] uses [Qhalf_nonneg_prop]
    in place of [Qle_0_1_prop], the same-file [Qhalf_nonneg_prop] form,
    semantically identical; [q_neq_of_ltT] restates the stdlib
    [Qlt_not_eq], [QArith_base :963]).

    Constructivity.  Statements carried at the [Set] level ([sigT]
    witnesses, the [Set]-carried [And] product, and the reflected form
    [QleT']); assumption-free and fully proved, with no
    non-constructive principles and no external decision procedure
    closing a main statement; the proof of the main statement
    [exp_series_arch] contains a substantive derivation chain
    (Archimedean witness instantiation, induction, and the
    geometric-sum tail bound).

    Build.  [rocq c -native-compiler no -q -Q . "" PiExpArch.v]; the
    first eight bytes of the artifact are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia Setoid Morphisms.
Require Import PiCompareT.
Require Import PiKernelSlack.
Require Import PiExpTrigSeries.

(* ---- Counting bridge and bookkeeping constants ---- *)

Lemma positive_nat_Z_prop : forall p : positive, Z.of_nat (Pos.to_nat p) = Z.pos p.
Proof.
  intro p. lia.
Qed.

Lemma Q2_pos_prop : Qlt 0 (1 + 1)%Q.
Proof. unfold Qlt; simpl; lia. Qed.

Lemma Qhalf_nonneg_prop : Qle 0 (1 / 2)%Q.
Proof.
  unfold Qle.
  simpl.
  lia.
Qed.

Lemma Qle_of_nat_prop : forall a b : nat, (a <= b)%nat ->
  Qle (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b Hab.
  unfold Qle; simpl; lia.
Qed.

Lemma Qlt_of_nat_lt_prop : forall a b : nat, (a < b)%nat ->
  Qlt (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b Hab.
  unfold Qlt; simpl; lia.
Qed.

Lemma q_neq_of_lt_prop : forall x : Q, Qlt 0 x -> ~ (x == 0).
Proof.
  intros x Hx H. exact (Qlt_not_eq 0 x Hx (Qeq_sym x 0 H)).
Qed.

Lemma q_pow_succ : forall x n, q_pow x (Datatypes.S n) == x * q_pow x n.
Proof. intros. reflexivity. Qed.

(* ---- Archimedean property (Set level): some [N] with
       [2A <= (t+1)#1] for every [t >= N] ---- *)

Lemma q_arch_geom : forall A : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)).
Proof.
  intro A.
  destruct (Qarchimedean (Qmult (1 + 1)%Q A)) as [p Hp].
  exists (Pos.to_nat p).
  intros t Ht.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply (Qlt_trans _ (Z.pos p # 1) _).
  - exact Hp.
  - rewrite <- (positive_nat_Z_prop p).
    apply (Qlt_of_nat_lt_prop (Pos.to_nat p) (t + 1)).
    apply NatLe_drop in Ht. lia.
Qed.

(* ---- Geometric decay: [A^{S k}/(S k)! <= (A^k/k!) * (1/2)] when
       [2A <= (k+1)#1] ---- *)

Lemma pow_fact_geom_int_prop : forall (A : Q) (k : nat),
  Qle 0 A -> Qle (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) ->
  Qle (q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) (q_pow A k * q_fact (Datatypes.S k)).
Proof.
  intros A k HA Hle.
  setoid_rewrite (q_pow_succ A k).
  setoid_rewrite (q_fact_succ k).
  setoid_replace (Z.of_nat (Datatypes.S k) # 1) with (Z.of_nat (k + 1) # 1).
  2: { unfold Qeq. simpl. lia. }
  apply (Qle_trans _ ((Qmult (1 + 1)%Q A) * (q_pow A k * q_fact k)) _).
  - apply QleT'_to_Qle. apply qeq_leT'. ring.
  - apply (Qle_trans _ ((Z.of_nat (k + 1) # 1) * (q_pow A k * q_fact k)) _).
    + apply (Qmult_le_compat_r (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) (q_pow A k * q_fact k)).
      * exact Hle.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply q_pow_nonnegT. apply Qle_to_QleT'. exact HA.
        -- apply (Qlt_le_weak 0 (q_fact k)). apply q_fact_pos.
    + apply QleT'_to_Qle. apply qeq_leT'. ring.
Qed.

Lemma div_form_lhs : forall (A : Q) (k : nat),
  q_pow A (Datatypes.S k) * q_fact k == (q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) * (1 / 2).
Proof. intros. field. Qed.

Lemma pow_fact_geom_step_prop : forall (A : Q) (k : nat),
  Qle 0 A -> Qle (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) ->
  Qle (q_pow A (Datatypes.S k) / q_fact (Datatypes.S k)) ((q_pow A k / q_fact k) * (1 / 2)).
Proof.
  intros A k HA Hle.
  apply (Qle_trans _ ((q_pow A k * (1 / 2)) / q_fact k) _).
  - apply (q_le_div_le_prop (q_pow A (Datatypes.S k)) (q_fact (Datatypes.S k))
                       (q_pow A k * (1 / 2)) (q_fact k)).
    + apply q_fact_pos.
    + apply q_fact_pos.
    + apply (Qle_trans _ ((q_pow A k * q_fact (Datatypes.S k)) * (1 / 2)) _).
      * apply (Qle_trans _ ((q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) * (1 / 2)) _).
        -- apply QleT'_to_Qle. apply qeq_leT'. apply div_form_lhs.
        -- apply (Qmult_le_compat_r (q_pow A (Datatypes.S k) * q_fact k * (1 + 1))
                                   (q_pow A k * q_fact (Datatypes.S k)) (1 / 2)).
           ++ apply (pow_fact_geom_int_prop A k HA Hle).
           ++ apply Qlt_le_weak. unfold Qlt; simpl; lia.
      * apply QleT'_to_Qle. apply qeq_leT'. field.
  - apply QleT'_to_Qle. apply qeq_leT'.
    field.
    intro Hz. apply (q_neq_of_lt_prop (q_fact k) (q_fact_pos k)). exact Hz.
Qed.

Lemma pow_fact_geom_iter_prop : forall (A : Q) (m j : nat),
  Qle 0 A ->
  (forall t : nat, (m <= t)%nat -> Qle (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  Qle (q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j))
      ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j)).
Proof.
  intros A m j HA Hgeom.
  revert m Hgeom. induction j as [| j IH]; intros m Hgeom.
  - replace (m + 1)%nat with (Datatypes.S m) by lia.
    setoid_replace (q_pow (1 / 2) 1) with (1 / 2).
    2: { change ((1 / 2) * 1 == 1 / 2). field. }
    apply (pow_fact_geom_step_prop A m HA).
    apply Hgeom. lia.
  - setoid_replace (q_pow (1 / 2) (Datatypes.S (Datatypes.S j))) with (q_pow (1 / 2) (Datatypes.S j) * (1 / 2)).
    2: { setoid_rewrite (q_pow_succ (1 / 2) (Datatypes.S j)). ring. }
    assert (Hm : (m + Datatypes.S (Datatypes.S j))%nat = Datatypes.S (m + Datatypes.S j)) by lia.
    setoid_replace (q_pow A (m + Datatypes.S (Datatypes.S j)) / q_fact (m + Datatypes.S (Datatypes.S j)))
      with (q_pow A (Datatypes.S (m + Datatypes.S j)) / q_fact (Datatypes.S (m + Datatypes.S j))).
    2: { rewrite Hm. reflexivity. }
    apply (Qle_trans _ ((q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j)) * (1 / 2)) _).
    { apply (pow_fact_geom_step_prop A (m + Datatypes.S j) HA).
      apply (Hgeom (m + Datatypes.S j)%nat). lia. }
    { setoid_replace ((q_pow A m / q_fact m) * (q_pow (1 / 2) (Datatypes.S j) * (1 / 2)))
        with ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j) * (1 / 2)).
      2: { apply Qmult_assoc. }
      apply (Qmult_le_compat_r (q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j))
                               ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j))
                               (1 / 2)).
      - exact (IH m Hgeom).
      - apply Qlt_le_weak. unfold Qlt; simpl; lia. }
Qed.

(* ---- Geometric sum: [geo_sum n = sum of (1/2)^j for j < n] <= 2 ---- *)

Fixpoint geo_sum (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => geo_sum m + q_pow (1 / 2) m
  end.

Lemma geo_sum_closed : forall n : nat,
  geo_sum n == (1 + 1) * (1 - q_pow (1 / 2) n).
Proof.
  intro n. induction n as [| n IH]; simpl.
  - ring.
  - rewrite IH.
    change ((1 + 1) * (1 - q_pow (1 / 2) n) + q_pow (1 / 2) n ==
            (1 + 1) * (1 - (1 / 2) * q_pow (1 / 2) n)).
    field.
Qed.

Lemma geo_sum_le_two_prop : forall n : nat, Qle (geo_sum n) (1 + 1).
Proof.
  intro n. rewrite geo_sum_closed.
  apply Qle_minus_iff.
  setoid_replace ((1 + 1) - (1 + 1) * (1 - q_pow (1 / 2) n))
    with ((1 + 1) * q_pow (1 / 2) n).
  2: { ring. }
  apply Qmult_le_0_compat.
  - unfold Qle; simpl; lia.
  - apply QleT'_to_Qle. apply q_pow_nonnegT. apply Qle_to_QleT'. apply Qhalf_nonneg_prop.
Qed.

(* ---- Tail sum: [exp_tail_abs m n A = sum of A^{S j}/(S j)! for
       m <= j < n] ---- *)

Fixpoint exp_tail_abs (m : nat) (n : nat) (A : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => exp_tail_abs m n' A + (if Nat.leb m n' then q_pow A (Datatypes.S n') / q_fact (Datatypes.S n') else 0)
  end.

Lemma exp_tail_abs_le_m_prop : forall m n A, (n <= m)%nat -> exp_tail_abs m n A == 0.
Proof.
  intros m n A Hn. induction n as [| n IH]; simpl.
  - reflexivity.
  - destruct (Nat.leb m n) eqn:E.
    + exfalso. apply Nat.leb_le in E. lia.
    + assert (Hn' : (n <= m)%nat) by lia.
      rewrite (IH Hn'). ring.
Qed.

Lemma exp_tail_abs_nonneg_prop : forall (m n : nat) (A : Q), Qle 0 A -> Qle 0 (exp_tail_abs m n A).
Proof.
  intros m n A HA. induction n as [| n IH]; simpl.
  - exact (Qle_refl 0).
  - destruct (Nat.leb m n) eqn:E.
  + exact (Qle_trans 0 (exp_tail_abs m n A)
  (exp_tail_abs m n A + (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n)))
  IH (Qle_plus_nonneg_r_prop (exp_tail_abs m n A)
  (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n))
  (q_pow_fact_nonneg_prop A (Datatypes.S n) HA))).
  + exact (Qle_trans 0 (exp_tail_abs m n A) (exp_tail_abs m n A + 0) IH
  (Qle_plus_nonneg_r_prop (exp_tail_abs m n A) 0 (Qle_refl 0))).
Qed.

(* ---- Tail-sum / geometric-sum bound:
       [exp_tail_abs m n A <= (A^m/m!) * geo_sum] ---- *)

Lemma exp_tail_abs_geom_prop : forall (A : Q) (m n : nat),
  Qle 0 A ->
  (forall t : nat, (m <= t)%nat -> Qle (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  Qle (exp_tail_abs m n A) ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))).
Proof.
  intros A m n HA Hgeom Hmn.
  revert Hmn.
  induction n as [| n IH]; intros Hmn.
  - assert (Hm0 : (m = 0)%nat) by lia. subst m.
    simpl. unfold Qle; simpl; lia.
  - change (exp_tail_abs m (Datatypes.S n) A)
      with (exp_tail_abs m n A + (if Nat.leb m n then q_pow A (Datatypes.S n) / q_fact (Datatypes.S n) else 0)).
    destruct (Nat.leb m n) eqn:Emn.
    + apply Nat.leb_le in Emn.
      apply (Qle_trans _ ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))
                          + (q_pow A m / q_fact m) * q_pow (1 / 2)%Q (Datatypes.S (n - m))) _).
      * apply Qplus_le_compat.
        -- exact (IH Emn).
        -- apply (Qle_trans _ (q_pow A (m + Datatypes.S (n - m)) / q_fact (m + Datatypes.S (n - m))) _).
           ++ apply QleT'_to_Qle. apply qeq_leT'.
              assert (Hn : (Datatypes.S n = m + Datatypes.S (n - m))%nat) by lia.
              rewrite Hn. reflexivity.
           ++ exact (pow_fact_geom_iter_prop A m (n - m) HA Hgeom).
      * replace (Datatypes.S ((Datatypes.S n) - m))%nat with (Datatypes.S (Datatypes.S (n - m)))%nat by lia.
        apply QleT'_to_Qle. apply qeq_leT'.
        change (geo_sum (Datatypes.S (Datatypes.S (n - m))))
          with (geo_sum (Datatypes.S (n - m)) + q_pow (1 / 2)%Q (Datatypes.S (n - m))).
        ring.
    + apply Nat.leb_gt in Emn.
      assert (Hle : (n <= m)%nat) by lia.
      rewrite (exp_tail_abs_le_m_prop m n A Hle).
      replace (Datatypes.S ((Datatypes.S n) - m))%nat with (Datatypes.S 0)%nat by lia.
      simpl.
      apply (Qle_trans _ (q_pow A m / q_fact m) _).
      * apply QleT'_to_Qle. apply q_pow_fact_nonnegT. apply Qle_to_QleT'. exact HA.
      * apply QleT'_to_Qle. apply qeq_leT'. ring.
Qed.

(* Tail sum <= [(A^m/m!) * 2] (closing with [geo_sum <= 2]). *)
Lemma exp_tail_abs_geom2_prop : forall (A : Q) (m n : nat),
  Qle 0 A ->
  (forall t : nat, (m <= t)%nat -> Qle (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  Qle (exp_tail_abs m n A) ((q_pow A m / q_fact m) * (1 + 1)%Q).
Proof.
  intros A m n HA Hgeom Hmn.
  apply (Qle_trans _ ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))) _).
  - apply exp_tail_abs_geom_prop; assumption.
  - apply (Qle_trans _ (geo_sum (Datatypes.S (n - m)) * (q_pow A m / q_fact m)) _).
    + apply QleT'_to_Qle. apply qeq_leT'. ring.
    + apply (Qle_trans _ ((1 + 1)%Q * (q_pow A m / q_fact m)) _).
      * apply (Qmult_le_compat_r (geo_sum (Datatypes.S (n - m))) (1 + 1)%Q (q_pow A m / q_fact m)).
        -- apply geo_sum_le_two_prop.
        -- apply QleT'_to_Qle. apply q_pow_fact_nonnegT. apply Qle_to_QleT'. exact HA.
      * apply QleT'_to_Qle. apply qeq_leT'. ring.
Qed.

(* ---- Tail difference <= tail sum: [n <= k] implies
       [exp_series k B - exp_series n B <= exp_tail_abs n k B] ---- *)

Lemma exp_series_tail_le_prop : forall (B : Q) (n k : nat), Qle 0 B -> (n <= k)%nat ->
  Qle (exp_series k B - exp_series n B) (exp_tail_abs n k B).
Proof.
  intros B n k HB Hnk.
  revert n Hnk.
  induction k as [| k IH]; intros n Hnk.
  - assert (Hn0 : n = 0%nat) by lia. subst n. simpl.
    apply QleT'_to_Qle. apply qeq_leT'. reflexivity.
  - simpl.
    destruct (Nat.leb n k) eqn:E.
    + apply Nat.leb_le in E.
      setoid_replace (exp_series k B + q_pow B (Datatypes.S k) / q_fact (Datatypes.S k) - exp_series n B)
        with (exp_series k B - exp_series n B + q_pow B (Datatypes.S k) / q_fact (Datatypes.S k)) by ring.
      apply (Qplus_le_compat (exp_series k B - exp_series n B) (exp_tail_abs n k B)
                             (q_pow B (Datatypes.S k) / q_fact (Datatypes.S k))
                             (q_pow B (Datatypes.S k) / q_fact (Datatypes.S k))).
      { apply IH. lia. }
      { apply Qle_refl. }
    + apply Nat.leb_gt in E.
      apply (Qle_trans _ 0 _).
      * apply Qle_minus_iff.
        setoid_replace (0 + - (exp_series (Datatypes.S k) B - exp_series n B))
          with (exp_series n B - exp_series (Datatypes.S k) B) by ring.
        setoid_replace (exp_series n B - exp_series (Datatypes.S k) B)
          with (exp_series n B + - exp_series (Datatypes.S k) B) by ring.
        apply (proj1 (Qle_minus_iff (exp_series (Datatypes.S k) B) (exp_series n B))).
        apply exp_series_mono_prop; [exact HB | lia].
      * setoid_replace (exp_tail_abs n k B + 0) with (exp_tail_abs n k B) by ring.
        apply exp_tail_abs_nonneg_prop. exact HB.
Qed.

(* ---- Main statement: [0 <= B] implies some [C >= 1] with
       [exp_series n B <= C] for every [n] ---- *)

Lemma exp_series_arch : forall (B : Q), QleT' 0 B ->
  sigT (fun C : Q => And (QleT' 1 C) (forall n : nat, QleT' (exp_series n B) C)).
Proof.
  intros B HB.
  destruct (q_arch_geom B) as [N0 HN0].
  set (C := exp_series N0 B + (q_pow B N0 / q_fact N0) * (1 + 1)%Q).
  exists C.
  split.
  - apply Qle_to_QleT'.
    unfold C.
    apply (Qle_trans _ (exp_series N0 B) _).
    + setoid_replace 1 with (exp_series 0 B).
      2: reflexivity.
      apply exp_series_mono_prop; [exact (QleT'_to_Qle _ _ HB) | lia].
    + apply (Qle_plus_nonneg_r_prop (exp_series N0 B) ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)).
      apply QleT'_to_Qle. apply q_pow_fact2_nonnegT. exact (HB).
  - intro n.
    apply Qle_to_QleT'.
    destruct (Nat.leb n N0) eqn:En.
    + apply Nat.leb_le in En.
      apply (Qle_trans _ (exp_series N0 B) _).
      * apply exp_series_mono_prop; [exact (QleT'_to_Qle _ _ HB) | exact En].
      * unfold C. apply (Qle_plus_nonneg_r_prop (exp_series N0 B) ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)).
        apply QleT'_to_Qle. apply q_pow_fact2_nonnegT. exact (HB).
    + apply Nat.leb_gt in En.
      apply (Qle_trans _ (exp_series N0 B + (q_pow B N0 / q_fact N0) * (1 + 1)%Q) _).
      * apply (Qle_trans _ (exp_series N0 B + exp_tail_abs N0 n B) _).
        -- apply Qle_minus_iff.
           setoid_replace (exp_series N0 B + exp_tail_abs N0 n B + - exp_series n B)
             with (exp_tail_abs N0 n B - (exp_series n B - exp_series N0 B)) by ring.
           setoid_replace (exp_tail_abs N0 n B - (exp_series n B - exp_series N0 B))
             with (exp_tail_abs N0 n B + - (exp_series n B - exp_series N0 B)) by ring.
           apply (proj1 (Qle_minus_iff (exp_series n B - exp_series N0 B) (exp_tail_abs N0 n B))).
            apply (exp_series_tail_le_prop B N0 n (QleT'_to_Qle _ _ HB)). lia.
        -- apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply (exp_tail_abs_geom2_prop B N0 n (QleT'_to_Qle _ _ HB))].
           { intros u Hu. apply QleT'_to_Qle. apply (HN0 u). apply NatLe_lift. lia. }
           { lia. }
      * unfold C. apply Qle_refl.
Qed.

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


(* Set twin of Q2_pos_prop *)
Lemma Q2_posT : QltT 0 (1 + 1)%Q.
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply Q2_pos_prop.
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

(* Set twin of Qhalf_nonneg_prop *)
Lemma Qhalf_nonnegT : QleT' 0 (1 / 2)%Q.
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply Qhalf_nonneg_prop.
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

(* Set twin of Qle_of_nat_prop *)
Lemma Qle_of_natT : forall a b : nat, NatLe (a) (b) -> QleT' (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (Qle_of_nat_prop a b).
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

(* Set twin of Qlt_of_nat_lt_prop *)
Lemma Qlt_of_nat_ltT : forall a b : nat, NatLe (Datatypes.S (a)) (b) -> QltT (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (Qlt_of_nat_lt_prop a b).
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

(* Set twin of q_pow_succ *)
Lemma q_pow_succT : forall x n, QeqT (q_pow x (Datatypes.S n)) (x * q_pow x n).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (q_pow_succ x n).
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

(* Set twin of pow_fact_geom_int_prop *)
Lemma pow_fact_geom_intT : forall (A : Q) (k : nat), QleT' 0 A -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) -> QleT' (q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) (q_pow A k * q_fact (Datatypes.S k)).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (pow_fact_geom_int_prop A k).
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

(* Set twin of div_form_lhs *)
Lemma div_form_lhsT : forall (A : Q) (k : nat), QeqT (q_pow A (Datatypes.S k) * q_fact k) ((q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) * (1 / 2)).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (div_form_lhs A k).
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

(* Set twin of pow_fact_geom_step_prop *)
Lemma pow_fact_geom_stepT : forall (A : Q) (k : nat), QleT' 0 A -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) -> QleT' (q_pow A (Datatypes.S k) / q_fact (Datatypes.S k)) ((q_pow A k / q_fact k) * (1 / 2)).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (pow_fact_geom_step_prop A k).
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

(* Set twin of pow_fact_geom_iter_prop *)
Lemma pow_fact_geom_iterT : forall (A : Q) (m j : nat), QleT' 0 A -> (forall t : nat, NatLe (m) (t) -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) -> QleT' (q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j)) ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j)).
Proof.
  intros.
  exact (Qle_to_QleT' _ _ (pow_fact_geom_iter_prop A m j (QleT'_to_Qle _ _ H) (fun t Ht => QleT'_to_Qle _ _ (H0 t (NatLe_lift _ _ Ht))))).
Qed.

(* Set twin of geo_sum_closed *)
Lemma geo_sum_closedT : forall n : nat, QeqT (geo_sum n) ((1 + 1) * (1 - q_pow (1 / 2) n)).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (geo_sum_closed n).
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

(* Set twin of geo_sum_le_two_prop *)
Lemma geo_sum_le_twoT : forall n : nat, QleT' (geo_sum n) (1 + 1).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (geo_sum_le_two_prop n).
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

(* Set twin of exp_tail_abs_le_m_prop *)
Lemma exp_tail_abs_le_mT : forall m n A, NatLe (n) (m) -> QeqT (exp_tail_abs m n A) (0).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (exp_tail_abs_le_m_prop m n A).
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

(* Set twin of exp_tail_abs_nonneg_prop *)
Lemma exp_tail_abs_nonnegT : forall (m n : nat) (A : Q), QleT' 0 A -> QleT' 0 (exp_tail_abs m n A).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (exp_tail_abs_nonneg_prop m n A).
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

(* Set twin of exp_tail_abs_geom_prop *)
Lemma exp_tail_abs_geomT : forall (A : Q) (m n : nat), QleT' 0 A -> (forall t : nat, NatLe (m) (t) -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) -> NatLe (m) (n) -> QleT' (exp_tail_abs m n A) ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))).
Proof.
  intros.
  exact (Qle_to_QleT' _ _ (exp_tail_abs_geom_prop A m n (QleT'_to_Qle _ _ H) (fun t Ht => QleT'_to_Qle _ _ (H0 t (NatLe_lift _ _ Ht))) (NatLe_drop _ _ H1))).
Qed.

(* Set twin of exp_tail_abs_geom2_prop *)
Lemma exp_tail_abs_geom2T : forall (A : Q) (m n : nat), QleT' 0 A -> (forall t : nat, NatLe (m) (t) -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) -> NatLe (m) (n) -> QleT' (exp_tail_abs m n A) ((q_pow A m / q_fact m) * (1 + 1)%Q).
Proof.
  intros.
  exact (Qle_to_QleT' _ _ (exp_tail_abs_geom2_prop A m n (QleT'_to_Qle _ _ H) (fun t Ht => QleT'_to_Qle _ _ (H0 t (NatLe_lift _ _ Ht))) (NatLe_drop _ _ H1))).
Qed.

(* Set twin of exp_series_tail_le_prop *)
Lemma exp_series_tail_leT : forall (B : Q) (n k : nat), QleT' 0 B -> NatLe (n) (k) -> QleT' (exp_series k B - exp_series n B) (exp_tail_abs n k B).
Proof.
  intros.
  first [ apply Qlt_to_QltT | apply Qle_to_QleT' | apply qeq_imp_qeqT | apply NatLe_lift | idtac ].
  eapply (exp_series_tail_le_prop B n k).
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
