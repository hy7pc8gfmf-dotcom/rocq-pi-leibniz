(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)

(** * PiLeibnizMargin: unboundedness of the Leibniz-series margin
      [leiblw_margin n = (2n+1)! * leiblw_gap n = 8 * (2n)! / (2n+3)].

    Mission.  This file formalizes the window-boundary margin theory of
      the alternating Leibniz series [leiblw_S n] (the partial sums of
      [4*(-1)^k/(2k+1)]) as a self-contained rational-arithmetic
      development.  The margin [leiblw_margin n] is the distance gap
      [leiblw_gap n] between same-side consecutive partial sums, scaled
      by the common denominator [leiblw_qf (2*n+1) = (2n+1)!] witnessing
      integrality of the scaled partial sums.  The main theorem
      [leiblw_margin_unbounded] proves that the margin exceeds every
      natural-number bound [B] at some index, carried on [Set]:
      [forall B : nat, sigT (fun n : nat => leiblw_Id (leiblw_Qltb
      (Z.of_nat B # 1) (leiblw_margin n)) true)].  Companion results:
      the two-sided alternating remainder bounds, the explicit gap,
      the integrality witness, the distance lower bound, the
      escape-window obstacle for nearby limits, the unbounded natural
      certificate window, and the separation of the unbounded Leibniz
      window from the bounded Niven-type factorial window.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [ZArith.ZArith], [Lia], [micromega.Lqa]; this development,
      [PiCompareT] (the canonical [Set]-valued decision types
      [QltT]/[QleT'] and the identity type [Id], consumed by the
      canonical twin block at the end of this file).

    References.  This development, module [LW0LeibWindow.v] (the
      statements and proofs of its comparator, series, remainder-bound,
      gap, integrality, distance, margin and family-separation sections
      are carried over unchanged; its standalone extraction statement
      and its certificate-machine section are not part of this module).

    Constructivity.  Assumption-free and fully proved; the flagship
      statements are carried on [Set] via [sigT] with the identity type
      [leiblw_Id] and the boolean comparators [leiblw_Qltb] and
      [leiblw_Qleb] (stdlib [QArith] ships no [Qlt_bool]);
      [Prop] occurs only as [Q]-order scaffolding inside proofs, and
      the decidable order trichotomy [Qcompare_spec] drives the
      comparator proofs; [lia]/[nia]/[lra] close only small
      rational-arithmetic bookkeeping goals, the margin identities
      reducing to explicit integer formulas after the denominator
      normalizations [leiblw_pos_succ1_prop] and [leiblw_zpos_mul_prop].

    Build.  [coqc -q -native-compiler no -Q theories pi_leibniz
      -Q theories/Reals/Cauchy "" theories/Reals/Cauchy/PiLeibnizMargin.v]
      (Rocq 9.1.0).
*)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import micromega.Lqa.
Require Import PiCompareT.

(* QArith.QArith opens Q_scope by default; this file works with
   nat_scope as the default scope, so every [Q] literal carries %Q. *)
Local Open Scope nat_scope.

(* ==== Section 0. Rational-order comparators and integer bridges ==== *)

(* Set-valued strict-order boolean on [Q] (stdlib [QArith] has no
   [Qlt_bool]; self-carried on the [Q] comparison). *)
Definition leiblw_Qltb (x y : Q) : bool :=
  match (x ?= y)%Q with Lt => true | _ => false end.

Lemma leiblw_Qltb_true_prop : forall x y : Q, Qlt x y -> leiblw_Qltb x y = true.
Proof.
  intros x y H. unfold leiblw_Qltb.
  destruct (Qcompare_spec x y) as [Heq|Hlt'|Hgt].
  - exfalso. unfold Qeq, Qlt in *. cbn [Qnum Qden] in *. nia.
  - reflexivity.
  - exfalso. unfold Qgt, Qlt in *. cbn [Qnum Qden] in *. nia.
Qed.


(* Positivity bridge for [Z.of_nat] (premise [1 <= n], since
   [Z.of_nat 0 = 0] is not positive). *)
Lemma leiblw_znat_pos_prop : forall n : nat, (1 <= n)%nat -> (0 < Z.of_nat n)%Z.
Proof.
  intros n Hn. destruct n as [|k]; [lia|].
  cbn [Z.of_nat]. apply Pos2Z.is_pos.
Qed.

(* [Z.pos (Pos.of_succ_nat k) = k+1]: normalizes every [Q] denominator
   into the integer fragment solvable by [lia]/[nia]. *)
Lemma leiblw_pos_succ_prop : forall k : nat, Z.pos (Pos.of_succ_nat k) = Z.of_nat (S k).
Proof.
  induction k as [|k IH]; [reflexivity|].
  simpl Pos.of_succ_nat. rewrite Pos2Z.inj_succ. rewrite IH. lia.
Qed.

(* Linearization tactic: pos_succ, then the injectivity lemmas. *)
Ltac leiblw_zlin :=
  rewrite ?leiblw_pos_succ_prop, ?Nat2Z.inj_succ, ?Nat2Z.inj_add,
          ?Nat2Z.inj_mul, ?Pos2Z.inj_mul, ?Nat2Z.inj_sub in *.

(* Direct +1 form of pos_succ, bypassing the extra inj_succ step. *)
Lemma leiblw_pos_succ1_prop : forall k : nat, Z.pos (Pos.of_succ_nat k) = (Z.of_nat k + 1)%Z.
Proof. intros k. rewrite leiblw_pos_succ_prop. lia. Qed.

Lemma leiblw_qmake_eq_prop : forall (a b : Z) (p q : positive),
  (a # p)%Q == (b # q)%Q <-> (a * Z.pos q = b * Z.pos p)%Z.
Proof.
  intros a b p q. unfold Qeq. cbn [Qnum Qden]. tauto.
Qed.

Lemma leiblw_qmake_lt_prop : forall (a b : Z) (p q : positive),
  Qlt (a # p)%Q (b # q)%Q <-> (a * Z.pos q < b * Z.pos p)%Z.
Proof.
  intros a b p q. unfold Qlt. cbn [Qnum Qden]. split.
  - intro H. apply Z.compare_lt_iff in H. exact H.
  - intro H. apply Z.compare_lt_iff. exact H.
Qed.

Lemma leiblw_qmake_le_prop : forall (a b : Z) (p q : positive),
  Qle (a # p)%Q (b # q)%Q <-> (a * Z.pos q <= b * Z.pos p)%Z.
Proof.
  intros a b p q. unfold Qle. cbn [Qnum Qden]. split.
  - intro H. apply Z.compare_le_iff in H. exact H.
  - intro H. apply Z.compare_le_iff. exact H.
Qed.

Lemma leiblw_qabs_id_prop : forall q : Q, Qle 0%Q q -> Qabs q == q.
Proof.
  intros [z p] H. unfold Qle in H. cbn [Qnum Qden] in H.
  cbn [Qabs]. unfold Qeq. cbn [Qnum Qden]. destruct z as [|z'|z'].
  - reflexivity.
  - reflexivity.
  - exfalso. pose proof (Pos2Z.is_pos z') as Hp. simpl in H. lia.
Qed.

Lemma leiblw_qabs_neg_prop : forall q : Q, Qle q 0%Q -> Qabs q == (- q)%Q.
Proof.
  intros [z p] H. unfold Qle in H. cbn [Qnum Qden] in H.
  cbn [Qabs Qopp]. unfold Qeq. cbn [Qnum Qden]. destruct z as [|z'|z'].
  - reflexivity.
  - exfalso. pose proof (Pos2Z.is_pos z') as Hp. simpl in H. lia.
  - reflexivity.
Qed.

(* Set-valued identity type, carried on [Set]. *)
Inductive leiblw_Id {A : Type} (a : A) : A -> Set := leiblw_id_intro : leiblw_Id a a.

Lemma leiblw_id_eq_prop : forall b : bool, b = true -> leiblw_Id b true.
Proof. intros b H. rewrite H. apply leiblw_id_intro. Qed.

Lemma leiblw_id_inv_prop : forall b : bool, leiblw_Id b true -> b = true.
Proof. intros b H. destruct H. reflexivity. Qed.

(* Parity decomposition of a natural number, as a [Set]-level sum. *)
Fixpoint leiblw_even (n : nat) : bool :=
  match n with
  | 0 => true
  | S k => negb (leiblw_even k)
  end.

Lemma leiblw_even_2m_prop : forall m : nat, leiblw_even (2 * m) = true.
Proof.
  induction m as [|m IH]; [reflexivity|].
  replace (2 * S m) with (S (S (2 * m))) by lia.
  cbn [leiblw_even]. rewrite IH. reflexivity.
Qed.

Lemma leiblw_even_2m1_prop : forall m : nat, leiblw_even (2 * m + 1) = false.
Proof.
  intros m. replace (2 * m + 1) with (S (2 * m)) by lia.
  cbn [leiblw_even]. rewrite leiblw_even_2m_prop. reflexivity.
Qed.

Lemma leiblw_par_decomp_prop : forall k : nat,
  sum (sigT (fun j : nat => k = 2 * j)) (sigT (fun j : nat => k = 2 * j + 1)).
Proof.
  induction k as [|k IH].
  - left. exists 0. reflexivity.
  - destruct IH as [[j Hj]|[j Hj]].
    + right. exists j. rewrite Hj. lia.
    + left. exists (S j). rewrite Hj. lia.
Qed.

(* ==== Section 1. The series terms and partial sums ==== *)

(* Term [t_k = 4*(-1)^k/(2k+1)] and partial sum [S_n = sum_{k<n} t_k]. *)
Definition leiblw_t (k : nat) : Q :=
  if leiblw_even k
  then (4 # Pos.of_succ_nat (2 * k))%Q
  else ((-4) # Pos.of_succ_nat (2 * k))%Q.

Fixpoint leiblw_S (n : nat) : Q :=
  match n with
  | 0 => 0%Q
  | S m => leiblw_S m + leiblw_t m
  end.

Lemma leiblw_S_SS : forall n : nat,
  leiblw_S (S (S n)) == leiblw_S n + leiblw_t n + leiblw_t (S n).
Proof. intros n. unfold Qeq. cbn [leiblw_S]. lia. Qed.

Lemma leiblw_S_step : forall n : nat, leiblw_S (S n) == leiblw_S n + leiblw_t n.
Proof. intros n. reflexivity. Qed.

Lemma leiblw_t_pos_case_prop : forall k : nat,
  leiblw_even k = true -> leiblw_t k == (4 # Pos.of_succ_nat (2 * k))%Q.
Proof. intros k H. unfold leiblw_t. rewrite H. reflexivity. Qed.

Lemma leiblw_t_neg_case_prop : forall k : nat,
  leiblw_even k = false -> leiblw_t k == ((-4) # Pos.of_succ_nat (2 * k))%Q.
Proof. intros k H. unfold leiblw_t. rewrite H. reflexivity. Qed.

Lemma leiblw_t_even : forall m : nat,
  leiblw_t (2 * m) == (4 # Pos.of_succ_nat (4 * m))%Q.
Proof.
  intros m. rewrite (leiblw_t_pos_case_prop (2 * m) (leiblw_even_2m_prop m)).
  replace (2 * (2 * m)) with (4 * m) by lia. reflexivity.
Qed.

Lemma leiblw_t_odd : forall m : nat,
  leiblw_t (2 * m + 1) == ((-4) # Pos.of_succ_nat (4 * m + 2))%Q.
Proof.
  intros m. rewrite (leiblw_t_neg_case_prop (2 * m + 1) (leiblw_even_2m1_prop m)).
  replace (2 * (2 * m + 1)) with (4 * m + 2) by lia. reflexivity.
Qed.

Lemma leiblw_t_even_pos_prop : forall m : nat, Qlt 0%Q (leiblw_t (2 * m))%Q.
Proof.
  intros m. rewrite leiblw_t_even. apply leiblw_qmake_lt_prop.
  leiblw_zlin.
  assert (0 <= Z.of_nat (4 * m))%Z by apply Nat2Z.is_nonneg. lia.
Qed.

Lemma leiblw_t_odd_neg_prop : forall m : nat, Qlt (leiblw_t (2 * m + 1))%Q 0%Q.
Proof.
  intros m. rewrite leiblw_t_odd. apply leiblw_qmake_lt_prop.
  leiblw_zlin. lia.
Qed.

(* ==== Section 1b. Rational fraction algebra ==== *)

(* Normalized addition: (a#p)+(b#q) == ((a*q'+b*p')#(p*q)). *)
Lemma leiblw_qplus_norm : forall (a b : Z) (p q : positive),
  ((a # p) + (b # q))%Q == ((a * Z.pos q + b * Z.pos p) # (Pos.mul p q))%Q.
Proof.
  intros a b p q. unfold Qeq. cbn [Qnum Qden Qplus Qmult Pos.mul].
  rewrite Pos2Z.inj_mul. ring.
Qed.

Lemma leiblw_qplus_lt0_prop : forall (a b : Z) (p q : positive),
  (0 < a * Z.pos q + b * Z.pos p)%Z -> Qlt 0%Q (((a # p) + (b # q))%Q).
Proof.
  intros a b p q H. rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_lt_prop. rewrite Z.mul_0_l, Z.mul_1_r. exact H.
Qed.

Lemma leiblw_qplus_lt0b_prop : forall (a b : Z) (p q : positive),
  (a * Z.pos q + b * Z.pos p < 0)%Z -> Qlt ((a # p) + (b # q))%Q 0%Q.
Proof.
  intros a b p q H.
  rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_lt_prop. rewrite Z.mul_1_r, Z.mul_0_l. exact H.
Qed.

Lemma leiblw_qplus_le0_prop : forall (a b : Z) (p q : positive),
  (a * Z.pos q + b * Z.pos p <= 0)%Z -> Qle (((a # p) + (b # q))%Q) 0%Q.
Proof.
  intros a b p q H. rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_le_prop. rewrite Z.mul_1_r, Z.mul_0_l. exact H.
Qed.

Lemma leiblw_qplus_eq_prop : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  ((a * Z.pos q + b * Z.pos p) * Z.pos r = c * Z.pos (Pos.mul p q))%Z ->
  ((a # p) + (b # q))%Q == (c # r)%Q.
Proof.
  intros a b p q c r H. rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_eq_prop. exact H.
Qed.

Lemma leiblw_qopp_distr : forall x y : Q, (-(x + y))%Q == ((- x) + (- y))%Q.
Proof.
  intros x y. unfold Qeq. cbn [Qnum Qden Qplus Qopp]. ring.
Qed.

(* Signed normalized form: -((a#p)+(b#q)) == (c#r). *)
Lemma leiblw_qneg_plus_eq_prop : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  (((- a) * Z.pos q + (- b) * Z.pos p) * Z.pos r = c * Z.pos (Pos.mul p q))%Z ->
  (-((a # p) + (b # q)))%Q == (c # r)%Q.
Proof.
  intros a b p q c r H.
  rewrite leiblw_qopp_distr. unfold Qopp.
  apply leiblw_qplus_eq_prop. exact H.
Qed.

(* Shunt identity: ((A+U)+V)-A == U+V. *)
Lemma leiblw_qshunt : forall A U V : Q, (((A + U) + V) - A)%Q == (U + V)%Q.
Proof.
  intros A U V. unfold Qminus.
  rewrite <- (Qplus_assoc (A + U)%Q V (- A)%Q).
  rewrite <- (Qplus_assoc A U (V + (- A))%Q).
  rewrite (Qplus_assoc U V (- A)%Q).
  rewrite (Qplus_assoc A (U + V)%Q (- A)%Q).
  rewrite (Qplus_comm A (U + V)%Q).
  rewrite <- (Qplus_assoc (U + V)%Q A (- A)%Q).
  rewrite Qplus_opp_r. apply Qplus_0_r.
Qed.

Lemma leiblw_qplus_opp_l0 : forall A X : Q, (A + (-(A + X)))%Q == (- X)%Q.
Proof. intros A X. lra. Qed.

(* Reverse shunt: A-((A+U)+V) == -(U+V). *)
Lemma leiblw_qshunt_neg : forall A U V : Q, (A - ((A + U) + V))%Q == (-(U + V))%Q.
Proof.
  intros A U V.
  rewrite <- (Qplus_assoc A U V).
  unfold Qminus. apply leiblw_qplus_opp_l0.
Qed.

Lemma leiblw_qopp_lt_prop : forall x : Q, Qlt 0%Q x -> Qlt (- x)%Q 0%Q.
Proof.
  intros x H. unfold Qlt in *. cbn [Qnum Qden Qopp] in *. lia.
Qed.

Lemma leiblw_qminus_flip : forall x y : Q, (y - x)%Q == (-(x - y))%Q.
Proof. intros x y. lra. Qed.

Lemma leiblw_qle_add_r_prop : forall A U : Q, Qle U 0%Q -> Qle (A + U)%Q A.
Proof. intros A U H. lra. Qed.

Lemma leiblw_qle_add2_r_prop : forall A U V : Q, Qle (U + V)%Q 0%Q -> Qle ((A + U) + V)%Q A.
Proof.
  intros A U V H.
  assert (H2 : Qle (((A + U) + V) - A)%Q 0%Q) by (rewrite leiblw_qshunt; exact H).
  lra.
Qed.

Lemma leiblw_qle_add_l_prop : forall A W : Q, Qle 0%Q W -> Qle A (A + W)%Q.
Proof. intros A W H. lra. Qed.

Lemma leiblw_qplus_le0b_prop : forall (a b : Z) (p q : positive),
  (0 <= a * Z.pos q + b * Z.pos p)%Z -> Qle 0%Q ((a # p) + (b # q))%Q.
Proof.
  intros a b p q H. rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_le_prop. rewrite Z.mul_0_l, Z.mul_1_r. exact H.
Qed.

Lemma leiblw_zpos_mul_prop : forall j k : nat,
  Z.pos (Pos.mul (Pos.of_succ_nat j) (Pos.of_succ_nat k)) =
  (Z.of_nat (S j) * Z.of_nat (S k))%Z.
Proof.
  intros j k. rewrite Pos2Z.inj_mul. rewrite !leiblw_pos_succ_prop. reflexivity.
Qed.

(* ==== Section 2. Two-sided alternating remainder bounds ==== *)

(* Even steps move up: S_{2m+2} - S_{2m} > 0. *)
Lemma leiblw_step_even_pos_prop : forall m : nat,
  Qlt 0%Q (leiblw_S (2 * m + 2) - leiblw_S (2 * m))%Q.
Proof.
  intros m.
  replace (2 * m + 2) with (S (S (2 * m))) by lia.
  cbn [leiblw_S]. rewrite leiblw_qshunt.
  rewrite leiblw_t_even. replace (2 * (2 * m)) with (4 * m) by lia.
  replace (S (2 * m)) with (2 * m + 1) by lia.
  rewrite leiblw_t_odd.
  apply leiblw_qplus_lt0_prop.
  rewrite (leiblw_pos_succ1_prop (4 * m)), (leiblw_pos_succ1_prop (4 * m + 2)).
  assert (H1 : (Z.of_nat (4 * m) + 2 = Z.of_nat (4 * m + 2))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  lia.
Qed.

(* Odd steps move down: S_{2m+3} - S_{2m+1} < 0. *)
Lemma leiblw_step_odd_neg_prop : forall m : nat,
  Qlt (leiblw_S (2 * m + 3) - leiblw_S (2 * m + 1))%Q 0%Q.
Proof.
  intros m.
  replace (2 * m + 3) with (S (S (2 * m + 1))) by lia.
  cbn [leiblw_S]. rewrite leiblw_qshunt.
  rewrite leiblw_t_odd.
  replace (S (2 * m + 1)) with (2 * m + 2) by lia.
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  rewrite leiblw_t_even.
  replace (4 * (m + 1)) with (4 * m + 4) by lia.
  apply leiblw_qplus_lt0b_prop.
  rewrite (leiblw_pos_succ1_prop (4 * m + 4)), (leiblw_pos_succ1_prop (4 * m + 2)).
  assert (H1 : (Z.of_nat (4 * m + 2) + 2 = Z.of_nat (4 * m + 4))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  lia.
Qed.

(* Interlacing: S_{2m+2} <= S_{2m+1}. *)
Lemma leiblw_interlace_prop : forall m : nat,
  Qle (leiblw_S (2 * m + 2)) (leiblw_S (2 * m + 1))%Q.
Proof.
  intros m.
  replace (2 * m + 2) with (S (2 * m + 1)) by lia.
  cbn [leiblw_S].
  apply leiblw_qle_add_r_prop.
  rewrite leiblw_t_odd.
  apply leiblw_qmake_le_prop.
  rewrite (leiblw_pos_succ1_prop (4 * m + 2)). lia.
Qed.

(* Even subsequence is non-decreasing. *)
Lemma leiblw_mono_even_prop : forall j m : nat, (m <= j)%nat ->
  Qle (leiblw_S (2 * m)) (leiblw_S (2 * j))%Q.
Proof.
  induction j as [|j IH]; intros m Hm.
  - assert (m = 0) by lia. subst. apply Qle_refl.
  - destruct (Nat.eq_dec m (S j)) as [He|Hne].
    + subst. apply Qle_refl.
    + assert (Hmj : (m <= j)%nat) by lia.
      apply (Qle_trans _ (leiblw_S (2 * j))).
      * apply IH. exact Hmj.
      * replace (2 * S j) with (S (S (2 * j))) by lia.
        cbn [leiblw_S].
        rewrite <- (Qplus_assoc (leiblw_S (2 * j)) (leiblw_t (2 * j)) (leiblw_t (S (2 * j)))).
        apply leiblw_qle_add_l_prop.
        rewrite leiblw_t_even.
        replace (2 * (2 * j)) with (4 * j) by lia.
        replace (S (2 * j)) with (2 * j + 1) by lia.
        rewrite leiblw_t_odd.
        apply leiblw_qplus_le0b_prop.
        rewrite (leiblw_pos_succ1_prop (4 * j + 2)), (leiblw_pos_succ1_prop (4 * j)).
        assert (H1 : (Z.of_nat (4 * j) + 2 = Z.of_nat (4 * j + 2))%Z).
        { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
        lia.
Qed.

(* Odd subsequence is non-increasing. *)
Lemma leiblw_mono_odd_prop : forall j m : nat, (m <= j)%nat ->
  Qle (leiblw_S (2 * j + 1)) (leiblw_S (2 * m + 1))%Q.
Proof.
  induction j as [|j IH]; intros m Hm.
  - assert (m = 0) by lia. subst. apply Qle_refl.
  - destruct (Nat.eq_dec m (S j)) as [He|Hne].
    + subst. apply Qle_refl.
    + assert (Hmj : (m <= j)%nat) by lia.
      apply (Qle_trans _ (leiblw_S (2 * j + 1))).
      * replace (2 * S j + 1) with (S (S (2 * j + 1))) by lia.
        cbn [leiblw_S].
        apply leiblw_qle_add2_r_prop.
        replace (S (2 * j + 1)) with (2 * j + 2) by lia.
        replace (2 * j + 2) with (2 * (j + 1)) by lia.
        rewrite leiblw_t_odd.
        rewrite leiblw_t_even.
        replace (4 * (j + 1)) with (4 * j + 4) by lia.
        apply leiblw_qplus_le0_prop.
        rewrite (leiblw_pos_succ1_prop (4 * j + 4)), (leiblw_pos_succ1_prop (4 * j + 2)).
        assert (H1 : (Z.of_nat (4 * j + 2) + 2 = Z.of_nat (4 * j + 4))%Z).
        { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
        lia.
      * apply IH. exact Hmj.
Qed.

(* ==== Section 3. The explicit gap ==== *)

(* gap n = 8/((2n+1)(2n+3)): the same-side consecutive-partial-sum step. *)
Definition leiblw_gap (n : nat) : Q :=
  (8 # (Pos.mul (Pos.of_succ_nat (2 * n)) (Pos.of_succ_nat (2 * n + 2))))%Q.

Lemma leiblw_gap_pos_prop : forall n : nat, Qlt 0%Q (leiblw_gap n).
Proof. intros n. unfold leiblw_gap. apply leiblw_qmake_lt_prop. apply Pos2Z.is_pos. Qed.

Lemma leiblw_gap_even_step : forall m : nat,
  (leiblw_S (2 * m + 2) - leiblw_S (2 * m))%Q == leiblw_gap (2 * m).
Proof.
  intros m. unfold leiblw_gap.
  replace (2 * m + 2) with (S (S (2 * m))) by lia.
  cbn [leiblw_S]. rewrite leiblw_qshunt.
  rewrite leiblw_t_even. replace (2 * (2 * m)) with (4 * m) by lia.
  replace (S (2 * m)) with (2 * m + 1) by lia.
  rewrite leiblw_t_odd.
  apply leiblw_qplus_eq_prop.
  rewrite (leiblw_pos_succ1_prop (4 * m)), (leiblw_pos_succ1_prop (4 * m + 2)).
  assert (Hw : (Z.pos (Pos.mul (Pos.of_succ_nat (4 * m)) (Pos.of_succ_nat (4 * m + 2))) =
                Z.of_nat (4 * m + 1) * Z.of_nat (4 * m + 3))%Z)
    by (rewrite leiblw_zpos_mul_prop; f_equal; lia).
  rewrite Hw.
  assert (H1 : (Z.of_nat (4 * m) + 2 = Z.of_nat (4 * m + 2))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H2 : (Z.of_nat (4 * m) + 1 = Z.of_nat (4 * m + 1))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H3 : (Z.of_nat (4 * m + 2) + 1 = Z.of_nat (4 * m + 3))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  nia.
Qed.

Lemma leiblw_gap_odd_step : forall m : nat,
  (leiblw_S (2 * m + 1) - leiblw_S (2 * m + 3))%Q == leiblw_gap (2 * m + 1).
Proof.
  intros m. unfold leiblw_gap.
  replace (2 * m + 3) with (S (S (2 * m + 1))) by lia.
  cbn [leiblw_S]. rewrite leiblw_qshunt_neg.
  rewrite leiblw_t_odd.
  replace (S (2 * m + 1)) with (2 * m + 2) by lia.
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  rewrite leiblw_t_even.
  replace (4 * (m + 1)) with (4 * m + 4) by lia.
  replace (2 * (2 * m + 1)) with (4 * m + 2) by lia.
  replace (2 * (2 * m + 1) + 2) with (4 * m + 4) by lia.
  apply leiblw_qneg_plus_eq_prop.
  rewrite (leiblw_pos_succ1_prop (4 * m + 4)), (leiblw_pos_succ1_prop (4 * m + 2)).
  assert (Hw : (Z.pos (Pos.mul (Pos.of_succ_nat (4 * m + 2)) (Pos.of_succ_nat (4 * m + 4))) =
                Z.of_nat (4 * m + 3) * Z.of_nat (4 * m + 5))%Z)
    by (rewrite leiblw_zpos_mul_prop; f_equal; lia).
  rewrite Hw.
  assert (H1 : (Z.of_nat (4 * m + 2) + 2 = Z.of_nat (4 * m + 4))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H2 : (Z.of_nat (4 * m + 2) + 1 = Z.of_nat (4 * m + 3))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H3 : (Z.of_nat (4 * m + 4) + 1 = Z.of_nat (4 * m + 5))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  nia.
Qed.

(* ==== Section 4. Common denominator integrality ==== *)

(* [zf n = n!] as a straightforward integer factorial; [qf n = n! # 1]. *)
Fixpoint leiblw_zf (n : nat) : Z :=
  match n with
  | 0 => 1%Z
  | S k => Z.pos (Pos.of_succ_nat k) * leiblw_zf k
  end.

Definition leiblw_qf (n : nat) : Q := (leiblw_zf n # 1)%Q.

Lemma leiblw_zf_ge1_prop : forall n : nat, (1 <= leiblw_zf n)%Z.
Proof. induction n as [|n IH]; cbn [leiblw_zf]; lia. Qed.

Lemma leiblw_zf_ge_id_prop : forall n : nat, (1 <= n)%nat -> (Z.of_nat n <= leiblw_zf n)%Z.
Proof.
  intros n Hn. replace n with (S (n - 1)) by lia.
  cbn [leiblw_zf]. rewrite leiblw_pos_succ_prop.
  assert (Hn0 : (0 < Z.of_nat (S (n - 1)))%Z) by (apply leiblw_znat_pos_prop; lia).
  pose proof (leiblw_zf_ge1_prop (n - 1)) as H1. nia.
Qed.

(* zf(2n) >= (2n-1)*(2n) for n >= 1: the fuel of the margin divergence. *)
Lemma leiblw_zf_lower_prop : forall n : nat, (1 <= n)%nat ->
  (Z.of_nat (2 * n - 1) * Z.of_nat (2 * n) <= leiblw_zf (2 * n))%Z.
Proof.
  intros n Hn.
  replace (leiblw_zf (2 * n)) with (leiblw_zf (S (2 * n - 1))) by (f_equal; lia).
  cbn [leiblw_zf]. rewrite leiblw_pos_succ_prop, Nat2Z.inj_succ.
  assert (H2 : (Z.of_nat (2 * n - 1) <= leiblw_zf (2 * n - 1))%Z)
    by (apply leiblw_zf_ge_id_prop; lia).
  assert (H3 : (0 <= Z.of_nat (2 * n - 1))%Z) by apply Nat2Z.is_nonneg.
  nia.
Qed.

(* One-step native unfolding of zf at the index [2n+1]. *)
Lemma leiblw_zf_2n1_prop : forall n : nat,
  leiblw_zf (2 * n + 1) = (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))%Z.
Proof.
  intros n. replace (2 * n + 1) with (S (2 * n)) by lia.
  cbn [leiblw_zf]. reflexivity.
Qed.

(* Three-factor native unfolding: zf(2n+3) = (2n+3)*(2n+2)*((2n+1)*zf(2n)). *)
Lemma leiblw_zf_2n3_prop : forall n : nat,
  leiblw_zf (2 * n + 3) =
  (Z.pos (Pos.of_succ_nat (S (S (2 * n)))) *
   (Z.pos (Pos.of_succ_nat (S (2 * n))) *
    (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))))%Z.
Proof.
  intros n. replace (2 * n + 3) with (S (S (S (2 * n)))) by lia.
  cbn [leiblw_zf]. reflexivity.
Qed.

(** Integrality witness: for every [n] there is an integer [p] with
    [(2n+1)! * S_n == p], proved by induction splitting on the parity of
    [n] and normalizing the three-factor factorial unfolding. *)
Theorem leiblw_integrality : forall n : nat,
  sigT (fun p : Z => (leiblw_qf (2 * n + 1) * leiblw_S n)%Q == (p # 1)%Q).
Proof.
  induction n as [|n IH].
  - exists 0%Z. unfold leiblw_qf. cbn [leiblw_zf leiblw_S].
    unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - destruct IH as [p Hp].
    replace (2 * S n + 1) with (2 * n + 3) by lia.
    unfold leiblw_qf in Hp. rewrite leiblw_zf_2n1_prop in Hp.
    destruct (leiblw_even n) eqn:Hev.
    + exists (Z.pos (Pos.of_succ_nat (S (S (2 * n)))) *
              (Z.pos (Pos.of_succ_nat (S (2 * n))) *
               (p + 4 * leiblw_zf (2 * n)))%Z)%Z.
      cbn [leiblw_S]. rewrite leiblw_t_pos_case_prop by exact Hev.
      unfold leiblw_qf at 1. rewrite leiblw_zf_2n3_prop.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (S (S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) Hp) as Hp2.
      rewrite Z.mul_1_r in Hp2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) +
                     (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite Hp2. ring.
    + exists (Z.pos (Pos.of_succ_nat (S (S (2 * n)))) *
              (Z.pos (Pos.of_succ_nat (S (2 * n))) *
               (p - 4 * leiblw_zf (2 * n)))%Z)%Z.
      cbn [leiblw_S]. rewrite leiblw_t_neg_case_prop by exact Hev.
      unfold leiblw_qf at 1. rewrite leiblw_zf_2n3_prop.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (S (S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) Hp) as Hp2.
      rewrite Z.mul_1_r in Hp2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) -
                     (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite Hp2. ring.
Qed.

(* ==== Section 5. Distance lower bound ==== *)

(* Even side, even tail: j >= m+1 implies S_{2j} - S_{2m} >= gap(2m). *)
Lemma leiblw_lower_even_e_prop : forall j m : nat, (m + 1 <= j)%nat ->
  Qle (leiblw_gap (2 * m)) (leiblw_S (2 * j) - leiblw_S (2 * m))%Q.
Proof.
  intros j m Hj. rewrite <- (leiblw_gap_even_step m).
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  assert (Hme : Qle (leiblw_S (2 * (m + 1))) (leiblw_S (2 * j)))
    by (apply leiblw_mono_even_prop; lia).
  lra.
Qed.

(* Even side, odd tail: j >= m implies S_{2j+1} - S_{2m} >= gap(2m). *)
Lemma leiblw_lower_even_o_prop : forall j m : nat, (m <= j)%nat ->
  Qle (leiblw_gap (2 * m)) (leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q.
Proof.
  intros j m Hj. rewrite <- (leiblw_gap_even_step m).
  assert (Hme : Qle (leiblw_S (2 * m + 2)) (leiblw_S (2 * j + 2))).
  { replace (2 * m + 2) with (2 * (m + 1)) by lia.
    replace (2 * j + 2) with (2 * (j + 1)) by lia.
    apply leiblw_mono_even_prop. lia. }
  assert (Hi : Qle (leiblw_S (2 * j + 2)) (leiblw_S (2 * j + 1)))
    by apply leiblw_interlace_prop.
  lra.
Qed.

(* Odd side, even tail: j >= m+1 implies S_{2m+1} - S_{2j} >= gap(2m+1). *)
Lemma leiblw_lower_odd_e_prop : forall j m : nat, (m + 1 <= j)%nat ->
  Qle (leiblw_gap (2 * m + 1)) ((leiblw_S (2 * m + 1) - leiblw_S (2 * j))%Q).
Proof.
  intros j m Hj.
  pose proof (leiblw_gap_odd_step m) as Hstep.
  pose proof (leiblw_S_step (2 * j)) as Hst.
  assert (Hsyn : (2 * j + 1 = S (2 * j))%nat) by lia.
  rewrite <- Hsyn in Hst.
  pose proof (leiblw_t_even_pos_prop j) as Hp.
  pose proof (leiblw_mono_odd_prop j (m + 1) Hj) as Hmo.
  replace (2 * (m + 1) + 1) with (2 * m + 3) in Hmo by lia.
  lra.
Qed.

(* Odd side, odd tail: j >= m+1 implies S_{2m+1} - S_{2j+1} >= gap(2m+1). *)
Lemma leiblw_lower_odd_o_prop : forall j m : nat, (m + 1 <= j)%nat ->
  Qle (leiblw_gap (2 * m + 1)) (leiblw_S (2 * m + 1) - leiblw_S (2 * j + 1))%Q.
Proof.
  intros j m Hj. rewrite <- (leiblw_gap_odd_step m).
  replace (2 * m + 3) with (2 * (m + 1) + 1) by lia.
  assert (Hle : Qle (leiblw_S (2 * j + 1)) (leiblw_S (2 * (m + 1) + 1)))
    by (apply leiblw_mono_odd_prop; lia).
  lra.
Qed.

(** Main distance theorem: k >= n+1 implies gap n <= |S_k - S_n|; the
    four parity cases select the matching one-sided bound and rewrite
    the absolute value with the sign-appropriate [Qabs] identity. *)
Theorem leiblw_dist_prop : forall n k : nat, (S n <= k)%nat ->
  Qle (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n))%Q.
Proof.
  intros n k Hk.
  destruct (leiblw_par_decomp_prop n) as [[m Hm]|Hm].
  - destruct (leiblw_par_decomp_prop k) as [[j Hj]|Hj].
    + assert (Hc : (m + 1 <= j)%nat) by lia.
      pose proof (leiblw_lower_even_e_prop j m Hc) as L.
      assert (Hy : Qle 0%Q ((leiblw_S (2 * j) - leiblw_S (2 * m))%Q)).
      { pose proof (leiblw_gap_pos_prop (2 * m)). lra. }
      pose proof (leiblw_qabs_id_prop _ Hy) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m))
                       (Qabs ((leiblw_S (2 * j) - leiblw_S (2 * m))%Q))) by lra.
      exact (eq_ind (2 * m)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j)
                 (fun v => Qle (leiblw_gap (2 * m))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
    + destruct Hj as [j Hj].
      assert (Hc : (m <= j)%nat) by lia.
      pose proof (leiblw_lower_even_o_prop j m Hc) as L.
      assert (Hy : Qle 0%Q ((leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q)).
      { pose proof (leiblw_gap_pos_prop (2 * m)). lra. }
      pose proof (leiblw_qabs_id_prop _ Hy) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m))
                       (Qabs ((leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q))) by lra.
      exact (eq_ind (2 * m)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j + 1)
                 (fun v => Qle (leiblw_gap (2 * m))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
  - destruct Hm as [m Hm].
    destruct (leiblw_par_decomp_prop k) as [[j Hj]|Hj].
    + assert (Hc : (m + 1 <= j)%nat) by lia.
      pose proof (leiblw_lower_odd_e_prop j m Hc) as L0.
      assert (Hy2 : Qle ((leiblw_S (2 * j) - leiblw_S (2 * m + 1))%Q) 0%Q).
      { pose proof (leiblw_gap_pos_prop (2 * m + 1)). lra. }
      pose proof (leiblw_qabs_neg_prop _ Hy2) as E1.
      pose proof (leiblw_qminus_flip (leiblw_S (2 * m + 1)) (leiblw_S (2 * j))) as Hz.
      assert (L2 : Qle (leiblw_gap (2 * m + 1))
                       (Qabs ((leiblw_S (2 * j) - leiblw_S (2 * m + 1))%Q))) by lra.
      exact (eq_ind (2 * m + 1)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j)
                 (fun v => Qle (leiblw_gap (2 * m + 1))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m + 1))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
    + destruct Hj as [j Hj].
      assert (Hc : (m + 1 <= j)%nat) by lia.
      pose proof (leiblw_lower_odd_o_prop j m Hc) as L0.
      assert (Hy : Qle ((leiblw_S (2 * j + 1) - leiblw_S (2 * m + 1))%Q) 0%Q).
      { pose proof (leiblw_gap_pos_prop (2 * m + 1)). lra. }
      pose proof (leiblw_qabs_neg_prop _ Hy) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m + 1))
                       (Qabs ((leiblw_S (2 * j + 1) - leiblw_S (2 * m + 1))%Q))) by lra.
      exact (eq_ind (2 * m + 1)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j + 1)
                 (fun v => Qle (leiblw_gap (2 * m + 1))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m + 1))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
Qed.

(* Set-valued non-strict-order boolean on [Q] (stdlib [QArith] has no
   [Qlt_bool]; [QArith_base] only ships [Qeq_bool] and [Qle_bool]). *)
Definition leiblw_Qleb (x y : Q) : bool :=
  match (x ?= y)%Q with Gt => false | _ => true end.

Lemma leiblw_Qleb_true_prop : forall x y : Q, Qle x y -> leiblw_Qleb x y = true.
Proof.
  intros x y H. unfold leiblw_Qleb.
  destruct (Qcompare_spec x y) as [Heq|Hlt'|Hgt].
  - reflexivity.
  - reflexivity.
  - exfalso. unfold Qgt, Qle in *. cbn [Qnum Qden] in *. nia.
Qed.


(** Set-level encapsulation of the distance bound.  The strict form
    gap n < |S_k - S_n| fails at k = n+2 where equality holds, so the
    non-strict order of [leiblw_dist_prop] is the honest face; the boolean
    wrapper [leiblw_Qleb] keeps the statement on [Set]. *)
Theorem leiblw_dist_set_prop : forall n : nat,
  sigT (fun N : nat => forall k : nat, (N <= k)%nat ->
    leiblw_Id (leiblw_Qleb (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n))) true).
Proof.
  intros n. exists (S n). intros k Hk.
  apply leiblw_id_eq_prop. apply leiblw_Qleb_true_prop.
  apply leiblw_dist_prop. exact Hk.
Qed.

(* ==== Section 6. The margin and its unboundedness ==== *)

(* margin n = (2n+1)! * gap n = 8*(2n)!/(2n+3): the residual lower bound
   in the integrality witness position. *)
Definition leiblw_margin (n : nat) : Q := (leiblw_qf (2 * n + 1) * leiblw_gap n)%Q.

(* Natural certificate window: W b n = 4b*(2n)! = b * (2n+1)! * |t_n|. *)
Definition leiblw_natwin (b n : nat) : Q :=
  (4 * Z.of_nat b * leiblw_zf (2 * n) # 1)%Q.

Lemma leiblw_qabs_make : forall q : Q,
  Qabs q == ((Z.abs (Qnum q)) # (Qden q))%Q.
Proof. intros [z p]. reflexivity. Qed.

(** Residual identity: W b n == b * (2n+1)! * |t_n|, by the even/odd
    case split on the term and the one-step factorial unfolding. *)
Lemma leiblw_natwin_residual : forall b n : nat,
  (leiblw_natwin b n)%Q
  == ((Z.of_nat b # 1) * (leiblw_qf (2 * n + 1) * Qabs (leiblw_t n)))%Q.
Proof.
  intros b n. unfold leiblw_natwin, leiblw_qf.
  destruct (leiblw_even n) eqn:Hev.
  - rewrite leiblw_t_pos_case_prop by exact Hev.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp Pos.mul Qabs Z.abs].
    rewrite leiblw_zf_2n1_prop. ring.
  - rewrite leiblw_t_neg_case_prop by exact Hev.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp Pos.mul Qabs Z.abs].
    rewrite leiblw_zf_2n1_prop. ring.
Qed.

Lemma leiblw_natwin_ge_prop : forall b n : nat,
  (1 <= b)%nat -> Qle (4 # 1)%Q (leiblw_natwin b n).
Proof.
  intros b n Hb. unfold leiblw_natwin. apply leiblw_qmake_le_prop.
  pose proof (leiblw_znat_pos_prop b Hb) as Hp.
  pose proof (leiblw_zf_ge1_prop (2 * n)) as Hf.
  nia.
Qed.

Lemma leiblw_natwin_mono_prop : forall b n : nat,
  Qle (leiblw_natwin b n) (leiblw_natwin b (S n)).
Proof.
  intros b n. unfold leiblw_natwin. apply leiblw_qmake_le_prop.
  rewrite !Z.mul_1_r.
  replace (2 * S n) with (S (S (2 * n))) by lia.
  cbn [leiblw_zf].
  rewrite (leiblw_pos_succ_prop (S (2 * n))), (leiblw_pos_succ_prop (2 * n)).
  pose proof (Nat2Z.is_nonneg (S (S (2 * n)))) as Ha.
  pose proof (Nat2Z.is_nonneg (S (2 * n))) as Hc.
  pose proof (leiblw_zf_ge1_prop (2 * n)) as Hf.
  pose proof (Nat2Z.is_nonneg b) as Hd.
  nia.
Qed.

(* Range of the partial sums: 0 <= S_n <= 4, with S_1 = 4 the maximum. *)
Lemma leiblw_S1_4 : leiblw_S 1 == (4 # 1)%Q.
Proof. cbn [leiblw_S leiblw_t leiblw_even]. reflexivity. Qed.

Lemma leiblw_S_le4_prop : forall n : nat, Qle (leiblw_S n) (4 # 1)%Q.
Proof.
  intros n. destruct (leiblw_par_decomp_prop n) as [[j Hj]|[j Hj]].
  - rewrite Hj. destruct j as [|j'].
    + cbn [leiblw_S]. apply leiblw_qmake_le_prop. lia.
    + replace (2 * S j') with (S (2 * j' + 1)) by lia.
      cbn [leiblw_S].
      assert (Ht : Qle (leiblw_t (2 * j' + 1)) 0%Q).
      { rewrite leiblw_t_odd. apply leiblw_qmake_le_prop.
        rewrite (leiblw_pos_succ1_prop (4 * j' + 2)). lia. }
      pose proof (leiblw_mono_odd_prop j' 0 (Nat.le_0_l j')) as Hm.
      replace (2 * 0 + 1) with 1 in Hm by lia.
      pose proof (leiblw_S1_4) as Hs1.
      lra.
  - pose proof (leiblw_mono_odd_prop j 0 (Nat.le_0_l j)) as Hm.
    replace (2 * 0 + 1) with 1 in Hm by lia.
    rewrite Hj.
    pose proof (leiblw_S1_4) as Hs1.
    lra.
Qed.

Lemma leiblw_S_ge0_prop : forall n : nat, Qle 0%Q (leiblw_S n).
Proof.
  intros n. destruct (leiblw_par_decomp_prop n) as [[j Hj]|[j Hj]].
  - rewrite Hj. pose proof (leiblw_mono_even_prop j 0 (Nat.le_0_l j)) as Hm.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    lra.
  - rewrite Hj. pose proof (leiblw_interlace_prop j) as Hi.
    pose proof (leiblw_mono_even_prop (j + 1) 0 (Nat.le_0_l (j + 1))) as Hm.
    replace (2 * (j + 1)) with (2 * j + 2) in Hm by lia.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    lra.
Qed.

(* |x| <= c from the two one-sided bounds (case analysis on the sign
   of the numerator; no classical decision). *)
Lemma leiblw_qabs_bound_prop : forall x c : Q,
  Qle x c -> Qle (- x)%Q c -> Qle (Qabs x) c.
Proof.
  intros [z p] c H1 H2. cbn [Qabs]. cbn [Qopp] in H2.
  destruct z as [|z'|z']; [exact H1 | exact H1 | exact H2].
Qed.

(** Escape-window obstacle: a rational [q] inside the m-th envelope
    [S_{2m+2} <= q <= S_{2m+1}] satisfies |q - S_n| <= 4 < 8 <= W b n
    for every n once b >= 2, so the natural window never lets such a
    [q] escape; the negative statement lives on [Prop] (negations have
    no [Set] form), while the [Set] delivery faces are
    [leiblw_dist_set_prop], [leiblw_natwin_unbounded_prop] and
    [leiblw_margin_unbounded]. *)
Theorem leiblw_escape_obstacle_prop : forall (b m : nat) (q : Q), (2 <= b)%nat ->
  Qle (leiblw_S (2 * m + 2)) q -> Qle q (leiblw_S (2 * m + 1)) ->
  forall n : nat, Qle (Qabs ((q - leiblw_S n)%Q)) (leiblw_natwin b n).
Proof.
  intros b m q Hb Hlo Hhi n.
  assert (Hb1 : (1 <= b)%nat) by lia.
  pose proof (leiblw_natwin_ge_prop b n Hb1) as Hw.
  assert (Hq4 : Qle q (4 # 1)%Q).
  { pose proof (leiblw_mono_odd_prop m 0 (Nat.le_0_l m)) as Hm.
    replace (2 * 0 + 1) with 1 in Hm by lia.
    pose proof (leiblw_S1_4) as Hs1.
    lra. }
  assert (Hq0 : Qle 0%Q q).
  { pose proof (leiblw_interlace_prop m) as Hi.
    pose proof (leiblw_mono_even_prop (m + 1) 0 (Nat.le_0_l (m + 1))) as Hm.
    replace (2 * (m + 1)) with (2 * m + 2) in Hm by lia.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    lra. }
  assert (Hs4 : Qle (leiblw_S n) (4 # 1)%Q) by apply leiblw_S_le4_prop.
  assert (Hs0 : Qle 0%Q (leiblw_S n)) by apply leiblw_S_ge0_prop.
  apply (Qle_trans _ (4 # 1)%Q).
  - apply leiblw_qabs_bound_prop.
    + lra.
    + rewrite <- (leiblw_qminus_flip q (leiblw_S n)). lra.
  - exact Hw.
Qed.

(** Unboundedness of the natural window on [Set]: the index
    n = S(B+B) satisfies zf(2n) >= 2n >= B+1 > B and 4b >= 4, so
    W b n exceeds every bound B. *)
Theorem leiblw_natwin_unbounded_prop : forall b B : nat, (1 <= b)%nat ->
  sigT (fun n : nat =>
    leiblw_Id (leiblw_Qltb ((Z.of_nat B # 1)%Q) (leiblw_natwin b n)) true).
Proof.
  intros b B Hb. exists (S (B + B)).
  apply leiblw_id_eq_prop. apply leiblw_Qltb_true_prop.
  unfold leiblw_natwin. apply leiblw_qmake_lt_prop.
  assert (H1 : (1 <= 2 * S (B + B))%nat) by lia.
  pose proof (leiblw_zf_ge_id_prop (2 * S (B + B)) H1) as Hf.
  pose proof (leiblw_znat_pos_prop b Hb) as Hp.
  pose proof (Nat2Z.is_nonneg B) as Hnn.
  nia.
Qed.

(** Main theorem, unboundedness of the margin on [Set]: at the index
    n = B+2 the factor (2n+1)! = (2B+5)! dominates the denominator
    (2n+1)(2n+3) of gap n, giving margin n >= n+1 > B; after the
    denominator normalizations the claim is a small integer inequality. *)
Theorem leiblw_margin_unbounded : forall B : nat,
  sigT (fun n : nat =>
    leiblw_Id (leiblw_Qltb ((Z.of_nat B # 1)%Q) (leiblw_margin n)) true).
Proof.
  intros B. exists (B + 2).
  apply leiblw_id_eq_prop. apply leiblw_Qltb_true_prop.
  unfold leiblw_margin, leiblw_qf, leiblw_gap.
  apply leiblw_qmake_lt_prop.
  cbn [Qnum Qden Pos.mul].
  rewrite (leiblw_zpos_mul_prop (2 * (B + 2)) (2 * (B + 2) + 2)).
  rewrite leiblw_zf_2n1_prop.
  assert (Hidx : (2 * (B + 2) = 2 * B + 4)%nat) by lia.
  rewrite Hidx.
  rewrite (leiblw_pos_succ1_prop (2 * B + 4)).
  assert (Hidx2 : (2 * B + 4 = S (2 * B + 3))%nat) by lia.
  rewrite Hidx2. cbn [leiblw_zf].
  rewrite (leiblw_pos_succ1_prop (2 * B + 3)).
  assert (H1 : (1 <= 2 * B + 3)%nat) by lia.
  pose proof (leiblw_zf_ge_id_prop (2 * B + 3) H1) as Hf3.
  pose proof (Nat2Z.is_nonneg (2 * B + 3)) as Hnn.
  nia.
Qed.

(* Interface shapes of the irrationality criterion of
   [UpReqIrrationalCriterion.v], restated on [Set] with [sigT] nesting
   and [leiblw_Id]; the boolean predicates are realized by the
   self-carried [leiblw_Qltb] of Section 0. *)

Definition leiblw_lic_tail_bounded (x e : nat -> Q) : Set :=
  forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
    leiblw_Id (leiblw_Qltb (Qabs ((x k - x n)%Q)) (e n)) true.

Definition leiblw_lic_escape_window (x e : nat -> Q) : Set :=
  forall q : Q,
    sigT (fun n : nat =>
      sigT (fun _ : (1 <= n)%nat =>
        leiblw_Id (leiblw_Qltb (e n) (Qabs ((q - x n)%Q))) true)).

Definition leiblw_lic_vanish (e : nat -> Q) : Set :=
  forall eps : Q, leiblw_Id (leiblw_Qltb 0%Q eps) true ->
    sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
      leiblw_Id (leiblw_Qltb (e n) eps) true).

(* ==== Section 7. Family separation ==== *)

(* Niven-type factorial window: w_niv n = 1/(2n+1), a certificate
   residual window that stays bounded. *)
Definition leiblw_nivwin (n : nat) : Q := (1 # Pos.of_succ_nat (n + n + 1))%Q.

(* The factorial window never exceeds 1: it separates from the
   unbounded natural window of Section 6. *)
Theorem leiblw_nivwin_bounded_prop : forall n : nat, Qle (leiblw_nivwin n) 1%Q.
Proof.
  intros n. unfold leiblw_nivwin. apply leiblw_qmake_le_prop.
  pose proof (Pos2Z.is_pos (Pos.of_succ_nat (n + n + 1))). nia.
Qed.

(** Separation statement on [Set]: the Leibniz natural window exceeds 1
    already at n = 1 (4*(2*1)! = 8 > 1), while the factorial window of
    [leiblw_nivwin_bounded_prop] never does, so the "window <= 1" test is
    reachable for the Niven family and unreachable for the Leibniz
    family. *)
Theorem leiblw_family_separation :
  sigT (fun n : nat => leiblw_Id (leiblw_Qltb 1%Q (leiblw_natwin 1 n)) true).
Proof.
  exists 1. apply leiblw_id_eq_prop. apply leiblw_Qltb_true_prop.
  unfold leiblw_natwin. apply leiblw_qmake_lt_prop.
  replace (2 * 1) with 2 by lia.
  cbn [leiblw_zf Z.of_nat Pos.of_succ_nat]. lia.
Qed.

(* ==== Section 8. Numerical spot checks and assumption audit ==== *)

(* Margin table spot check: margin n = 8*(2n)!/(2n+3), first four values. *)
Lemma leiblw_margin_tbl :
  (leiblw_margin 0 == (8 # 3)%Q) /\
  (leiblw_margin 1 == (16 # 5)%Q) /\
  (leiblw_margin 2 == (192 # 7)%Q) /\
  (leiblw_margin 3 == (640 # 1)%Q).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(* Natural window table spot check: W 1 n = 4*(2n)!, first four values. *)
Lemma leiblw_natwin_tbl :
  (leiblw_natwin 1 0 == (4 # 1)%Q) /\
  (leiblw_natwin 1 1 == (8 # 1)%Q) /\
  (leiblw_natwin 1 2 == (96 # 1)%Q) /\
  (leiblw_natwin 1 3 == (2880 # 1)%Q).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(* Assumption audit: every flagship statement is closed under the
   global context. *)
Print Assumptions leiblw_dist_prop.
Print Assumptions leiblw_integrality.
Print Assumptions leiblw_dist_set_prop.
Print Assumptions leiblw_natwin_residual.
Print Assumptions leiblw_natwin_unbounded_prop.
Print Assumptions leiblw_margin_unbounded.
Print Assumptions leiblw_escape_obstacle_prop.
Print Assumptions leiblw_nivwin_bounded_prop.
Print Assumptions leiblw_family_separation.
Print Assumptions leiblw_margin_tbl.
Print Assumptions leiblw_natwin_tbl.

(* ==== Section 9. Canonical Set-carried twins ==== *)

(* The canonical [Set]-valued decision types [QltT]/[QleT'] and the
   identity type [Id] are shared from [PiCompareT].  The bridge family
   below couples the canonical faces with the [Prop]-level order and
   the self-carried comparators of Section 0; each twin afterwards is
   the Set-carried twin of the same-named statement earlier in this
   file, derived from its original through these bridges.  In every
   twin, each [Q]-order premise or conclusion is carried by
   [QltT]/[QleT'], each Boolean or [Z] equality by [Id], and each [Q]
   equality by [Qeq_bool] under [Id].  The original statements are
   untouched. *)

Lemma leiblw_canon_id_eq : forall b : bool, b = true -> Id b true.
Proof. intros b H. rewrite H. apply id_refl. Qed.

Lemma leiblw_canon_id_inv : forall b : bool, Id b true -> b = true.
Proof. intros b H. destruct H. reflexivity. Qed.

Lemma QltT_to_Qlt : forall x y : Q, QltT x y -> Qlt x y.
Proof.
  intros x y H.
  unfold QltT in H.
  unfold Qlt_bool in H.
  destruct (Qcompare x y) eqn:E; try (inversion H).
  apply Qlt_alt. exact E.
Qed.

Lemma Qlt_to_QltT : forall x y : Q, Qlt x y -> QltT x y.
Proof.
  intros x y H.
  unfold QltT, Qlt_bool.
  destruct (Qcompare x y) eqn:E.
  - exfalso.
    apply (Qlt_irrefl y).
    assert (Heq : x == y) by (apply Qeq_alt; exact E).
    rewrite Heq in H.
    exact H.
  - reflexivity.
  - exfalso.
    apply (Qlt_irrefl x).
    assert (Hyx : (y < x)%Q) by (apply Qgt_alt; exact E).
    eapply Qlt_trans.
    exact H.
    exact Hyx.
Qed.

Lemma QleT'_to_Qle : forall x y : Q, QleT' x y -> Qle x y.
Proof.
  intros x y H.
  apply (proj1 (Qle_bool_iff x y)).
  apply leiblw_canon_id_inv. exact H.
Qed.

Lemma Qle_to_QleT' : forall x y : Q, Qle x y -> QleT' x y.
Proof.
  intros x y H.
  apply leiblw_canon_id_eq. apply (proj2 (Qle_bool_iff x y)). exact H.
Qed.

(* Set twin of leiblw_pos_succ_prop. *)
Lemma leiblw_pos_succ_T : forall k : nat,
  @Id Z (Z.pos (Pos.of_succ_nat k)) (Z.of_nat (S k)).
Proof. intros k. exact (@id_refl Z (Z.pos (Pos.of_succ_nat k))). Qed.

(* Set twin of leiblw_pos_succ1_prop. *)
Lemma leiblw_pos_succ1_T : forall k : nat,
  @Id Z (Z.pos (Pos.of_succ_nat k)) (Z.of_nat k + 1)%Z.
Proof. intros k. rewrite leiblw_pos_succ_prop, Nat2Z.inj_succ. apply id_refl. Qed.

(* Set twin of leiblw_zpos_mul_prop. *)
Lemma leiblw_zpos_mul_T : forall j k : nat,
  @Id Z (Z.pos (Pos.mul (Pos.of_succ_nat j) (Pos.of_succ_nat k)))
        (Z.of_nat (S j) * Z.of_nat (S k))%Z.
Proof. intros j k. rewrite leiblw_zpos_mul_prop. apply id_refl. Qed.

(* Set twin of leiblw_zf_2n1_prop. *)
Lemma leiblw_zf_2n1_T : forall n : nat,
  @Id Z (leiblw_zf (2 * n + 1))
        (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))%Z.
Proof. intros n. rewrite leiblw_zf_2n1_prop. apply id_refl. Qed.

(* Set twin of leiblw_zf_2n3_prop. *)
Lemma leiblw_zf_2n3_T : forall n : nat,
  @Id Z (leiblw_zf (2 * n + 3))
        (Z.pos (Pos.of_succ_nat (S (S (2 * n)))) *
         (Z.pos (Pos.of_succ_nat (S (2 * n))) *
          (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))))%Z.
Proof. intros n. rewrite leiblw_zf_2n3_prop. apply id_refl. Qed.

(* Set twin of leiblw_even_2m_prop. *)
Lemma leiblw_even_2m_T : forall m : nat, Id (leiblw_even (2 * m)) true.
Proof. intros m. apply leiblw_canon_id_eq. apply leiblw_even_2m_prop. Qed.

(* Set twin of leiblw_even_2m1_prop. *)
Lemma leiblw_even_2m1_T : forall m : nat, Id (leiblw_even (2 * m + 1)) false.
Proof. intros m. rewrite leiblw_even_2m1_prop. apply id_refl. Qed.

(* Set twin of leiblw_par_decomp_prop. *)
Lemma leiblw_par_decomp_T : forall k : nat,
  sum (sigT (fun j : nat => @Id nat k (2 * j)))
      (sigT (fun j : nat => @Id nat k (2 * j + 1))).
Proof.
  intros k. destruct (leiblw_par_decomp_prop k) as [[j Hj]|[j Hj]].
  - left. exists j. rewrite <- Hj. apply id_refl.
  - right. exists j. rewrite <- Hj. apply id_refl.
Qed.

(* Set twin of leiblw_t_pos_case_prop. *)
Lemma leiblw_t_pos_case_T : forall k : nat,
  Id (leiblw_even k) true ->
  Id (Qeq_bool (leiblw_t k) (4 # Pos.of_succ_nat (2 * k))%Q) true.
Proof.
  intros k H. apply leiblw_canon_id_eq.
  apply (proj2 (Qeq_bool_iff (leiblw_t k) (4 # Pos.of_succ_nat (2 * k))%Q)).
  apply leiblw_t_pos_case_prop. apply leiblw_canon_id_inv. exact H.
Qed.

(* Set twin of leiblw_t_neg_case_prop. *)
Lemma leiblw_t_neg_case_T : forall k : nat,
  Id (leiblw_even k) false ->
  Id (Qeq_bool (leiblw_t k) ((-4) # Pos.of_succ_nat (2 * k))%Q) true.
Proof.
  intros k H. apply leiblw_canon_id_eq.
  apply (proj2 (Qeq_bool_iff (leiblw_t k) ((-4) # Pos.of_succ_nat (2 * k))%Q)).
  apply leiblw_t_neg_case_prop. destruct H. reflexivity.
Qed.

(* Set twin of leiblw_t_even_pos_prop. *)
Lemma leiblw_t_even_pos_T : forall m : nat, QltT 0%Q (leiblw_t (2 * m))%Q.
Proof. intros m. apply Qlt_to_QltT. apply leiblw_t_even_pos_prop. Qed.

(* Set twin of leiblw_t_odd_neg_prop. *)
Lemma leiblw_t_odd_neg_T : forall m : nat, QltT (leiblw_t (2 * m + 1))%Q 0%Q.
Proof. intros m. apply Qlt_to_QltT. apply leiblw_t_odd_neg_prop. Qed.

(* Set twin of leiblw_qabs_id_prop. *)
Lemma leiblw_qabs_id_T : forall q : Q,
  QleT' 0%Q q -> Id (Qeq_bool (Qabs q) q) true.
Proof.
  intros q H. apply leiblw_canon_id_eq.
  apply (proj2 (Qeq_bool_iff (Qabs q) q)).
  apply leiblw_qabs_id_prop. apply QleT'_to_Qle. exact H.
Qed.

(* Set twin of leiblw_qabs_neg_prop. *)
Lemma leiblw_qabs_neg_T : forall q : Q,
  QleT' q 0%Q -> Id (Qeq_bool (Qabs q) (- q)%Q) true.
Proof.
  intros q H. apply leiblw_canon_id_eq.
  apply (proj2 (Qeq_bool_iff (Qabs q) (- q)%Q)).
  apply leiblw_qabs_neg_prop. apply QleT'_to_Qle. exact H.
Qed.

(* Set twin of leiblw_qopp_lt_prop. *)
Lemma leiblw_qopp_lt_T : forall x : Q, QltT 0%Q x -> QltT (- x)%Q 0%Q.
Proof.
  intros x H. apply Qlt_to_QltT. apply leiblw_qopp_lt_prop.
  apply QltT_to_Qlt. exact H.
Qed.

(* Set twin of leiblw_qle_add_r_prop. *)
Lemma leiblw_qle_add_r_T : forall A U : Q, QleT' U 0%Q -> QleT' (A + U)%Q A.
Proof.
  intros A U H. apply Qle_to_QleT'. apply leiblw_qle_add_r_prop.
  apply QleT'_to_Qle. exact H.
Qed.

(* Set twin of leiblw_qle_add2_r_prop. *)
Lemma leiblw_qle_add2_r_T : forall A U V : Q,
  QleT' (U + V)%Q 0%Q -> QleT' ((A + U) + V)%Q A.
Proof.
  intros A U V H. apply Qle_to_QleT'. apply leiblw_qle_add2_r_prop.
  apply QleT'_to_Qle. exact H.
Qed.

(* Set twin of leiblw_qle_add_l_prop. *)
Lemma leiblw_qle_add_l_T : forall A W : Q, QleT' 0%Q W -> QleT' A (A + W)%Q.
Proof.
  intros A W H. apply Qle_to_QleT'. apply leiblw_qle_add_l_prop.
  apply QleT'_to_Qle. exact H.
Qed.

(* Set twin of leiblw_step_even_pos_prop. *)
Lemma leiblw_step_even_pos_T : forall m : nat,
  QltT 0%Q (leiblw_S (2 * m + 2) - leiblw_S (2 * m))%Q.
Proof. intros m. apply Qlt_to_QltT. apply leiblw_step_even_pos_prop. Qed.

(* Set twin of leiblw_step_odd_neg_prop. *)
Lemma leiblw_step_odd_neg_T : forall m : nat,
  QltT (leiblw_S (2 * m + 3) - leiblw_S (2 * m + 1))%Q 0%Q.
Proof. intros m. apply Qlt_to_QltT. apply leiblw_step_odd_neg_prop. Qed.

(* Set twin of leiblw_interlace_prop. *)
Lemma leiblw_interlace_T : forall m : nat,
  QleT' (leiblw_S (2 * m + 2)) (leiblw_S (2 * m + 1))%Q.
Proof. intros m. apply Qle_to_QleT'. apply leiblw_interlace_prop. Qed.

(* Set twin of leiblw_gap_pos_prop. *)
Lemma leiblw_gap_pos_T : forall n : nat, QltT 0%Q (leiblw_gap n).
Proof. intros n. apply Qlt_to_QltT. apply leiblw_gap_pos_prop. Qed.

(* Set twin of leiblw_natwin_mono_prop. *)
Lemma leiblw_natwin_mono_T : forall b n : nat,
  QleT' (leiblw_natwin b n) (leiblw_natwin b (S n)).
Proof. intros b n. apply Qle_to_QleT'. apply leiblw_natwin_mono_prop. Qed.

(* Set twin of leiblw_S_le4_prop. *)
Lemma leiblw_S_le4_T : forall n : nat, QleT' (leiblw_S n) (4 # 1)%Q.
Proof. intros n. apply Qle_to_QleT'. apply leiblw_S_le4_prop. Qed.

(* Set twin of leiblw_S_ge0_prop. *)
Lemma leiblw_S_ge0_T : forall n : nat, QleT' 0%Q (leiblw_S n).
Proof. intros n. apply Qle_to_QleT'. apply leiblw_S_ge0_prop. Qed.

(* Set twin of leiblw_qabs_bound_prop. *)
Lemma leiblw_qabs_bound_T : forall x c : Q,
  QleT' x c -> QleT' (- x)%Q c -> QleT' (Qabs x) c.
Proof.
  intros x c H1 H2. apply Qle_to_QleT'. apply leiblw_qabs_bound_prop.
  - apply QleT'_to_Qle. exact H1.
  - apply QleT'_to_Qle. exact H2.
Qed.

(* Set twin of leiblw_nivwin_bounded_prop. *)
Lemma leiblw_nivwin_bounded_T : forall n : nat, QleT' (leiblw_nivwin n) 1%Q.
Proof. intros n. apply Qle_to_QleT'. apply leiblw_nivwin_bounded_prop. Qed.

(* Set twin of leiblw_znat_pos_prop. *)
Lemma leiblw_znat_pos_T : forall n : nat, NatLe 1 n -> ZltT 0%Z (Z.of_nat n).
Proof.
  intros n H. apply ZltT_lift. apply leiblw_znat_pos_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_qmake_eq_prop. *)
Lemma leiblw_qmake_eq_T : forall (a b : Z) (p q : positive),
  ((Id (Qeq_bool (a # p)%Q (b # q)%Q) true -> @Id Z (a * Z.pos q)%Z (b * Z.pos p)%Z) *
   (@Id Z (a * Z.pos q)%Z (b * Z.pos p)%Z ->
    Id (Qeq_bool (a # p)%Q (b # q)%Q) true))%type.
Proof.
  intros a b p q. split.
  - intros H. apply leiblw_canon_id_inv in H.
    apply (proj1 (Qeq_bool_iff (a # p)%Q (b # q)%Q)) in H.
    apply (proj1 (leiblw_qmake_eq_prop a b p q)) in H.
    rewrite <- H. apply id_refl.
  - intros H.
    assert (E : (a * Z.pos q)%Z = (b * Z.pos p)%Z) by (destruct H; reflexivity).
    apply (proj2 (leiblw_qmake_eq_prop a b p q)) in E.
    apply (proj2 (Qeq_bool_iff (a # p)%Q (b # q)%Q)) in E.
    apply leiblw_canon_id_eq. exact E.
Qed.

(* Set twin of leiblw_qmake_lt_prop. *)
Lemma leiblw_qmake_lt_T : forall (a b : Z) (p q : positive),
  ((QltT (a # p)%Q (b # q)%Q -> ZltT (a * Z.pos q)%Z (b * Z.pos p)%Z) *
   (ZltT (a * Z.pos q)%Z (b * Z.pos p)%Z -> QltT (a # p)%Q (b # q)%Q))%type.
Proof.
  intros a b p q. split.
  - intros H. apply ZltT_lift.
    apply (proj1 (leiblw_qmake_lt_prop a b p q)).
    apply QltT_to_Qlt. exact H.
  - intros H. apply Qlt_to_QltT.
    apply (proj2 (leiblw_qmake_lt_prop a b p q)).
    apply ZltT_drop. exact H.
Qed.

(* Set twin of leiblw_qmake_le_prop. *)
Lemma leiblw_qmake_le_T : forall (a b : Z) (p q : positive),
  ((QleT' (a # p)%Q (b # q)%Q -> ZleT (a * Z.pos q)%Z (b * Z.pos p)%Z) *
   (ZleT (a * Z.pos q)%Z (b * Z.pos p)%Z -> QleT' (a # p)%Q (b # q)%Q))%type.
Proof.
  intros a b p q. split.
  - intros H. apply ZleT_lift.
    apply (proj1 (leiblw_qmake_le_prop a b p q)).
    apply QleT'_to_Qle. exact H.
  - intros H. apply Qle_to_QleT'.
    apply (proj2 (leiblw_qmake_le_prop a b p q)).
    apply ZleT_drop. exact H.
Qed.

(* Set twin of leiblw_qplus_lt0_prop. *)
Lemma leiblw_qplus_lt0_T : forall (a b : Z) (p q : positive),
  ZltT 0%Z (a * Z.pos q + b * Z.pos p)%Z ->
  QltT 0%Q ((a # p) + (b # q))%Q.
Proof.
  intros a b p q H. apply Qlt_to_QltT. apply leiblw_qplus_lt0_prop.
  apply ZltT_drop. exact H.
Qed.

(* Set twin of leiblw_qplus_lt0b_prop. *)
Lemma leiblw_qplus_lt0b_T : forall (a b : Z) (p q : positive),
  ZltT (a * Z.pos q + b * Z.pos p)%Z 0%Z ->
  QltT ((a # p) + (b # q))%Q 0%Q.
Proof.
  intros a b p q H. apply Qlt_to_QltT. apply leiblw_qplus_lt0b_prop.
  apply ZltT_drop. exact H.
Qed.

(* Set twin of leiblw_qplus_le0_prop. *)
Lemma leiblw_qplus_le0_T : forall (a b : Z) (p q : positive),
  ZleT (a * Z.pos q + b * Z.pos p)%Z 0%Z ->
  QleT' ((a # p) + (b # q))%Q 0%Q.
Proof.
  intros a b p q H. apply Qle_to_QleT'. apply leiblw_qplus_le0_prop.
  apply ZleT_drop. exact H.
Qed.

(* Set twin of leiblw_qplus_le0b_prop. *)
Lemma leiblw_qplus_le0b_T : forall (a b : Z) (p q : positive),
  ZleT 0%Z (a * Z.pos q + b * Z.pos p)%Z ->
  QleT' 0%Q ((a # p) + (b # q))%Q.
Proof.
  intros a b p q H. apply Qle_to_QleT'. apply leiblw_qplus_le0b_prop.
  apply ZleT_drop. exact H.
Qed.

(* Set twin of leiblw_qplus_eq_prop. *)
Lemma leiblw_qplus_eq_T : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  @Id Z ((a * Z.pos q + b * Z.pos p) * Z.pos r)%Z (c * Z.pos (Pos.mul p q))%Z ->
  Id (Qeq_bool ((a # p) + (b # q))%Q (c # r)%Q) true.
Proof.
  intros a b p q c r H. apply leiblw_canon_id_eq.
  apply (proj2 (Qeq_bool_iff ((a # p) + (b # q))%Q (c # r)%Q)).
  assert (E : ((a * Z.pos q + b * Z.pos p) * Z.pos r)%Z
              = (c * Z.pos (Pos.mul p q))%Z) by (destruct H; reflexivity).
  apply leiblw_qplus_eq_prop. exact E.
Qed.

(* Set twin of leiblw_qneg_plus_eq_prop. *)
Lemma leiblw_qneg_plus_eq_T : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  @Id Z (((- a) * Z.pos q + (- b) * Z.pos p) * Z.pos r)%Z
        (c * Z.pos (Pos.mul p q))%Z ->
  Id (Qeq_bool (-((a # p) + (b # q)))%Q (c # r)%Q) true.
Proof.
  intros a b p q c r H. apply leiblw_canon_id_eq.
  apply (proj2 (Qeq_bool_iff (-((a # p) + (b # q)))%Q (c # r)%Q)).
  assert (E : (((- a) * Z.pos q + (- b) * Z.pos p) * Z.pos r)%Z
              = (c * Z.pos (Pos.mul p q))%Z) by (destruct H; reflexivity).
  apply leiblw_qneg_plus_eq_prop. exact E.
Qed.

(* Set twin of leiblw_mono_even_prop. *)
Lemma leiblw_mono_even_T : forall j m : nat, NatLe m j ->
  QleT' (leiblw_S (2 * m)) (leiblw_S (2 * j))%Q.
Proof.
  intros j m H. apply Qle_to_QleT'. apply leiblw_mono_even_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_mono_odd_prop. *)
Lemma leiblw_mono_odd_T : forall j m : nat, NatLe m j ->
  QleT' (leiblw_S (2 * j + 1)) (leiblw_S (2 * m + 1))%Q.
Proof.
  intros j m H. apply Qle_to_QleT'. apply leiblw_mono_odd_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_lower_even_e_prop. *)
Lemma leiblw_lower_even_e_T : forall j m : nat, NatLe (m + 1) j ->
  QleT' (leiblw_gap (2 * m)) (leiblw_S (2 * j) - leiblw_S (2 * m))%Q.
Proof.
  intros j m H. apply Qle_to_QleT'. apply leiblw_lower_even_e_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_lower_even_o_prop. *)
Lemma leiblw_lower_even_o_T : forall j m : nat, NatLe m j ->
  QleT' (leiblw_gap (2 * m)) (leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q.
Proof.
  intros j m H. apply Qle_to_QleT'. apply leiblw_lower_even_o_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_lower_odd_e_prop. *)
Lemma leiblw_lower_odd_e_T : forall j m : nat, NatLe (m + 1) j ->
  QleT' (leiblw_gap (2 * m + 1))
        (leiblw_S (2 * m + 1) - leiblw_S (2 * j))%Q.
Proof.
  intros j m H. apply Qle_to_QleT'. apply leiblw_lower_odd_e_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_lower_odd_o_prop. *)
Lemma leiblw_lower_odd_o_T : forall j m : nat, NatLe (m + 1) j ->
  QleT' (leiblw_gap (2 * m + 1))
        (leiblw_S (2 * m + 1) - leiblw_S (2 * j + 1))%Q.
Proof.
  intros j m H. apply Qle_to_QleT'. apply leiblw_lower_odd_o_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_dist_prop. *)
Lemma leiblw_dist_T : forall n k : nat, NatLe (S n) k ->
  QleT' (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n)).
Proof.
  intros n k H. apply Qle_to_QleT'. apply leiblw_dist_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_dist_set_prop. *)
Lemma leiblw_dist_set_T : forall n : nat,
  sigT (fun N : nat => forall k : nat, NatLe N k ->
    leiblw_Id (leiblw_Qleb (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n))) true).
Proof.
  intros n. exists (S n). intros k H.
  apply leiblw_id_eq_prop. apply leiblw_Qleb_true_prop.
  apply leiblw_dist_prop. apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_natwin_ge_prop. *)
Lemma leiblw_natwin_ge_T : forall b n : nat, NatLe 1 b ->
  QleT' (4 # 1)%Q (leiblw_natwin b n).
Proof.
  intros b n H. apply Qle_to_QleT'. apply leiblw_natwin_ge_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_zf_ge1_prop. *)
Lemma leiblw_zf_ge1_T : forall n : nat, ZleT 1%Z (leiblw_zf n).
Proof.
  intros n. apply ZleT_lift. apply leiblw_zf_ge1_prop.
Qed.

(* Set twin of leiblw_zf_ge_id_prop. *)
Lemma leiblw_zf_ge_id_T : forall n : nat, NatLe 1 n ->
  ZleT (Z.of_nat n) (leiblw_zf n).
Proof.
  intros n H. apply ZleT_lift. apply leiblw_zf_ge_id_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_zf_lower_prop. *)
Lemma leiblw_zf_lower_T : forall n : nat, NatLe 1 n ->
  ZleT (Z.of_nat (2 * n - 1) * Z.of_nat (2 * n))%Z (leiblw_zf (2 * n)).
Proof.
  intros n H. apply ZleT_lift. apply leiblw_zf_lower_prop.
  apply NatLe_drop. exact H.
Qed.

(* Set twin of leiblw_escape_obstacle_prop. *)
Lemma leiblw_escape_obstacle_T : forall (b m : nat) (q : Q), NatLe 2 b ->
  QleT' (leiblw_S (2 * m + 2)) q ->
  QleT' q (leiblw_S (2 * m + 1)) ->
  forall n : nat, QleT' (Qabs ((q - leiblw_S n)%Q)) (leiblw_natwin b n).
Proof.
  intros b m q Hb Hlo Hhi n. apply Qle_to_QleT'.
  apply (leiblw_escape_obstacle_prop b m q).
  - apply NatLe_drop. exact Hb.
  - apply QleT'_to_Qle. exact Hlo.
  - apply QleT'_to_Qle. exact Hhi.
Qed.

(* Set twin of leiblw_natwin_unbounded_prop. *)
Lemma leiblw_natwin_unbounded_T : forall b B : nat, NatLe 1 b ->
  sigT (fun n : nat =>
    leiblw_Id (leiblw_Qltb ((Z.of_nat B # 1)%Q) (leiblw_natwin b n)) true).
Proof.
  intros b B H.
  destruct (leiblw_natwin_unbounded_prop b B (NatLe_drop 1 b H)) as [n Hn].
  exists n. exact Hn.
Qed.

Print Assumptions leiblw_canon_id_eq.
Print Assumptions leiblw_canon_id_inv.
Print Assumptions QltT_to_Qlt.
Print Assumptions Qlt_to_QltT.
Print Assumptions QleT'_to_Qle.
Print Assumptions Qle_to_QleT'.
Print Assumptions leiblw_pos_succ_T.
Print Assumptions leiblw_pos_succ1_T.
Print Assumptions leiblw_zpos_mul_T.
Print Assumptions leiblw_zf_2n1_T.
Print Assumptions leiblw_zf_2n3_T.
Print Assumptions leiblw_even_2m_T.
Print Assumptions leiblw_even_2m1_T.
Print Assumptions leiblw_par_decomp_T.
Print Assumptions leiblw_t_pos_case_T.
Print Assumptions leiblw_t_neg_case_T.
Print Assumptions leiblw_t_even_pos_T.
Print Assumptions leiblw_t_odd_neg_T.
Print Assumptions leiblw_qabs_id_T.
Print Assumptions leiblw_qabs_neg_T.
Print Assumptions leiblw_qopp_lt_T.
Print Assumptions leiblw_qle_add_r_T.
Print Assumptions leiblw_qle_add2_r_T.
Print Assumptions leiblw_qle_add_l_T.
Print Assumptions leiblw_step_even_pos_T.
Print Assumptions leiblw_step_odd_neg_T.
Print Assumptions leiblw_interlace_T.
Print Assumptions leiblw_gap_pos_T.
Print Assumptions leiblw_natwin_mono_T.
Print Assumptions leiblw_S_le4_T.
Print Assumptions leiblw_S_ge0_T.
Print Assumptions leiblw_qabs_bound_T.
Print Assumptions leiblw_nivwin_bounded_T.

(* Assumption audits for the twins above. *)
Print Assumptions leiblw_znat_pos_T.
Print Assumptions leiblw_qmake_eq_T.
Print Assumptions leiblw_qmake_lt_T.
Print Assumptions leiblw_qmake_le_T.
Print Assumptions leiblw_qplus_lt0_T.
Print Assumptions leiblw_qplus_lt0b_T.
Print Assumptions leiblw_qplus_le0_T.
Print Assumptions leiblw_qplus_le0b_T.
Print Assumptions leiblw_qplus_eq_T.
Print Assumptions leiblw_qneg_plus_eq_T.
Print Assumptions leiblw_mono_even_T.
Print Assumptions leiblw_mono_odd_T.
Print Assumptions leiblw_lower_even_e_T.
Print Assumptions leiblw_lower_even_o_T.
Print Assumptions leiblw_lower_odd_e_T.
Print Assumptions leiblw_lower_odd_o_T.
Print Assumptions leiblw_dist_T.
Print Assumptions leiblw_dist_set_T.
Print Assumptions leiblw_natwin_ge_T.
Print Assumptions leiblw_zf_ge1_T.
Print Assumptions leiblw_zf_ge_id_T.
Print Assumptions leiblw_zf_lower_T.
Print Assumptions leiblw_escape_obstacle_T.
Print Assumptions leiblw_natwin_unbounded_T.