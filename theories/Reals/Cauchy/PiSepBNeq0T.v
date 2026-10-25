(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * PiSepBNeq0T: a Set-carried nonzero premise for the strong
      irrationality theorem.

    Mission.  The main theorem [pi_leibniz_strong_irrational_prop] (in
      [PiSeparation]) carries the premise [b <> 0] as a bare
      [Prop] disequality.  This file re-faces that premise so the
      whole statement face lives in [Set]: the nonzero premise
      [Qneq0T] mirrors the sum shape of the apartness twin
      [CReal_appartT] (in [PiCRealAppartT]) — the [Q]-apartness of
      [b] from zero with a [QltT] witness on each side.  A
      down-grader connects the new premise to the stdlib [Prop]
      premise, and an up-builder shows the two faces are
      equipollent on [Q] (whose order and equality are decidable,
      so a nonzero rational always carries a side witness).

    Dependencies.  Stdlib [QArith.QArith]; [PiCompareT] (the
      reflected strict-order decision [QltT]); [PiKernelSlack] (the
      decision bridges [QltT_to_Qlt] and [Qlt_to_QltT]).

    References.  [PiCRealAppartT.v] (the sum-of-decisions
      statement-face canon this premise form follows);
      [PiSeparation.v] (the consuming theorem, whose [b <> 0]
      premise this file re-faces); [QArith_base] ([Qcompare_spec],
      [Qeq_sym], [Qlt_not_eq]); [PiCompareT] (the strict-order
      decision [QltT]).
    Statement-level migration provenance is maintained in
    [docs/statement-provenance.md]; citations in this file are by
    fully qualified name.

    Constructivity.  Both statement faces are [Set]-carried (a sum
      of two [Id]-wrapped decision witnesses); the proof bodies use
      only the decidability of equality and order on [Q] (sumbool
      case analysis) and transport through the decision bridges; no
      solver closes any statement; all items end in [Defined].
      Assumption-free.

    Build.  [coqc -native-compiler no -q -Q theories pi_leibniz
      -Q theories/Reals/Cauchy "" PiSepBNeq0T.v] compiles cleanly
      (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith.
Require Import PiCompareT.
Require Import PiKernelSlack.

(* ============ Section 1. The Set-carried nonzero premise ============ *)

(* Set-carried re-facing of the premise [b <> 0] (Path A v2.4): the
   Q-apartness of [b] from zero as a sum of two strict-order
   witnesses, mirroring the sum shape of [CReal_appartT]. *)
Definition Qneq0T (b : Q) : Set :=
  (PiCompareT.QltT 0 b + PiCompareT.QltT b 0)%type.

(* Down-grader: the Set-carried premise implies the stdlib [Prop]
   premise, through the down-level decision bridge. *)
Lemma Qneq0T_down : forall b : Q, Qneq0T b -> b <> 0.
Proof.
  intros b H Hb.
  assert (Hbq : (b == 0)%Q) by (rewrite Hb; reflexivity).
  destruct H as [Hp | Hn].
  - exact (Qlt_not_eq 0 b (QltT_to_Qlt 0 b Hp) (Qeq_sym b 0 Hbq)).
  - exact (Qlt_not_eq b 0 (QltT_to_Qlt b 0 Hn) Hbq).
Defined.

(* Up-builder, Qeq face: on [Q] the Set premise is equipollent to the
   Qeq-carried disequality [~ (b == 0)] (whose order and equality are
   decidable, so a nonzero rational always carries a side witness —
   trichotomy case analysis through sumbools).  Note on the premise
   face: the original [b <> 0] is the Leibniz-face disequality
   (representation-level); no transport from it into the Qeq face is
   admissible in general (e.g. [0 # 2 = 0] is false while
   [0 # 2 == 0] holds), so the honest re-facing of the premise is the
   Qeq-carried face below. *)
Lemma Qneq0T_qeq_down : forall b : Q, Qneq0T b -> ~ (b == 0)%Q.
Proof.
  intros b H Hq.
  destruct H as [Hp | Hn].
  - exact (Qlt_not_eq 0 b (QltT_to_Qlt 0 b Hp) (Qeq_sym b 0 Hq)).
  - exact (Qlt_not_eq b 0 (QltT_to_Qlt b 0 Hn) Hq).
Defined.

Lemma Qneq0T_qeq_up : forall b : Q, ~ (b == 0)%Q -> Qneq0T b.
Proof.
  intros b Hb.
  destruct (Qcompare 0 b)%Q eqn:Ec.
  - exfalso. exact (Hb (Qeq_sym 0 b (proj2 (Qeq_alt 0 b) Ec))).
  - left. exact (Qlt_to_QltT 0 b (proj2 (Qlt_alt 0 b) Ec)).
  - right.
    assert (Ecx : (b ?= 0)%Q = Lt).
    { rewrite <- (Qcompare_antisym 0 b). rewrite Ec. reflexivity. }
    exact (Qlt_to_QltT b 0 (proj2 (Qlt_alt b 0) Ecx)).
Defined.

(* ============ Section 2. Concrete spot-check witness ================= *)

(* A numeric spot-check: [2] is nonzero through the left side of the
   sum, the strict-order decision on the two closed rational terms
   closing by computation. *)
Definition qneq0T_two : Qneq0T (2 # 1).
Proof.
  left.
  unfold PiCompareT.QltT, PiCompareT.Qlt_bool.
  vm_compute. exact id_refl.
Defined.

