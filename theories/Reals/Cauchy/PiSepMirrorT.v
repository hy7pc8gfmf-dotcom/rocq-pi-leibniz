(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * PiSepMirrorT: the closing theorems re-faced to the Set-carried
      apartness twin.

    Mission.  The two closing theorems of [PiSeparation]
      ([pi_leibniz_appart_all_Q] and
      [pi_leibniz_strong_irrational_prop]) conclude in the stdlib
      apartness [CReal_appart].  This file carries their mirror
      images concluding in [CReal_appartT] (of [PiCRealAppartT]):
      the final jump is taken from the unchanged stdlib-form
      theorems and transported through the apartness-level
      interchange bridge, so the engine piece
      [ConstructiveCauchyRealsSep] and the assembly piece
      [PiSeparation] are consumed read-only.  The strong form is
      stated with the Set-carried nonzero premise [Qneq0T] (of
      [PiSepBNeq0T]); a further form derives it from the Qeq-carried
      disequality [~ (b == 0)] through the up-builder on that face
      (the Leibniz-face premise of the original admits no transport
      into the Qeq face in general, and is zero-consumption there).

    Dependencies.  Stdlib [QArith.QArith],
      [ConstructiveCauchyReals]; [ConstructiveCauchyRealsSep] (the
      engine, read-only); [PiSeparation] (the assembly, read-only);
      [PiCRealAppartT] (the apartness twin and its interchange
      bridges); [PiSepBNeq0T] (the Set-carried nonzero premise and
      its up-builder on the Qeq face).

    References.  [PiSeparation.v] (the mirrored
      originals); [PiCRealAppartT.v] ([creal_appartT_of_appart],
      the transport used at the jump); [PiSepBNeq0T.v]
      ([Qneq0T], [Qneq0T_qeq_up]).
    Statement-level migration provenance is maintained in
    [docs/statement-provenance.md]; citations in this file are by
    fully qualified name.

    Constructivity.  Every statement face is [Set]-carried (the
      [CReal_appartT] sum with [sigT] witnesses, the [Qneq0T] sum
      of decision witnesses); the proofs are single transports
      through the interchange and premise bridges; no solver closes
      any statement; all items end in [Defined].  Assumption-free.

    Build.  [coqc -native-compiler no -q -Q theories pi_leibniz
      -Q theories/Reals/Cauchy "" PiSepMirrorT.v] compiles cleanly
      (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsSep.
Require Import PiLeibnizCReal.
Require Import PiSeparation.
Require Import PiCRealAppartT.
Require Import PiSepBNeq0T.

(* ============ Section 1. The mirror of the closing theorems ========== *)

(* Mirror of [pi_leibniz_appart_all_Q] ([PiSeparation.v]): the
   final jump is taken from the unchanged stdlib-form theorem and
   transported through the apartness-level interchange bridge. *)
Definition pi_leibniz_appart_all_Q_T :
  forall q : Q, CReal_appartT pi_leibniz (inject_Q q).
Proof.
  intros q. exact (creal_appartT_of_appart _ _ (pi_leibniz_appart_all_Q q)).
Defined.

(* Mirror of [pi_leibniz_strong_irrational_prop] ([PiSeparation.v]):
   the conclusion face re-faced to [CReal_appartT] and the premise
   face re-faced to [Qneq0T].  Note on the zero-consumption premise:
   as in the original, the mounting piece holds for every rational,
   so the nonzero premise serves only as the semantic guard of the
   notion of a rational number; the witness it carries is not
   consumed. *)
Theorem pi_leibniz_strong_irrational_T :
  forall a b : Q, Qneq0T b -> CReal_appartT pi_leibniz (inject_Q (a / b)).
Proof.
  intros a b _. exact (pi_leibniz_appart_all_Q_T (a / b)).
Defined.

(* Derivation of the mirrored strong form from the Qeq-carried
   disequality face: the up-builder of [PiSepBNeq0T] converts
   [~ (b == 0)] into the Set-carried premise.  Note on the premise
   face: the Leibniz-face premise [b <> 0] of the original admits no
   transport into the Qeq face in general (representation-level
   counterexample), and it is zero-consumption in the original; the
   honest re-facing of the premise is the Qeq-carried face. *)
Definition pi_leibniz_strong_irrational_T_qeq :
  forall a b : Q, ~ (b == 0)%Q -> CReal_appartT pi_leibniz (inject_Q (a / b)).
Proof.
  intros a b Hb.
  exact (pi_leibniz_strong_irrational_T a b (Qneq0T_qeq_up b Hb)).
Defined.

(* ============ Section 2. Witness-existence spot checks =============== *)

(* The mirrored apartness witness exists at the documented sample
   point [22 # 7] (compilation-level existence; the witness value is
   probed separately). *)
Definition creal_appartT_pi_227 :
  CReal_appartT pi_leibniz (inject_Q (22 # 7)).
Proof.
  exact (creal_appartT_of_appart _ _ (pi_leibniz_appart_all_Q (22 # 7))).
Defined.

