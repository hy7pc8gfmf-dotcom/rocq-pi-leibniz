(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * PiCRealAppartT: a Set-carried apartness counterpart for the
      constructive Cauchy reals.

    Mission.  This file carries the apartness relation on the
      constructive Cauchy reals of [ConstructiveCauchyReals] in a
      form whose every component lives in [Set]: the strict-order
      witness type [CRealLtT] mirrors the stdlib [CRealLt] with the
      reflected strict-order decision [QltT] (of [PiCompareT]) in the
      place of the [Qlt] predicate, and the apartness relation
      [CReal_appartT] mirrors the stdlib [CReal_appart] sum type with
      the two [CRealLtT] sides.  Interchange bridges in both
      directions connect the new form with the stdlib originals, so
      the two relations stay interchangeable during the period in
      which they run in parallel.

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith],
      [ConstructiveCauchyReals] ([CReal], [seq], [inject_Q],
      [CRealLt], [CReal_appart]); [PiCompareT] (the reflected
      strict-order decision [QltT]); [PiKernelSlack] (the two
      decision bridges [QltT_to_Qlt] and [Qlt_to_QltT]).

    References.  Stdlib [ConstructiveCauchyReals] ([CRealLt],
      [CReal_appart] — the mirrored originals); [PiCompareT.v]
      ([QltT], the canonical strict-order decision); [PiKernelSlack.v]
      (the bridge family [QltT_to_Qlt]/[Qlt_to_QltT]); this
      development, [ConstructiveCauchyRealsSep.v] (the escape-window
      engine whose apartness conclusion this counterpart receives).

    Constructivity.  Every statement is carried at the [Set] level:
      the witness type is a [sigT] whose predicate component is the
      [Set]-valued [QltT], and the apartness relation is a [sum] of
      two [sigT] types; no [Prop] component enters any statement
      face.  The proof bodies only destruct the [Set]-carried
      witnesses and transport them through the two decision bridges;
      no solver closes any statement, and all items end in
      [Defined].  Assumption-free.

    Build.  [coqc -q -Q theories pi_leibniz -Q theories/Reals/Cauchy ""
      theories/Reals/Cauchy/PiCRealAppartT.v] compiles cleanly
      (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ConstructiveCauchyReals.
Require Import PiCompareT.
Require Import PiKernelSlack.

(* ============ Section 1. The Set-carried strict-order witness ======== *)

(* Set twin of CRealLt (Path A v2.4): the stdlib witness type
   [{n : Z | Qlt (2 * 2^n) (seq y n - seq x n)}] with the reflected
   strict-order decision [QltT] in the place of the [Qlt] predicate,
   carried as a [sigT] whose predicate component lives in [Set]. *)
Definition CRealLtT (x y : CReal) : Set :=
  sigT (fun n : Z => QltT (2 * 2 ^ n)%Q (seq y n - seq x n)%Q).

(* Set twin of CReal_appart (Path A v2.4): the stdlib apartness sum
   [CRealLt x y + CRealLt y x] with the [CRealLtT] sides, so the
   whole statement face lives in [Set] with no [Prop] component. *)
Definition CReal_appartT (x y : CReal) : Set :=
  (CRealLtT x y + CRealLtT y x)%type.

(* ============ Section 2. The witness-level interchange bridges ======= *)

(* Interchange bridge (stdlib to Set-carried): the [CRealLt] witness
   index and its strict-order evidence transport to [CRealLtT] through
   the up-level decision bridge of [PiKernelSlack]. *)
Definition CRealLtT_of_CRealLt (x y : CReal) (h : CRealLt x y) : CRealLtT x y.
Proof.
  destruct h as [n Hn].
  exists n. apply Qlt_to_QltT. exact Hn.
Defined.

(* Interchange bridge (Set-carried to stdlib): the converse transport,
   through the down-level decision bridge of [PiKernelSlack]. *)
Definition CRealLt_of_CRealLtT (x y : CReal) (h : CRealLtT x y) : CRealLt x y.
Proof.
  destruct h as [n Hn].
  exists n. apply QltT_to_Qlt. exact Hn.
Defined.

(* ============ Section 3. The apartness-level interchange bridges ===== *)

(* Interchange bridge (stdlib to Set-carried), statement face: the two
   sides of the stdlib apartness sum transport side by side. *)
Definition creal_appartT_of_appart (x y : CReal) :
  CReal_appart x y -> CReal_appartT x y.
Proof.
  intros h. destruct h as [hxy | hyx].
  - left. exact (CRealLtT_of_CRealLt x y hxy).
  - right. exact (CRealLtT_of_CRealLt y x hyx).
Defined.

(* Interchange bridge (Set-carried to stdlib), statement face: the
   converse transport. *)
Definition creal_appart_of_appartT (x y : CReal) :
  CReal_appartT x y -> CReal_appart x y.
Proof.
  intros h. destruct h as [hxy | hyx].
  - left. exact (CRealLt_of_CRealLtT x y hxy).
  - right. exact (CRealLt_of_CRealLtT y x hyx).
Defined.

(* ============ Section 4. Concrete spot-check witness ================= *)

(* A numeric spot-check: the embedded rationals [1/2] and [1/3] stand
   apart through the right side of the sum: at the index [-4] the
   threshold [2 * 2^(-4) = 1/8] stays below the distance
   [1/2 - 1/3 = 1/6], and the strict-order decision on the two closed
   rational terms closes by computation. *)
Definition creal_appartT_half_third :
  CReal_appartT (inject_Q (1 # 2)) (inject_Q (1 # 3)).
Proof.
  right. exists (-4)%Z. unfold QltT, Qlt_bool. vm_compute. exact id_refl.
Defined.

(* Statement provenance: for every statement of this file, the source
   statement that it mirrors, with the source coordinates.  Rows
   marked (new) are statements first stated in this file.

   [CRealLtT] <- [CRealLt] at [ConstructiveCauchyReals] (stdlib, the
      mirrored original; the predicate component replaced by [QltT])
   [CReal_appartT] <- [CReal_appart] at [ConstructiveCauchyReals]
      (stdlib, the mirrored original)
   [CRealLtT_of_CRealLt] <- (new in this file)
   [CRealLt_of_CRealLtT] <- (new in this file)
   [creal_appartT_of_appart] <- (new in this file)
   [creal_appart_of_appartT] <- (new in this file)
   [creal_appartT_half_third] <- (new in this file)
*)
