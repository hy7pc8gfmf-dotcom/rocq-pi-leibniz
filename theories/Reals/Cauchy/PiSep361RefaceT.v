(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * PiSep361RefaceT: the registration of the re-faced premise of
      [pi_leibniz_strong_irrational], in machine-checked form.

    Mission.  The premise [b <> 0] of [pi_leibniz_strong_irrational]
      ([PiSeparation.v:L361-L362]) is re-faced to the Set-carried
      [Qneq0T] of [PiSepBNeq0T].  This file registers that re-facing
      in machine-checked form.  The registration is rooted at the
      Qeq-carried disequality [~ (b == 0)] — equipollent to [Qneq0T]
      by the bridges of [PiSepBNeq0T] — because the Leibniz-carried
      face admits no transport into the Qeq face: that negative fact
      is proved here from the representation counterexample
      [(0 # 2)], which is Leibniz-unequal to [0] (the denominators
      differ) while Qeq-equal to [0] (the values coincide).  The
      registered chain is one-way: from [~ (b == 0)] the up-builder
      yields [Qneq0T b], and from [Qneq0T b] the down-grader yields
      the Leibniz face [b <> 0]; the reverse direction is blocked by
      the counterexample.  In the consuming theorem the premise is
      zero-consumption (the mounting piece holds for every rational),
      so the re-facing changes the statement face only.

    Dependencies.  Stdlib [QArith.QArith]; [PiCompareT]; [PiSepBNeq0T]
      ([Qneq0T], [Qneq0T_qeq_up], [Qneq0T_down], and the premise-face
      notes this file registers).

    References.  [PiSeparation.v:L361-L362] (the audited premise
      slot); [PiSepBNeq0T.v] (the Set-carried premise and its
      bridges); [PiCRealAppartT.v] (the sum-of-decisions
      statement-face canon the re-facing follows).

    Constructivity.  [leibniz_qeq_transport_blocked] is a negative
      statement (a refutation of an inadmissible transport, which has
      no Set-carried form); its proof body is a single instantiation
      fed by computation ([vm_compute] closes the Qeq fact;
      discrimination closes the Leibniz fact).  [qeq_face_to_leibniz_face]
      composes the two bridges of [PiSepBNeq0T].  No solver closes
      any statement; all items end in [Defined].  Assumption-free.

    Build.  [coqc -native-compiler no -q -Q theories pi_leibniz
      -Q theories/Reals/Cauchy "" PiSep361RefaceT.v] compiles cleanly
      (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith.
Require Import PiCompareT.
Require Import PiSepBNeq0T.

(* ============ Section 1. The transport blockader ===================== *)

(* The Leibniz-face premise admits no transport into the Qeq face.
   The rational [(0 # 2)] witnesses the block: it is Leibniz-unequal
   to [0] (representation level: [Qmake 0 2] and [Qmake 0 1] differ)
   while Qeq-equal to [0] (value level), so any candidate transport
   [forall b : Q, b <> 0 -> ~ (b == 0)] applied at [(0 # 2)] yields
   the refutable conclusion [~ ((0 # 2) == 0)]. *)
Definition leibniz_qeq_transport_blocked :
  ~ (forall b : Q, b <> 0 -> ~ (b == 0)%Q).
Proof.
  intro H.
  assert (Hn : (0 # 2) <> 0).
  { intro E. discriminate E. }
  assert (Hq : ((0 # 2) == 0)%Q).
  { vm_compute. exact eq_refl. }
  exact (H (0 # 2) Hn Hq).
Defined.

(* ============ Section 2. The registered one-way chain ================ *)

(* The premise slot of [pi_leibniz_strong_irrational]
   ([PiSeparation.v:L361-L362]) registers as the Set-carried
   [Qneq0T], rooted at the Qeq face: the Qeq-carried disequality
   builds up into [Qneq0T], and [Qneq0T] grades down to the Leibniz
   face.  The reverse direction is blocked by Section 1. *)
Definition qeq_face_to_leibniz_face :
  forall b : Q, ~ (b == 0)%Q -> b <> 0.
Proof.
  intros b Hb. exact (Qneq0T_down b (Qneq0T_qeq_up b Hb)).
Defined.

(* Statement provenance: for every statement of this file, the source
   statement that it mirrors or registers, with the source
   coordinates.  Rows marked (new) are statements first stated in
   this file.

   [leibniz_qeq_transport_blocked] <- (new in this file;
      machine-checks the premise-face note recorded at
      [PiSepBNeq0T.v] and fixes the audited premise slot
      [PiSeparation.v:L361-L362] to its honest re-facing)
   [qeq_face_to_leibniz_face] <- composition of [Qneq0T_qeq_up] and
      [Qneq0T_down] at [PiSepBNeq0T.v] (the registered one-way
      chain, stated here for reference)
*)
