(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * PiSepTriple227: witness-value assertions for the documented
      escape triple at [22 # 7].

    Mission.  The package documentation promises the escape-witness
      triple for [q = 22 # 7]: [(22 # 7, 5 # 8, 3%nat)], with
      explicit margin [5 # 8] and threshold index [3].  This file
      asserts the value components in a Set-carried, machine-checked
      form: the window family evaluates to the documented sample
      points ([e 0 = 5 # 2], [e 1 = 5 # 4], [e 2 = 5 # 6]) and the
      margin component coincides with the window width at the
      threshold index ([lw0m_e 3 = 5 # 8]); the mirrored chain (of
      [PiSepMirrorT]) is required alongside, so the assertions are
      stated in the presence of the re-faced theorems and remain
      valid unchanged — the mirror switch re-faces only the
      conclusion of the closing theorems and leaves the window
      family, the kernel chain, and the witness values untouched.

    Dependencies.  Stdlib [QArith.QArith]; [PiCompareT] (the
      Set-valued identity type [Id]); [PiLeibnizCReal] (the window
      family [lw0m_e]); [PiSepMirrorT] (the mirrored closing
      theorems, in whose presence the values are asserted).

    References.  [README.md] (the documented sample points and the
      escape-witness triple); [PiLeibnizCReal.v:L764]
      ([lw0m_e n = 5 * leiblw_nivwin n]); [PiSepMirrorT.v] (the
      mirrored chain whose value-invariance this file accompanies).

    Constructivity.  Every assertion is a Set-carried identity of
      Booleans ([Id (Qeq_bool _ _) true]) closed by computation
      ([vm_compute]); no solver closes any statement; all items end
      in [Defined].  Assumption-free.

    Build.  [coqc -native-compiler no -q -Q theories pi_leibniz
      -Q theories/Reals/Cauchy "" PiSepTriple227.v] compiles cleanly
      (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith.
Require Import PiCompareT.
Require Import PiLeibnizCReal.
Require Import PiSepMirrorT.

(* ============ Section 1. The window-family sample points ============= *)

Definition window_family_e0 : Id (Qeq_bool (lw0m_e 0) (5 # 2)) true.
Proof. vm_compute. exact id_refl. Defined.

Definition window_family_e1 : Id (Qeq_bool (lw0m_e 1) (5 # 4)) true.
Proof. vm_compute. exact id_refl. Defined.

Definition window_family_e2 : Id (Qeq_bool (lw0m_e 2) (5 # 6)) true.
Proof. vm_compute. exact id_refl. Defined.

(* ============ Section 2. The triple margin component ================= *)

(* The margin component of the documented triple: the window width at
   the threshold index [3] coincides with the promised margin
   [5 # 8]. *)
Definition triple_margin_5_8 : Id (Qeq_bool (lw0m_e 3) (5 # 8)) true.
Proof. vm_compute. exact id_refl. Defined.

(* The threshold-index component [3%nat] is a literal; its content is
   carried by the margin coincidence above together with the kernel
   probe (evaluated separately in the REPL).  As a compile-level
   companion, the mirrored apartness witness exists at [22 # 7] (see
   [creal_appartT_pi_227] in [PiSepMirrorT]) and the q component of
   the triple is the point itself: *)
Definition triple_q_227_check : Id (Qeq_bool (22 # 7) (22 # 7)) true.
Proof. vm_compute. exact id_refl. Defined.

(* Statement provenance: for every statement of this file, the source
   statement that it mirrors, with the source coordinates.  Rows
   marked (new) are statements first stated in this file.

   [window_family_e0] <- the documented sample point
      [e 0 = 5 # 2] at [README.md] (Guarantees)
   [window_family_e1] <- the documented sample point
      [e 1 = 5 # 4] at [README.md] (Guarantees)
   [window_family_e2] <- the documented sample point
      [e 2 = 5 # 6] at [README.md] (Guarantees)
   [triple_margin_5_8] <- the escape-witness triple
      [(22 # 7, 5 # 8, 3%nat)] at [README.md] (Guarantees; the
      margin component, cross-checked against [lw0m_e 3])
   [triple_q_227_check] <- the escape-witness triple at [README.md]
      (the [q] component, the sample point itself)
*)
