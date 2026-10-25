(* ===================================================================== *)
(* Module.  wall2_apart.v                                                *)
(*                                                                       *)
(* Mission.  Carrier audit and identical-statement twin of the escape-  *)
(*   window separation theorem for the constructive Cauchy reals.       *)
(*   The original [ConstructiveCauchyRealsSep.v                         *)
(*   creal_escape_window_apart] was recorded as W-APART ("CReal_appart  *)
(*   conclusion face is Prop; Set apartness carrier not yet in the      *)
(*   world").  First-hand reading of the stdlib source shows the        *)
(*   opposite: [CRealLt] is a Set-level sigma of margin witnesses and   *)
(*   [CReal_appart] is the Set-level sum of the two margin witnesses.   *)
(*   The two definitions below make that carrier fact mechanical:       *)
(*   they elaborate only if the apartness carrier lives in Set.         *)
(*                                                                       *)
(* Dependencies.  ConstructiveCauchyRealsSep (this directory), Stdlib    *)
(*   ConstructiveCauchyReals, Stdlib QArith.                            *)
(*                                                                       *)
(* References.  Stdlib ConstructiveCauchyReals.v [:83-90] (CRealLt,     *)
(*   CReal_appart); ConstructiveCauchyRealsSep.v creal_escape_window.   *)
(*                                                                       *)
(* Constructivity.  The twin statement is the original statement (the   *)
(*   conclusion face is already Set-carried); it is discharged by the   *)
(*   original constructive proof.  No axioms, no Admitted.              *)
(*                                                                       *)
(* Build.  coqc -Q . "" wall2_apart.v  (born-in-place, Rocq 9.1)         *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsSep.

(* Mechanical carrier check: elaborates only if [CReal_appart] is a
   Set-valued family. *)
Definition wall2_apart_carrier_check (x y : CReal) : Set := CReal_appart x y.

(* Identical-statement Set twin: the conclusion face is already the
   Set-carried stdlib apartness sum, so the twin coincides with the
   original statement and is discharged by the original constructive
   proof. *)
Theorem creal_escape_window_apartT :
  forall (x : CReal) (e : nat -> Q),
    creal_escape_window x e ->
    forall q : Q, CReal_appart x (inject_Q q).
Proof. exact creal_escape_window_apart_prop. Qed.

Print Assumptions creal_escape_window_apartT.
