(* ==== Section 1. Set-carrier twins for renamed Prop statements (batch 2a) ==== *)

(* Mission: Set-carrier twins (Path A v2.4) for rename-roster names without a
   twin, batch 2a: the PiVertexPolyDiff / PiCosTailScan / PiCosApproxRoot
   families. Conclusions and Q-comparison premises are recast on QltT / QleT' /
   QeqT / Id carriers; nat-order innards inside sigT keep the (<=)%nat face
   the landed twins use. *)
(* Dependencies: PiVertexPolyDiff, PiKernelSlack (bridges, q_neq_of_ltT,
   cos_partial, q_pow, vt_bisect). *)
(* References: original statements vt_qpos_neq_prop and vt_parity_prop in
   PiVertexPolyDiff. The vt_pow_half_archT and vt_bisect_specT twins moved
   home to PiCosApproxRoot and PiCosTailScan beside their originals (MIG5,
   20261025) so that the consumer modules can reach them without an import
   cycle through this file. *)
(* Constructivity: proofs demote Set premises via the canonical bridges, reuse
   the original lemma, rebuild Set-conclusions componentwise. No axioms, no
   Admitted, no new Prop statements. *)
(* Build: coqc -Q . "" after the batch-1 chain in the same world.
   Section 1 retains vt_qpos_neqT; the vt_pow_half_archT and vt_bisect_specT
   twins moved home to PiCosApproxRoot and PiCosTailScan (MIG5, 20261025). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import PiCompareT.
Require Import PiKernelSlack.
Require Import PiVertexPolyDiff.

(* Set twin of vt_qpos_neq_prop (Path A v2.4) *)
Lemma vt_qpos_neqT : forall x : Q, QltT 0 x -> QeqT x 0 -> Empty_set.
Proof.
  intros x H1 H2.
  apply (q_neq_of_ltT x).
  - apply QltT_to_Qlt. exact H1.
  - apply qeqT_imp_qeq. exact H2.
Qed.

(* Set twin of vt_parity_prop (Path A v2.4): DEFERRED to the gap ledger.
   The Set-level disjunction witness cannot be transported out of the Prop
   disjunction (no large elimination of Prop), and a self-contained
   constructive parity needs its own add/mul transport family, which exceeds
   this batch. Registered as W-PARITY. *)



(* Set twin of approx_root_cos_prop (Path A v2.4): DEFERRED to the gap ledger
   as W-EXBLOCK. The original statement carries an inner Prop existential
   (exists N : nat, ...) whose informative bound cannot be eliminated into the
   Set-level sigT innard of the twin (no large elimination of Prop). A honest
   Set twin needs the original statement recast with a Set-side witness, which
   belongs to the source-statement wave, not to twin casting. *)



(* ==== Section 2. Extraction audit probe ==== *)

Print Assumptions vt_qpos_neqT.
