(* ==== Section 1. Set-carrier twins for renamed Prop statements (batch 2a) ==== *)

(* Mission: Set-carrier twins (Path A v2.4) for rename-roster names without a
   twin, batch 2a: the PiVertexPolyDiff / PiCosTailScan / PiCosApproxRoot
   families. Conclusions and Q-comparison premises are recast on QltT / QleT' /
   QeqT / Id carriers; nat-order innards inside sigT keep the (<=)%nat face
   the landed twins use. *)
(* Dependencies: PiCosApproxRoot (which transitively supplies PiVertexPolyDiff
   and PiCosTailScan), PiKernelSlack (bridges, q_neq_of_ltT, cos_partial,
   q_pow, vt_bisect). *)
(* References: original statements vt_qpos_neq_prop and vt_parity_prop in
   PiVertexPolyDiff; vt_bisect_spec_prop in PiCosTailScan; vt_pow_half_arch_prop
   and approx_root_cos_prop in PiCosApproxRoot. *)
(* Constructivity: proofs demote Set premises via the canonical bridges, reuse
   the original lemma, rebuild Set-conclusions componentwise. No axioms, no
   Admitted, no new Prop statements. *)
(* Build: coqc -Q . "" after the batch-1 chain in the same world. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import PiCompareT.
Require Import PiKernelSlack.
Require Import PiVertexPolyDiff.
Require Import PiCosTailScan.
Require Import PiCosApproxRoot.

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



(* Set twin of vt_pow_half_arch_prop (Path A v2.4) *)
Lemma vt_pow_half_archT : forall (D eps : Q), QleT' 0 D -> QltT 0 eps ->
  sigT (fun n => QltT (D * q_pow (1#2) n) eps).
Proof.
  intros D eps HD Heps.
  apply QleT'_to_Qle in HD.
  apply QltT_to_Qlt in Heps.
  destruct (vt_pow_half_arch_prop D eps HD Heps) as [n Hn].
  exists n. apply Qlt_to_QltT. exact Hn.
Qed.

(* Set twin of approx_root_cos_prop (Path A v2.4): DEFERRED to the gap ledger
   as W-EXBLOCK. The original statement carries an inner Prop existential
   (exists N : nat, ...) whose informative bound cannot be eliminated into the
   Set-level sigT innard of the twin (no large elimination of Prop). A honest
   Set twin needs the original statement recast with a Set-side witness, which
   belongs to the source-statement wave, not to twin casting. *)



(* Set twin of vt_bisect_spec_prop (Path A v2.4): all Q-comparison premises
   and the And-chain innards are recast on QltT / QleT' / QeqT; the bisection
   function itself keeps its Qlt argument, fed by QltT_to_Qlt. *)
Lemma vt_bisect_specT : forall (n K : nat) (a b : Q) (Hab : QltT a b),
  QleT' 0 a -> QleT' b 2 -> NatLe 2 K ->
  QltT 0 (cos_partial K a) -> QleT' (cos_partial K b) 0 ->
  And (QleT' a (fst (vt_bisect K a b (QltT_to_Qlt a b Hab) n)))
      (And (QleT' (snd (vt_bisect K a b (QltT_to_Qlt a b Hab) n)) b)
      (And (QeqT ((b - a) * q_pow (1#2) n)
                (snd (vt_bisect K a b (QltT_to_Qlt a b Hab) n)
                 - fst (vt_bisect K a b (QltT_to_Qlt a b Hab) n)))
      (And (QltT 0 (cos_partial K (fst (vt_bisect K a b (QltT_to_Qlt a b Hab) n))))
           (QleT' (cos_partial K (snd (vt_bisect K a b (QltT_to_Qlt a b Hab) n))) 0)))).

Proof.
  intros n K a b Hab H0 H1 H2 H3 H4.
  set (Hab' := QltT_to_Qlt a b Hab) in *.
  assert (H0' : Qle 0 a) by (apply QleT'_to_Qle; exact H0).
  assert (H1' : Qle b 2) by (apply QleT'_to_Qle; exact H1).
  assert (H2' : (2 <= K)%nat) by (apply NatLe_drop; exact H2).
  destruct (vt_bisect_spec_prop n K a b Hab' H0' H1' H2' H3 H4)
    as [Ha [Hb [Heq [Hl Hr]]]].
  apply Qle_to_QleT' in Ha.
  apply Qle_to_QleT' in Hb.
  apply qeq_imp_qeqT in Heq.
  exact (pair Ha (pair Hb (pair Heq (pair Hl Hr)))).
Qed.

(* ==== Section 2. Extraction audit probe ==== *)

Print Assumptions vt_qpos_neqT.
Print Assumptions vt_pow_half_archT.
Print Assumptions vt_bisect_specT.
