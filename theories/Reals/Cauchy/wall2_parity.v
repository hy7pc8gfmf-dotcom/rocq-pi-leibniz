(* ===================================================================== *)
(* Module.  wall2_parity.v                                               *)
(*                                                                       *)
(* Mission.  Set-carried twin of the natural-number parity split: every  *)
(*   nat is even or odd, with explicit witnesses, stated over the        *)
(*   Set-level sum and the boolean equality decision [NatEqT].  This     *)
(*   recasts [PiVertexPolyDiff.v vt_parity_prop], whose original face    *)
(*   was a Prop disjunction of Prop existentials.                        *)
(*                                                                       *)
(* Dependencies.  PiCompareT (Id, NatLe), PiWindowCore (Id-bool          *)
(*   bridges), Stdlib PeanoNat.                                          *)
(*                                                                       *)
(* References.  PiVertexPolyDiff.v vt_parity_prop; its consumer          *)
(*   sc_P_ge_P2_prop.                                                    *)
(*                                                                       *)
(* Constructivity.  Statement is Set-carried throughout (sum of sigT     *)
(*   with NatEqT faces); no axioms, no Admitted.  The arithmetic step    *)
(*   is a pure rewriting chain over [Nat.add_succ_r] and                *)
(*   [Nat.mul_succ_r]; no tactic solver closes any goal.                 *)
(*                                                                       *)
(* Build.  coqc -Q . "" wall2_parity.v  (born-in-place, Rocq 9.1)        *)
(* ===================================================================== *)

From Stdlib Require Import Arith.PeanoNat.
Require Import PiCompareT PiWindowCore.

(* The Set-level boolean equality decision on [nat], with both bridge
   directions against the propositional equality. *)

Definition NatEqT (n m : nat) : Set := Id (Nat.eqb n m) true.

Lemma nat_eq_NatEqT : forall n m : nat, n = m -> NatEqT n m.
Proof.
  intros n m H.
  apply (leiblw_id_eq_prop (Nat.eqb n m)).
  apply (proj2 (Nat.eqb_eq n m)). exact H.
Qed.

Lemma NatEqT_eq : forall n m : nat, NatEqT n m -> n = m.
Proof.
  intros n m H.
  apply (proj1 (Nat.eqb_eq n m)).
  apply (leiblw_id_inv_prop). exact H.
Qed.

(* Set-carried parity split.  Matches the mathematical content of
   vt_parity_prop: (exists m, n = 2*m) or (exists m, n = 2*m + 1),
   with the disjunction carried by [sum] and each equation carried by
   [NatEqT]. *)

Lemma vt_parityT : forall n : nat,
  sum (sigT (fun m : nat => NatEqT n (2 * m)))
      (sigT (fun m : nat => NatEqT n (2 * m + 1))).
Proof.
  intro n. induction n as [| n IH].
  - left. exists 0%nat. apply nat_eq_NatEqT. reflexivity.
  - destruct IH as [[m Hm] | [m Hm]].
    + (* n = 2*m gives S n = 2*m + 1 *)
      right. exists m. apply nat_eq_NatEqT.
      apply NatEqT_eq in Hm. rewrite Hm.
      repeat rewrite Nat.add_succ_r.
      rewrite Nat.add_0_r. reflexivity.
    + (* n = 2*m+1 gives S n = 2 * S m *)
      left. exists (S m). apply nat_eq_NatEqT.
      apply NatEqT_eq in Hm. rewrite Hm.
      rewrite Nat.mul_succ_r.
      repeat rewrite Nat.add_succ_r.
      rewrite Nat.add_0_r. reflexivity.
Qed.

Print Assumptions vt_parityT.
Print Assumptions nat_eq_NatEqT.
Print Assumptions NatEqT_eq.
