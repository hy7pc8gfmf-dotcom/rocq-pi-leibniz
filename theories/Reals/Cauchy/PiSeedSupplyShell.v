(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)
(** * PiSeedSupplyShell: the supply assembly shell for the three seed
      slots of the double-index synthesis bundle.

    Mission.  It makes the three slot supply faces (the half-window
    pair / the double-angle sin residual / the double-angle cos
    residual) available under explicit names and certifies the V1/V2
    consumption wiring (with the supplies fed into the slot forms, the
    conclusions close with zero adaptation).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [Arith.PeanoNat]; [PiCompareT]; [PiKernelSlack] (the merged
    identity segment carrying the premise bundles); [PiLeibnizCReal];
    [PiCosBandAssemble]; [PiHalfwinSeed].

    References.  [PiKernelSlack] (the three slots of the synthesis
    bundle and the two main vanishing forms); the mathematical content
    is the partial-sum stratified truncation-residual vanishing of
    [sin2x = 2 sin x cos x] and [cos2x = cos^2 x - sin^2 x] (the
    double-index uniform forms).

    Constructivity.  [Set]-level statements (conclusions
    [QltT]/[sigT]; premises [QltT]/[QleT']/[Qeq]); assumption-free,
    no admits.

    Build.  [coqc -native-compiler no -q -Q . "" PiSeedSupplyShell.v]
    compiles cleanly (exit 0); the first eight bytes of the artifact
    are [436f7121 00015ff4].

    This file is part of the rocq-pi-leibniz package; its interface
    may change in future releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.PeanoNat.
Require Import PiCompareT.
Require Import PiKernelSlack.
Require Import PiLeibnizCReal.
(* Supply module lines: the two truncation-residual seed theorems
   [piLe_seed_dres_prop]/[piLe_seed_dcos_prop] live in [PiCosBandAssemble];
   the half-window pair seed theorem [piLh_seed_halfwin_prop] lives in
   [PiHalfwinSeed]. *)
Require Import PiCosBandAssemble.
Require Import PiHalfwinSeed.
(* Topology note: in this tree the identity premise bundles and the
   synthesis segment are carried by the merged PiKernelSlack segment;
   the slot definitions piLd3_seed_* and the V1/V2 vanishing forms
   (piL_sin_xL_vanish_prop/piL_cos_xL_neg1_vanish_prop) are supplied by the
   Requires above. *)

(* ==== Section 1. The three supplies, stated verbatim ==== *)

(* The sigma-1 half-window pair supply face: |C_k(2*lp_odd m)| -> 0 and
   |S_k(2*lp_odd m) - 1| -> 0, uniform in both indices. *)
Definition piLsup_halfwin : Set := piLd3_seed_halfwin.

(* The sigma-2 supply face: the sin double-angle truncation residual vanishes uniformly for |x| <=
   B.  *)
Definition piLsup_dres : Set := piLd3_seed_dres.

(* The sigma-3 supply face: the cos double-angle truncation residual vanishes uniformly for |x| <=
   B.  *)
Definition piLsup_dcos : Set := piLd3_seed_dcos.

(* ==== Section 1.5. Loading the three supplies with checked type ascriptions ==== *)

(* Loading: the three slots are supplied under pinned names --
   sigma-1 [piLh_seed_halfwin_prop] ([PiHalfwinSeed]); sigma-2
   [piLe_seed_dres_prop] and sigma-3 [piLe_seed_dcos_prop] ([PiCosBandAssemble]).
   The three ascriptions match the slot types [piLd3_seed_*] verbatim,
   so the supplies load with zero adaptation. *)
Definition piLsup_halfwin_supply : piLsup_halfwin := piLh_seed_halfwin_prop.
Definition piLsup_dres_supply : piLsup_dres := piLe_seed_dres_prop.
Definition piLsup_dcos_supply : piLsup_dcos := piLe_seed_dcos_prop.

(* ==== Section 2. The vertex anchor premise (open companion of the sigma-1 supply) ==== *)

(* The anchor face is the sigma-1 face with the k-lower-bound half removed:
   at the window half-points 2*lp_odd m the sin/cos partial sums vanish
   doubly for every truncation depth k, uniformly in m only.  The
   k-uniform half is carried by the partial-sum uniform Cauchy machine
   (the tail-sum machine of the identity premise bundle); this face is
   the one statement left open here. *)
Definition piLsup_vertex_anchor : Set :=
  forall dt : Q, QltT 0 dt ->
    sigT (fun N : nat => forall k m : nat, (N <= m)%nat ->
      And (QltT (Qabs (cos_partial k (2 * lp_odd m))) dt)
          (QltT (Qabs (sin_partial k (2 * lp_odd m) - (1 # 1)%Q)) dt)).

(* A resolution of the anchor face implies the sigma-1 supply face (glue: take K := N). *)
Theorem piLsup_halfwin_of_anchor_prop :
  piLsup_vertex_anchor -> piLsup_halfwin.
Proof.
  intros Hanchor dt Hdt.
  destruct (Hanchor dt Hdt) as [N HN].
  exists N. intros k m Hk Hm. exact (HN k m Hm).
Qed.

(* ==== Section 3. Direct use of the sigma-2 and sigma-3 supplies ==== *)

(* With the sigma-2 supply resolved, the V1 conclusion form holds (fed directly, zero adaptation). 
      *)
Theorem piLsup_sin_vanish_of_sup :
  piLsup_halfwin -> piLsup_dres ->
  forall dt : Q, QltT 0 dt ->
    sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
      QltT (Qabs (sin_partial m (lw0m_xL m))) dt).
Proof.
  intros H1 H2 dt Hdt.
  exact (piL_sin_xL_vanish_prop H1 H2 dt Hdt).
Qed.

(* With the sigma-3 supply resolved, the V2 conclusion form holds (fed directly, zero adaptation). 
      *)
Theorem piLsup_cos_vanish_of_sup :
  piLsup_halfwin -> piLsup_dcos ->
  forall dt : Q, QltT 0 dt ->
    sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
      QltT (Qabs (cos_partial m (lw0m_xL m) + (1 # 1)%Q)) dt).
Proof.
  intros H1 H3 dt Hdt.
  exact (piL_cos_xL_neg1_vanish_prop H1 H3 dt Hdt).
Qed.

(* ==== Section 4. Final assembly with the three supplies as explicit premises ==== *)

(* With the three supplies at hand, the conjunction of the sin/cos double
   vanishing follows (the two positive identity forms wired in one step);
   with each premise replaced by its supply theorem, the statement closes
   with no assumptions. *)
Theorem piLsup_seedfree_xL_vanish_carry :
  forall (H1 : piLsup_halfwin) (H2 : piLsup_dres) (H3 : piLsup_dcos)
         (dt : Q), QltT 0 dt ->
    And (sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
                QltT (Qabs (sin_partial m (lw0m_xL m))) dt))
        (sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
                QltT (Qabs (cos_partial m (lw0m_xL m) + (1 # 1)%Q)) dt)).
Proof.
  intros H1 H2 H3 dt Hdt. split.
  - exact (piLsup_sin_vanish_of_sup H1 H2 dt Hdt).
  - exact (piLsup_cos_vanish_of_sup H1 H3 dt Hdt).
Qed.

(* ==== Section 5. The final vanishing-conjunction form ==== *)

Theorem piLsup_seedfree_xL_vanish :
  forall dt : Q, QltT 0 dt ->
    And (sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
                QltT (Qabs (sin_partial m (lw0m_xL m))) dt))
        (sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
                QltT (Qabs (cos_partial m (lw0m_xL m) + (1 # 1)%Q)) dt)).
Proof.
  exact (piLsup_seedfree_xL_vanish_carry
         piLsup_halfwin_supply piLsup_dres_supply piLsup_dcos_supply).
Qed.
