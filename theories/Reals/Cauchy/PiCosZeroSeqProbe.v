(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)

(** * The consumption-side certificate of the cosine zero sequence

    Mission.  The consumption-side certificate for the cosine zero
    sequence [cos_zero_seq]: with the half-power step
    [eps_n = (1/2)^(n+1)] as the tolerance, the n-th zero is taken
    from the [sig] witness of the main existence theorem for the
    zeros of the cosine ([PiCosApproxRoot.approx_root_cos_prop]).  The
    definition face is verbatim the same shape as the [Q]-level form
    of [cos_zero_seq] in [S10_KVQuantTrig.v] ([proj1_sig] taken
    directly).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs];
    [QCauchyZeroCos] ([log_eps]/[log_eps_posT]);
    [PiCosApproxRoot] ([approx_root_cos_prop]).

    References.  [S10_KVQuantTrig.v] (the [Q]-level form of
    [cos_zero_seq]).

    Constructivity.  Statements carried at the [Set] level (with
    [Q] as the carrier); assumption-free and fully proved, with no
    non-constructive principles.

    Build.  [coqc -native-compiler no -q -Q . "" PiCosZeroSeqProbe.v]
    (Rocq 9.1.0).

    This file is part of the rocq-pi-leibniz package; its interface
    may change in future releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import QCauchyZeroCos.
Require Import PiCosApproxRoot.

(** The n-th term of the zero sequence: the localization point with
    tolerance [eps_n] (taken directly from the [sig] witness). *)
Definition cos_zero_seq (n : nat) : Q :=
  proj1_sig (approx_root_cos_prop (log_eps n) (log_eps_pos_prop n)).

Print Assumptions cos_zero_seq.
