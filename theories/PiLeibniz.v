(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * PiLeibniz: root module of the [rocq-pi-leibniz] package.

    Convenience re-export of the whole development in one import.
    This file is release packaging scaffolding: it states no theorem,
    defines nothing, and proves nothing.  Every content module is
    carried verbatim from the submitted state (head [841855c]) of the
    Rocq standard-library proposal; see the repository README for the
    provenance account. *)

From pi_leibniz Require Export ConstructiveCauchyRealsSep.
From pi_leibniz Require Export PiArctanFixedQ.
From pi_leibniz Require Export PiBandBound.
From pi_leibniz Require Export PiCompareT.
From pi_leibniz Require Export PiCosApproxRoot.
From pi_leibniz Require Export PiCosApproxRootSet.
From pi_leibniz Require Export PiCosBandAssemble.
From pi_leibniz Require Export PiCosPartialSeqCauchy.
From pi_leibniz Require Export PiCosTailScan.
From pi_leibniz Require Export PiCosZeroSeqConv.
From pi_leibniz Require Export PiCosZeroSeqProbe.
From pi_leibniz Require Export PiExpArch.
From pi_leibniz Require Export PiExpTrigSeries.
From pi_leibniz Require Export PiHalfwinSeed.
From pi_leibniz Require Export PiKernelSlack.
From pi_leibniz Require Export PiLeibnizCReal.
From pi_leibniz Require Export PiPascalMachine.
From pi_leibniz Require Export PiPascalResidue.
From pi_leibniz Require Export PiPythBandDonor.
From pi_leibniz Require Export PiRowIdentity.
From pi_leibniz Require Export PiSeedSupplyShell.
From pi_leibniz Require Export PiSeparation.
From pi_leibniz Require Export PiVertexPolyDiff.
From pi_leibniz Require Export PiWindowCore.
From pi_leibniz Require Export QCauchyZeroCos.
