(* rocq-pi-leibniz — constructive pi for the Rocq constructive Cauchy reals. Released under LGPL-2.1; see LICENSE. *)

(** * PiLeibniz: root module of the [rocq-pi-leibniz] package.

    Mission.  Release packaging scaffolding: a convenience re-export
    of the whole development in one import.  The file states no
    theorem, defines nothing, and proves nothing; importing
    [PiLeibniz] makes every name of every content module available.

    Dependencies.  All content modules of the package, re-exported:
    [ConstructiveCauchyRealsSep], [PiArctanFixedQ], [PiBandBound],
    [PiCompareT], [PiCRealAppartT], [PiCosApproxRoot],
    [PiCosApproxRootSet],
    [PiCosBandAssemble], [PiCosPartialSeqCauchy], [PiCosTailScan],
    [PiCosZeroSeqConv], [PiCosZeroSeqProbe], [PiExpArch],
    [PiExpTrigSeries], [PiHalfwinSeed], [PiKernelSlack],
    [PiLeibnizCReal], [PiLeibnizMargin], [PiPadeQLeg],
    [PiPascalMachine], [PiPascalResidue], [PiPythBandDonor],
    [PiRowIdentity], [PiSeedSupplyShell], [PiSep361RefaceT],
    [PiSepBNeq0T], [PiSepMirrorT], [PiSepSearch],
    [PiSepTriple227], [PiSeparation], [PiVertexPolyDiff],
    [PiWindowCore],
    [QCauchyZeroCos].

    References.  The repository README (Position, Provenance): the
    content modules are carried verbatim from the submitted state
    (head [841855c]) of the Rocq standard-library proposal "Add a
    constructive pi for the constructive Cauchy reals with a strong
    irrationality separation theorem" (upstream PR #316).

    Constructivity.  No statement is made in this file; the guarantee
    face is inherited from the re-exported modules (premise-free main
    theorems, assumption-free by [coqchk]).

    Build.  [coqc -native-compiler no -q -Q . "" PiLeibniz.v]
    compiles cleanly (exit 0); the first eight bytes of the artifact
    are [436f7121 00015ff4].

    This file is part of the rocq-pi-leibniz package; its interface
    may change in future releases. *)

Require Export ConstructiveCauchyRealsSep.
Require Export PiArctanFixedQ.
Require Export PiBandBound.
Require Export PiCompareT.
Require Export PiCosApproxRoot.
Require Export PiCosApproxRootSet.
Require Export PiCosBandAssemble.
Require Export PiCosPartialSeqCauchy.
Require Export PiCosTailScan.
Require Export PiCosZeroSeqConv.
Require Export PiCosZeroSeqProbe.
Require Export PiExpArch.
Require Export PiExpTrigSeries.
Require Export PiHalfwinSeed.
Require Export PiKernelSlack.
Require Export PiLeibnizCReal.
Require Export PiPascalMachine.
Require Export PiPascalResidue.
Require Export PiPascalResidueT.
Require Export PiPythBandDonor.
Require Export PiRowIdentity.
Require Export PiSeedSupplyShell.
Require Export PiSeparation.
Require Export PiVertexPolyDiff.
Require PiWindowCore.
Require Export QCauchyZeroCos.
Require Export twin46_b23a.
Require Export wall2_apart.
Require Export wall2_exblock.
Require Export wall2_parity.
Require Export PiLeibnizMargin.
Require Export PiPadeQLeg.
Require Export PiSepSearch.
Require Export PiCRealAppartT.
Require Export PiSep361RefaceT.
Require Export PiSepBNeq0T.
Require Export PiSepMirrorT.
Require Export PiSepTriple227.
Require Export PiMu0Cos.
Require Export Sqrt2UniformStrongIrrational.
