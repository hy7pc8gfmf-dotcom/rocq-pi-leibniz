# rocq-pi-leibniz

[![CI](https://github.com/hy7pc8gfmf-dotcom/rocq-pi-leibniz/actions/workflows/ci.yml/badge.svg)](https://github.com/hy7pc8gfmf-dotcom/rocq-pi-leibniz/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23527294.svg)](https://zenodo.org/doi/10.5281/zenodo.23527294)

Constructive pi for the Rocq constructive Cauchy reals — premise-free
separation from every rational with extractable witnesses.

A constructive pi for the constructive Cauchy reals of the Rocq standard
library (`ConstructiveCauchyReals`), realized by the alternating Leibniz
series, with the strong irrationality separation theorem

```coq
Theorem pi_leibniz_strong_irrational_prop :
  forall a b : Q, b <> 0 -> CReal_appart pi_leibniz (inject_Q (a / b)).
```

together with its premise-free companion

```coq
Theorem pi_leibniz_appart_all_Q :
  forall q : Q, CReal_appart pi_leibniz (inject_Q q).
```

As of v1.0.4, a statement name that carries a `Set`-carried twin is
suffixed `_prop` (`pi_leibniz_strong_irrational_prop`); the `Prop`-level
originals carry the suffix and the bare names remain reserved for the
`Set`-carried statements, so a name without a twin, such as
`pi_leibniz_appart_all_Q`, keeps its bare form.

pi is apart, in the sense of `CReal_appart`, from every embedded rational
constant, and the apartness witness comes with an explicit positive margin
and an explicit convergence modulus for the realizer.  The abstract
escape-window criterion (a concrete constructive real is apart from every
rational once it carries a family of positive window widths decaying
slower than the resolution `2 * 2^(-n)` of `CReal`) is reused unchanged;
this development supplies the pi-specific window family at the purely
rational level, converts it into a `CReal` modulus, and loads the engine,
so that the main theorems follow from `creal_escape_window_apart` with no
further analytic input.  For the antecedent device — computing pi from
alternating series with easy error bounds — see O'Connor 2008 and
Krebbers and Spitters 2013, in the tradition of exact real arithmetic.

## Position

To the best of our knowledge, this package is the first formalization in
any proof-assistant library of a constructive, premise-free separation
of pi from every rational number: both main theorems hold without
excluded middle or any other non-constructive principle, and each
apartness statement produces an explicit, extractable, and runnable
witness (a positive margin and a convergence modulus, per rational).
The closest formalized relatives are classical: mathlib's
`Real.irrational_pi` and Eberl's Niven-style proof of the irrationality
of pi in the Archive of Formal Proofs both establish the irrationality
by classical reasoning and carry no computational witnesses.  Search
window and caveats for the first-of-its-kind claim are recorded under
*Prior work* below.

## Convergence rate

The Leibniz realization is chosen for proof-theoretic transparency, not
for speed, and this should be stated plainly.  The alternating series
`pi/4 = 1 - 1/3 + 1/5 - 1/7 + ...` has a remainder bounded by the first
omitted term, about `1/n` after `n` terms, so obtaining `d` correct
decimal digits takes on the order of `10^d` terms — exponentially many
terms in the number of digits.  None of the theorems are affected: the
apartness statements carry an explicit positive margin and an explicit
convergence modulus, so they hold at any requested precision, but
evaluating the witnesses at high precision by these series is
prohibitively slow.  This mirrors the classical exact-real-arithmetic
tradition the development builds on (O'Connor 2008; Krebbers and
Spitters 2013), in which Leibniz-type series serve as correctness
baselines while fast-converging series drive the actual computation.
A fast-converging variant of this development is on the roadmap
(see *Roadmap* below).  The cost of evaluating the witnesses of the main
theorems is entered in the package's exception register (its first
performance case; registration accepted): the exponential term count
above stands as the recorded order-of-magnitude qualification, with the
fast-converging variant on the roadmap as the registered improvement
path.

## Guarantees

- **Premise-free.**  Both main theorems are stated with no section
  variables and no hypotheses beyond the rational `q` itself.  The one
  registered antecedent, `b <> 0` in `pi_leibniz_strong_irrational_prop`,
  is zero-consumption: the proof discards it, the content rests on the
  premise-free companion `pi_leibniz_appart_all_Q`, and it serves only
  as the semantic guard of the notion of a rational number (header
  note in `PiSeparation`).  It is entered in the exception register as
  a backfill line for a statement face already on disk (red-line law
  v2.4 freezes the register — no new entries).  Its Set-carried
  re-facing is recorded in machine-checked form in `PiSep361RefaceT`:
  the Leibniz face admits no transport into the `Qeq` face
  (`leibniz_qeq_transport_blocked`, counterexample `0 # 2`), and the
  chain is one-way, from `~ (b == 0)` to `Qneq0T b` to `b <> 0`
  (`qeq_face_to_leibniz_face`).
- **Zero axioms.**  `Print Assumptions pi_leibniz_strong_irrational_prop` and
  `Print Assumptions pi_leibniz_appart_all_Q` report *Closed under the
  global context*; the same holds for the main statements of every
  supply-layer file.  `coqchk -o` over the whole dependency closure:
  *Modules were successfully checked*, assumption context summary
  all-none.
- **Extractable witnesses.**  Statement faces are Set-carried: the
  sigma witnesses and the apartness sum are `Set`-valued, and the
  kernel-slack restatement file carries 238 Set-carried twin faces of
  its order statements (`QltT`/`QleT'`/`QeqT` reflected decisions in
  the place of the `Prop`-level faces), each proved by transport
  through the decision bridges.  The canonical `QltT`-based carriers
  are unified in `PiCompareT` — `QltT`, `QleT'`, the `Id` equality
  type, and the `And`/`NatLe`/`ZleT`/`ZltT`/`IffT` carrier block,
  obtained from that single source by every consumer module — and the
  scheduled `QltT`-based Set-carrier rewrite of the registered
  `CRealLt` mirror is now in place: `CRealLtT` and `CReal_appartT`
  (in `PiCRealAppartT`) mirror the stdlib originals and run in
  parallel with them over two-way bridges, the main theorems remaining
  on the stdlib face pending the full Set replacement.  Legacy
  supply-layer helper lemmas stated over `Prop` are being restated
  over Set carriers wave by wave (red-line law v2.4: the exception
  register is frozen — no new entries, existing ones sunset on a
  fixed schedule); the kernel-slack twin ablation and the 26-face
  window-equality cascade, reshaped onto its `Set` twin
  `lw0_qpoly_eqT`, are complete.  Proof-internal `Prop` is erased at
  extraction: the extracted OCaml carries zero `Obj.magic` and zero
  statement-name loss.
- **Runnable witnesses.**  Sample-point probes run in the REPL with
  `vm_compute`: the window family evaluates to `e 0 = 5 # 2`,
  `e 1 = 5 # 4`, `e 2 = 5 # 6`, and the escape-witness triple for
  `q = 22 # 7` computes to `(22 # 7, 5 # 8, 3%nat) : Q * Q * nat`
  (explicit margin `5 # 8`, threshold index `3`).
- **Explicit proofs.**  Every witness is explicitly constructed; the
  proofs are explicit chains of rational-order lemmas; no automation
  tactic closes the main statements (`lia` appears only in small integer
  and rational literal bookkeeping steps, as in the engine file).
- **Verified.**  This package has its own CI (a single self-hosted job
  on the maintainers' machine, Rocq 9.1 line): it seeds the trust cache
  from the local clone, certifies the whole dependency closure with
  `rocqchk -o` (all-none assumption summary), and runs an assumption
  smoke check on the two main theorems plus witness-value assertions on
  the documented sample points — currently green (badge above).
  The content modules also compiled green across the CI matrix of the
  hosting standard-library submission (Alpine build and Rocq 9.2 / 9.3
  / master Nix bundles; 180/180 checks passed at the submitted head).

## Requirements

- [Rocq](https://rocq-prover.org) >= 9.1 with the standard library
  (`rocq-stdlib`), which provides `ConstructiveCauchyReals` and the
  other `Stdlib` modules the development builds on.

## Build and install

From a Rocq 9.1+ opam switch, in the repository root:

```sh
opam pin add rocq-pi-leibniz . -y
# or, since the directory name matches the package name:
opam install .
```

The build regenerates `Makefile.coq` from `_CoqProject` (via
`rocq makefile`, with a `coq_makefile` fallback) and delegates every
target to it.

## Usage

```coq
From Stdlib Require Import QArith.QArith.
From pi_leibniz Require Import PiLeibniz.

Check pi_leibniz_appart_all_Q.
(* : forall q : Q, CReal_appart pi_leibniz (inject_Q q) *)
```

Individual modules can be imported directly, e.g.

```coq
Require Import PiSeparation.
```

(The content modules carry the bare logical names they were submitted
with — `PiSeparation`, `PiKernelSlack`, … — so they are imported by
short name; only the root re-export module lives under the `pi_leibniz`
prefix.)

## Content map

Three layers, all under `theories/Reals/Cauchy/`:

- **Core (5 files).**  `PiCompareT` (the `Set`-valued identity type and
  the strict-order pair), `PiWindowCore` (the window machinery),
  `PiLeibnizCReal` (`pi_leibniz` as a `CReal` with its convergence
  modulus), `PiKernelSlack` (the per-rational escape-witness machine:
  for every rational `q` an explicit positive margin and a threshold
  index, uniform in `q`), `PiSeparation` (the two main theorems: the
  engine's conclusion applied verbatim, zero new proofs).
- **Supply layer (19 files).**  Standalone rational-level (`Q`)
  arithmetic feeding the core's seed slots so that the main theorems are
  stated premise-free: the geometric route via the zeros of the cosine
  over `Q` (`QCauchyZeroCos`, `PiCosZeroSeqProbe`, `PiCosTailScan`,
  `PiCosApproxRoot`, `PiCosApproxRootSet`, `PiCosZeroSeqConv`,
  `PiCosPartialSeqCauchy`, `PiExpTrigSeries`, `PiExpArch`), the arctan
  fixed-point machine and band bounds (`PiArctanFixedQ`, `PiBandBound`,
  `PiCosBandAssemble`, `PiPythBandDonor`), the combinatorial machines
  behind the double-angle stratification `sin(2x) = 2 sin x cos x`
  (`PiPascalMachine`, `PiRowIdentity`, `PiPascalResidue`), the polynomial
  difference bound (`PiVertexPolyDiff`), and the seed closure
  (`PiHalfwinSeed`, `PiSeedSupplyShell`).
- **Engine file (1 file).**  `ConstructiveCauchyRealsSep` — the abstract
  escape-window engine for the constructive Cauchy reals
  (`creal_escape_window`, `creal_escape_window_apart`), reused unchanged.

- **v1.0.1 additions (3 files).**  `PiLeibnizMargin` (the
  unbounded-margin statement for the Leibniz window family),
  `PiPadeQLeg` (the rational-level Padé leg, groundwork for accelerated
  variants), and `PiSepSearch` (generic separation search, groundwork
  for the approximation interface).

- **v1.0.3 additions (5 files).**  `PiCRealAppartT` (the `Set`-carried
  apartness counterpart: `CRealLtT`/`CReal_appartT` mirroring the
  stdlib `CRealLt`/`CReal_appart` over the `QltT` carrier, with two-way
  bridges), `PiSepBNeq0T` (a `Set`-carried nonzero premise for the
  strong irrationality theorem), `PiSep361RefaceT` (the re-faced
  premise of `pi_leibniz_strong_irrational_prop` registered in
  machine-checked form), `PiSepMirrorT` (the closing theorems re-faced
  to the `Set`-carried apartness twin), and `PiSepTriple227`
  (witness-value assertions for the documented escape triple at
  `22 # 7`).

- **v1.0.4 additions (1 file).**  `PiPascalResidueT` (Set-carried
  twins of the anti-diagonal band residue statements of
  `PiPascalResidue`, over the `QltT`/`QeqT` carriers).

Counting: 33 pi-stack files (about 47,300 lines) plus the 230-line engine
file they build on = 34 content modules, about 47,600 lines.
`theories/PiLeibniz.v` is release scaffolding: a root re-export module
that states no theorem and defines nothing.

## Provenance

The content modules are carried verbatim from the submitted state (head
`841855c`) of the Rocq standard-library proposal *Add a constructive pi
for the constructive Cauchy reals with a strong irrationality separation
theorem* (PR #316, stacked on #313; both part of one independent
constructive-formalization campaign), with one exception: the two
`Abbreviation` declarations in `PiKernelSlack.v` (`qpoly`, `S973`) are
restated as the equivalent `Notation` declarations, because the
`Abbreviation` vernac does not exist in Rocq 9.1 and this package keeps
the 9.1 line as its compatibility floor.  No proof content is affected.
The packaging scaffolding (opam file, build files, README, package
layout) is new.

Statement-level migration provenance (per-statement source coordinates,
frozen as recorded) is maintained in
[docs/statement-provenance.md](docs/statement-provenance.md); citations
inside the library are by fully qualified name.

## Prior work

As far as we know, no constructive formalization of the irrationality of
pi in the apartness sense, with explicit witnesses, exists (search
window: public web and the main proof-assistant libraries, checked
2026-10-09); the closest formalized relatives are classical
(Bernard–Bertot–Rideau–Strub's Coq transcendence proofs; Eberl's Niven
proof in the AFP; mathlib's `irrational_pi`).  The method family —
alternating series with decreasing terms giving an easy error bound and
a fast-converging sequence computing pi in Coq's exact real arithmetic —
is due to O'Connor (TYPES 2007) and Krebbers–Spitters (LMCS 2013,
arXiv:1105.2751); that line targets efficient computation and carries no
apartness statements and no per-rational witnesses, which are the
increment claimed here.  At the purely classical level, quantitative
separations of pi from rationals go back to Mahler's effective
irrationality measure (Indagationes Mathematicae 15, 1953, pp. 30–42,
`|pi - p/q| > q^-42`); the witnesses supplied here are elementary at the
rational level, do not assume any irrationality measure, and are
extracted as running OCaml with zero `Obj.magic`.

## Roadmap

- **v1.1 — cosine on `CReal` and window uniqueness.**  A constructive
  cosine for the constructive Cauchy reals (power series with explicit
  convergence moduli), unlocking the uniqueness statement that the pi
  window `(3/2, 7/2)` contains a unique zero of the cosine.
- **v1.2 — e instance.**  The same premise-free apartness treatment,
  with explicit extractable witnesses, applied to Euler's number e.
- **v2.0 — fast pi.**  A fast-converging realization of the same
  separation theorems, in the O'Connor / Krebbers–Spitters
  exact-real-arithmetic line, so that witness evaluation at high
  precision becomes practical; the Leibniz realization remains the
  compatibility floor.

Planned items are subject to change.

## License

[LGPL-2.1](LICENSE); every content module carries the standard Rocq
license header referring to the GNU Lesser General Public License
Version 2.1.
