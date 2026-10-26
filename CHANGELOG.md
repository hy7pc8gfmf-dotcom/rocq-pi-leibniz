# Changelog

All notable changes to this package are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.0.4] - 2026-10-26

### Added

- A Set-carried twin of the anti-diagonal band residue machine:
  `theories/Reals/Cauchy/PiPascalResidueT.v` restates the named
  statements of `PiPascalResidue` over `Set` carriers — each twin
  carries the same mathematical content with the reflected decision
  types (`QltT`/`QeqT`-based decidable predicates) in the place of the
  `Prop`-level faces — so the band representation of the truncation
  remainder is available in extractable form. The module is registered
  in `_CoqProject` and re-exported from the root module.
- Self-contained computational micro-proofs for the documented witness
  values: the window-family sample points (`lw0m_e 0 = 5 # 2`,
  `lw0m_e 1 = 5 # 4`, `lw0m_e 2 = 5 # 6`) and the margin component of
  the escape-witness triple (`lw0m_e 3 = 5 # 8`) are asserted as
  Set-carried Boolean identities (`Id (Qeq_bool _ _) true`) whose proof
  bodies close by `vm_compute` alone — no solver tactic and no transport
  through the bridges participates — each ending in `Defined` and
  assumption-free.

### Changed

- Statement names that carry a Set-carried twin are suffixed `_prop`
  across the package (681 names, counted over definitions, lemmas,
  theorems, and corollaries): a `Prop`-level statement and its
  `Set`-carried twin express the same mathematical content, but the two
  faces cannot share one name once both must be importable side by
  side; the `Prop`-level originals carry the suffix and the bare names
  remain reserved for the `Set`-carried faces, so downstream code
  states which face it consumes.
- The root module no longer re-exports `PiWindowCore` (`Require Export`
  lowered to `Require`): the bare name `leiblw_id_eq_prop` was declared
  with different types in `PiWindowCore` and `PiLeibnizMargin`, and
  downstream `Require Import pi_leibniz` users previously resolved it
  to whichever export came last; consumers now get the package's own
  `PiLeibnizMargin` face unambiguously, and code that needs the
  `PiWindowCore` face should `Require Import` that module directly.
- Library comments are in English throughout and normalized to the
  package comment policy (five-field module headers, no process
  narrative); residual process-language version stamps were cleared;
  statement-level migration provenance lives in
  [docs/statement-provenance.md](docs/statement-provenance.md)
  (coordinates frozen as recorded), leaving name-level citations in the
  library.
- Consumers migrated to the Set-carried twins: use sites across the
  package now reference the `Set`-carried faces directly, including the
  bisection, approx-root and Pascal-residue families; the twin blocks
  for the bisection and approx-root-arch statements moved next to their
  original statements, removing a reverse-require cycle.

### Removed

- Eight zero-reference `_prop` statement faces (full-tree residual
  grep: zero).

### Fixed

- `PiPascalResidueT` referenced statements beyond its declared
  dependencies; the missing module dependencies (`PiKernelSlack`,
  `PiPascalMachine`) are now imported and declared in the module
  header.
- `scripts/pi_ci_chk.sh` targeted statement names that the renaming had
  changed; the assumption smoke check now names
  `pi_leibniz_strong_irrational_prop`, in step with the renamed
  statements.

## [1.0.3] - 2026-10-25

### Added

- Set-carried twins of the order statement faces (path-A `Prop`
  ablation): `theories/Reals/Cauchy/PiKernelSlack.v` now carries 238
  twin faces restated over `Set` carriers — each twin restates the
  same mathematical content with the reflected decision types
  (`QltT`/`QleT'`/`QeqT`) in the place of the `Prop`-level order
  faces, is proved by transporting through the file's decision
  bridges, and leaves the original statements untouched.
- The window-equality cascade reshaped onto its `Set` twin: the 26
  faces of the `lw0_qpoly_eq` family (the pointwise definition, the
  24 cascade lemmas, and the two interchange bridges) now stand on
  the Set-carried `lw0_qpoly_eqT`, with the two bridges keeping the
  original form interchangeable.
- A unified carrier block in `theories/Reals/Cauchy/PiCompareT.v`:
  the remaining statement carriers (`And`, `NatLe`, `ZleT`, `ZltT`,
  `IffT`) and their double-sided reflection bridges moved alongside
  the canonical `QltT`/`QleT'` wrappers and the `Id` equality type,
  so every consumer module obtains its `Set`-level predicates from
  a single source.
- A Set-carried apartness counterpart,
  `theories/Reals/Cauchy/PiCRealAppartT.v`: `CRealLtT` mirrors the
  stdlib `CRealLt` with `QltT` in the place of the `Qlt` predicate,
  and `CReal_appartT` mirrors the stdlib `CReal_appart` sum;
  two-way bridges connect the two forms, which run in parallel.
- Four separation modules, registered in `_CoqProject` and
  re-exported from the root module: `PiSep361RefaceT`, `PiSepBNeq0T`,
  `PiSepMirrorT`, and `PiSepTriple227`.
- CI: the all-none `rocqchk -o` certification and the 4c
  witness-validity assertions on the documented sample points
  (`lw0m_e 0 = 5 # 2`, `lw0m_e 1 = 5 # 4`, `lw0m_e 2 = 5 # 6`;
  compile-fail on mismatch) now run over the extended closure, with
  the five new Set-carried modules included.
- Library comments normalized in three waves to the package comment
  policy: five-field module headers, no process narrative, and the
  statement-level migration provenance externalized to
  [docs/statement-provenance.md](docs/statement-provenance.md)
  (coordinates frozen as recorded), leaving name-level citations in
  the library.

## [1.0.2] - 2026-10-24

### Added

- CI: the smoke check now asserts the documented witness values — the
  window family must evaluate to `e 0 = 5 # 2`, `e 1 = 5 # 4`,
  `e 2 = 5 # 6` (compile-fail on mismatch), alongside the assumption
  smoke check on the two main theorems.

## [1.0.1] - 2026-10-24

### Added

- Three new modules in the pi supply chain under
  `theories/Reals/Cauchy/`: `PiLeibnizMargin` (the unbounded-margin
  statement for the Leibniz window family), `PiPadeQLeg` (the
  rational-level Padé leg), and `PiSepSearch` (generic separation
  search), registered in `_CoqProject` and re-exported from the root
  module `theories/PiLeibniz.v`.
- CI: the workflow is now a single self-hosted job that seeds the trust
  cache from the pinned local clone (build is a skip pass over the
  cache), certifies the whole dependency closure with `rocqchk -o`, and
  runs the assumption smoke check on the two main theorems; every
  compilation step is wrapped in the machine's cpu guard.

## [1.0.0] - 2026-10-15

### Added

- Initial release: a constructive pi for the Rocq constructive Cauchy
  reals (`pi_leibniz`), realized by the alternating Leibniz series, with
  the premise-free strong irrationality separation theorem
  `pi_leibniz_strong_irrational` and its premise-free companion
  `pi_leibniz_appart_all_Q` (`theories/Reals/Cauchy/PiSeparation.v`).
- The 24-file pi supply chain (five-file core plus nineteen-file supply
  layer, about 35,100 lines) and the escape-window engine file
  `theories/Reals/Cauchy/ConstructiveCauchyRealsSep.v` (221 lines) that
  the core builds on: 25 content modules, 35,287 lines.  All content
  modules are carried verbatim from the submitted state (head `841855c`)
  of the Rocq standard-library proposal (PR #316, stacked on #313); no
  proof content was modified.
- Packaging scaffolding: `opam` package (`rocq-prover`/`rocq-stdlib`
  >= 9.1), `_CoqProject`/`Makefile` build via `rocq makefile`
  (`coq_makefile` fallback), root convenience module
  `theories/PiLeibniz.v` (re-export only; no statements, no proofs),
  README, and the LGPL-2.1 license text.
