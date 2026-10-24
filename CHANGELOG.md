# Changelog

All notable changes to this package are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
