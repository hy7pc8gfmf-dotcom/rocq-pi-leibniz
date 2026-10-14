# Changelog

All notable changes to this package are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
