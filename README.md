# Palomar candidate: sectorial asymptotics for centered Riemann-xi coefficients

This repository snapshot is the dedicated Palomar candidate for the analytic input used in John Savva's *A Two-Thirds Hyperbolicity Wedge for Jensen Polynomials of Riemann's Xi-Function*.

Permanent Version 1.1 paper record: https://doi.org/10.5281/zenodo.22293642

## Exact scope

The Comparator topic records three declarations:

1. the exact positive-integer identification of the centered-xi coefficient continuation;
2. the uniform three-sector saddle-point asymptotic used by manuscript Theorem 7.1; and
3. the proportional-disc derivative bounds through order six used by the interpolation residual.

This entry does **not** state or verify the final Jensen-polynomial hyperbolicity theorem. That theorem also consumes T1-T4 and the algebraic finite-free-convolution chain described in the paper and its technical supplement.

## Palomar paths

- Project path: repository root (leave the form field blank)
- Comparator configuration: `comparator/config-theorem-seven-one.json`
- Formalization metadata: `comparator/formalization.yaml`
- Challenge: `comparator/Challenge/TheoremSevenOne.lean`
- Solution: `comparator/Solution/TheoremSevenOne.lean`

The Challenge is 168 lines and imports Mathlib only. It contains deliberate `sorry` placeholders, as expected for Comparator's trusted statement surface. The Solution and production import cone are sorry-free. The permitted axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Local check

```bash
lake build Challenge.TheoremSevenOne Solution.TheoremSevenOne
lake env lean comparator/PrintAxioms/TheoremSevenOne.lean
```

The axiom command must report exactly the three permitted axioms for each compared declaration. Palomar independently runs Comparator, Lean-kernel replay and NanoDa; a local pass is not a Palomar result.

## Provenance and review status

The formal project began from the Apache-2.0 Zeta23 Lean development and includes the new Jensen-Theorem-7.1 production cone and Comparator topic. The original root README is retained as `ZETA23_BASE_README.md`; `NOTICE` and source attribution headers remain in place.

The papers and accompanying Lean formalization were developed with substantial AI assistance, primarily from OpenAI GPT-5.6 Sol Pro. Additional models assisted with adversarial testing and AI-only review. Wolfram Mathematica 15.0.1 was executed by the human maintainer for clean-room computational corroboration of selected identities. No human mathematical review or peer review is claimed.

Palomar is a registry of machine-checked Lean formalizations, not a journal, novelty assessment, or human peer review. Do not claim a Palomar result unless a version-specific registry entry exists.

## Licence

The submitted source snapshot is Apache-2.0; see `LICENSE` and `NOTICE`. Cited papers retain their own rights.
