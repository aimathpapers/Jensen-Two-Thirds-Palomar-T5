# Palomar topic: manuscript Theorem 7.1 (T5)

This topic exposes the analytic coefficient theorem through a deliberately
small trusted surface. It is a topic inside the substantive `Zeta23` Lean
project, not a thin wrapper around a separate repository.

## What is compared

`Challenge/TheoremSevenOne.lean` imports only Mathlib and defines, in
ordinary formulas:

- Riemann's theta tail and its Mellin moment;
- the Gamma quotient and the exact complex centered-xi coefficient;
- the saddle equation, curvature, displayed coefficient main;
- the `1/100` proof, `1/200` outer, and `1/400` inner sectors; and
- the proportional Cauchy radius `x/1000`.

The same file then states three results with deliberate `sorry` holes: exact
agreement of the continuation with the actual centered-xi coefficient at
positive integers, the literal three-sector coefficient asymptotic, and the
derivative estimates through order six. Palomar does not allow the trusted challenge to import a
candidate-local helper module, so the Mathlib-only definition block is
embedded directly in the challenge and repeated byte-for-byte in
`Solution/TheoremSevenOne.lean`. The solution proves the statements by a
definition-level bridge to the production Phase-28 theorem. Comparator,
rather than a source-code diff, is responsible for checking that the two
exported theorem types are identical.

## Local checks

From this Lean project directory:

```bash
lake build Challenge.TheoremSevenOne Solution.TheoremSevenOne
lake env lean comparator/PrintAxioms/TheoremSevenOne.lean
```

The second command must report exactly `propext`, `Classical.choice`, and
`Quot.sound` for all three solution declarations. The challenge warnings about
`sorry` are expected; no `sorry` occurs in the solution or production cone.

For the project verification harness, run from the repository root:

```bash
C48_PYTHON="$PWD/.venv/bin/python" bash ground_zero_work/phase29/verify_phase29.sh
```

## Palomar form values

- project path: repository root in the dedicated public candidate
- Comparator config: `comparator/config-theorem-seven-one.json`
- metadata: `comparator/formalization-theorem-seven-one.yaml`

The repository must be public and the submitted revision must be a pushed,
full 40-character commit SHA. Palomar's NanoDa and automated editorial checks
have not run merely because the local checks above pass. No human or peer
review is claimed; all review presently available is AI review plus the human
maintainer's clean-room Mathematica recalculation.
