# Coefficient positivity for arborescences of covering digraphs

Fresh Lean 4 project for formalizing Sections 2–5 of the manuscript
`Positivity paper.zip`. Sections 6 and 7, their extensions, and their
conjectures are excluded.

The paper archive is intentionally kept local and is not part of this Lean
project's tracked files. The formalization is in progress; the main positivity
theorem and the coefficient recurrences are not yet fully formalized.

## Modules

- `Positivity/FiniteFiber.lean`: finite-fiber systems, quotient matrices, and
  the polarization substitution identity.
- `Positivity/LoopContraction.lean`: rank-one determinant derivatives and the
  loop-contraction construction; the coefficient recurrence remains
  unfinished.
- `Positivity/VertexElimination.lean`: vertex selection, the elimination
  construction, and an abstract Schur complement identity; the coefficient
  recurrence remains unfinished.
- `Positivity/MainTheorem.lean`: Section 5 induction and main positivity result.

Lean toolchain: `leanprover/lean4:v4.34.0`.

