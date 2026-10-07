# Coefficient positivity for arborescences of covering digraphs

Fresh Lean 4 project for formalizing Sections 2–5 of the manuscript
`Positivity paper.zip`. Sections 6 and 7, their extensions, and their
conjectures are excluded.

The paper archive is intentionally kept local and is not part of this Lean
project's tracked files. The formalization is in progress; the main positivity
theorem and the coefficient recurrences are not yet fully formalized.

## Modules

- `Positivity/FiniteFiber.lean`: finite-fiber systems, quotient matrices,
  covering identity, and polarization.
- `Positivity/LoopContraction.lean`: Section 3 loop contraction recurrence.
- `Positivity/VertexElimination.lean`: Section 4 elimination recurrence.
- `Positivity/MainTheorem.lean`: Section 5 induction and main positivity result.

Lean toolchain: `leanprover/lean4:v4.34.0`.
