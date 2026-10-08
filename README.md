# Coefficient positivity for arborescences of covering digraphs

Lean 4 formalization of the main proof in Sections 2–5 of
*Coefficient positivity for arborescence ratios of covering digraphs*,
including the covering application in Theorem 1.1.

The main proof is complete, including the covering
arborescence-ratio application (Theorem 1.1). The finite-fiber positivity
theorem (Theorem 2.3), both recurrences, the directed matrix-tree theorem,
the covering determinant identity, and the integrality argument are proved.
The final results have no assumed recurrence or matrix-tree hypotheses.

## Main results

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 2.3: all finite-fiber determinant coefficients are nonnegative | `Positivity.quotientDeterminant_coeff_nonnegative` |
| Loop determinant derivative and Corollary 3.2 | `Positivity.loopDeterminantDerivative`, `Positivity.loopCoefficientRecurrence` |
| Proposition 4.4: elimination coefficient recurrence | `Positivity.eliminationCoefficientRecurrence` |
| Directed matrix-tree theorem | `Positivity.directed_matrix_tree` |
| Proposition 2.6: equality of quotient and covering determinants | `Positivity.FiniteFiberSystem.coveringLaplacian_det` |
| Exact integer identity `k * A_lift = A_base * P` | `Positivity.FiniteFiberSystem.covering_tree_identity` |
| Proposition 2.6: ratio equals `P / k` | `Positivity.FiniteFiberSystem.arborescenceRatio_eq_normalized_determinant` |
| Theorem 1.1: ratio is a nonnegative integer polynomial | `Positivity.FiniteFiberSystem.arborescenceRatio_nonnegative_integer_polynomial` |

The final theorem is in [CoveringMainTheorem.lean](Positivity/CoveringMainTheorem.lean). Given a finite
fiber system with bijective edge maps, a root `r`, a point `p` above it, and
a nonzero base arborescence polynomial, it produces `Q : MvPolynomial E ℤ`
with nonnegative coefficients such that the lifted/base arborescence ratio
equals `Q` in the fraction field and `P = C(k) * Q`. Here `k` is the size of
the root fiber; a uniform `k`-fold cover is a special case.

Arborescences are defined as choices of one outgoing edge from each nonroot
vertex for which every selected path reaches the root. Their polynomial is
the sum of their edge monomials. Lifted vertices and edges are explicitly
constructed from the fibers and fiber maps. Renaming lifted-edge variables
by their base-edge labels implements the manuscript's inherited weights.
Loops, parallel edges, and one-element fibers are included.

## Modules

- `Positivity/FiniteFiber.lean`: finite-fiber systems, quotient matrices, and
  the polarization substitution identity, including its compatibility with
  the quotient determinant and the labelled-copy system. The quotient
  determinant's sourcewise homogeneity is also proved from the Leibniz
  expansion.
- `Positivity/LoopContraction.lean`: the loop-contraction construction and
  edge deletion specialization. Contraction preserves the reference when
  it survives and redirects it otherwise.
- `Positivity/DeterminantDerivative.lean`, `DirectionalDeterminant.lean`, and
  `DeterminantCompression.lean`: determinant differentials, decomposition
  into rank-one directions, and row and column compression identities.
- `Positivity/LoopDirections.lean`, `LoopCompression.lean`,
  `ContractionCoordinates.lean`, `ContractionMatrix.lean`,
  `ReferenceContractionCoordinates.lean`, and `ReferenceContractionMatrix.lean`:
  the concrete contraction comparison, including the reference-sheet case.
- `Positivity/LoopRecurrence.lean`: the proved `loopDeterminantDerivative`
  and `loopCoefficientRecurrence`, with no recurrence hypotheses.
- `Positivity/NormalizedPullback.lean`: composition and reference-change
  identities for quotient pullback matrices.
- `Positivity/VertexElimination.lean`: vertex selection, the elimination
  constructions for selected injections and for all incoming/outgoing
  compositions, and an abstract Schur complement identity.
- `Positivity/EliminationBlocks.lean`, `EliminationPullback.lean`,
  `EliminationMatrix.lean`, `EliminationSchur.lean`, `EliminationEvaluation.lean`,
  and `EliminationDeterminant.lean`: the concrete Schur substitution identity.
- `Positivity/EliminationSelection.lean`, `SquarefreeCompletion.lean`,
  `GroupedSquarefree.lean`, `SumGroupedSquarefree.lean`,
  `EliminationCoefficientAlgebra.lean`, and the elimination coordinate and
  localization modules: the coefficient extraction over injective pairings.
- `Positivity/EliminationRecurrence.lean`: the proved vertex-elimination
  coefficient recurrence, including its factorial factor.
- `Positivity/MainTheorem.lean`: the Section 5 dimension induction, proved
  conditional on both recurrences. The arbitrary-coefficient polarization
  reduction is formalized and uses the proved sourcewise homogeneity result.
- `Positivity/CoefficientPositivity.lean`: applies the proved recurrences to
  the induction, then polarization, to obtain unconditional nonnegativity.
- `Positivity/CoverCoordinateChange.lean`, `CoveringMatrix.lean`, and
  `CoveringPositivity.lean`: the change from quotient to zero-sum fiber
  coordinates and equality of the covering and quotient determinants.
- `Positivity/DirectedArborescence.lean`, `FunctionalTreeDeterminant.lean`,
  `DeterminantRowExpansion.lean`, `DirectedMatrixTree.lean`, and
  `WeightedMatrixTree.lean`: actual rooted trees, their primitive polynomial,
  and the directed matrix-tree theorem over arbitrary commutative rings.
- `Positivity/FiberZeroSumBasis.lean`, `AdjugateBlocks.lean`,
  `SigmaBlockMatrix.lean`, `SigmaRectBlock.lean`, `BlockLaplacian.lean`,
  `CofactorDecomposition.lean`, and `FullCoverDecomposition.lean`: the full
  covering Laplacian split and its cofactor normalization by the fiber size.
- `Positivity/LiftedLaplacian.lean`, `CoverDeterminantCast.lean`, and
  `CoverTreeIdentity.lean`: connect that split to the base and lifted tree
  polynomials, then descend the exact identity from rational to integer
  coefficients.
- `Positivity/PrimitiveQuotient.lean` and `CoveringMainTheorem.lean`:
  integrality, nonnegative coefficients, and the final ratio theorem.

## Verification

Install [Lean via elan](https://github.com/leanprover/elan). The committed
`lean-toolchain` selects Lean 4.34.0, and `lake-manifest.json` pins mathlib
and its transitive dependencies. From a fresh checkout, run:

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

`Verification.lean` prints the axiom dependencies of the principal results.
They use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`;
there are no `sorryAx` dependencies or additional mathematical axioms.
The main results listed above are fully proved. The scope excludes Sections
6–7, their extensions and conjectures, and separate formalizations of
expository examples.

`Positivity.lean` is the library entry point. `Verification.lean` is the
reproducible axiom audit. This repository contains only the library sources,
documentation, audit, and build configuration; development experiments,
recovery copies, generated outputs, and manuscript archives are omitted.

Lean toolchain: `leanprover/lean4:v4.34.0`.
