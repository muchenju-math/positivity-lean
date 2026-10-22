# Correspondence with the manuscript

This file refers to *Coefficient positivity for arborescence ratios of
covering digraphs*, `main.tex` in the Overleaf positivity project, reviewed
on 22 October 2026. Its SHA-256 digest is
`d481cc30be558d1196bd72360fbb9b9a4065c3112bba8162a28a0aa247c38f02`.
The manuscript and development backups are kept outside this repository.

## Definitions and notation

| Manuscript | Lean |
| --- | --- |
| Finite-fiber system `F` (Definition 2.1) | `FiniteFiberSystem V E` |
| Fiber `S_v`, map `f_e` | `F.Fiber v`, `F.fiberMap e` |
| Associated vertices and edges | `F.FullCoord`, `F.LiftedEdge` |
| Coordinate matrix of the base endomorphism `L_G` | `F.baseGraphMatrix` |
| Coordinate matrix of the endomorphism `L_F` | `F.fullGraphMatrix` |
| Induced quotient endomorphism `Q_F` | represented by `F.quotientLaplacian` over the integers, or `F.quotientGraphMatrix` over the rationals |
| `P_F = det Q_F` | `F.quotientDeterminant` |
| Quotient rank `D(F)` | `F.totalDimension` |
| Balanced system | `F.Balanced` |
| Rooted polynomial `A_r(G)` | `arborescencePolynomial F.src F.tgt r` |
| Rooted polynomial `A_p(F)` | `F.liftedArborescencePolynomial r p` |
| Contraction `F/(p -> f_e(p))` | `F.contractMovedEdge` |
| Contraction followed by deletion of the base loop, `F_{e,p}` | `F.contractLoopEdge` |
| Auxiliary system `hat F` | `F.eliminateSystemAllCompositions` |
| System `F_phi` | `F.eliminateSystemInj` |

The paper defines endomorphisms over `Q[x]`. Lean uses their coordinate
matrices, acting on column vectors. These are the same operators: an edge
`p -> f_e(p)` contributes `x_e` at `(p,p)` and `-x_e` at `(p,f_e(p))`,
with cancellation when the two positions coincide. No bijectivity is
assumed in the finite-fiber definitions.

Lean chooses one reference point in each nonempty fiber. The quotient
basis consists of the classes of all other coordinate vectors. This
choice provides coordinates; it imposes no restriction on a fiber map.
In `FiberConstantDecomposition.lean`, the first basis vector in each fiber
is its constant vector. The remaining vectors are the coordinate vectors
away from the reference. `fullGraphMatrix_constant_intertwine` proves
that the full matrix in this basis has diagonal blocks `L_G` and `Q_F`
and a zero lower-left block. `quotientGraphMatrix_eq_map` identifies its
quotient block with the rational image of `quotientLaplacian`. Thus the
matrix used in the positivity theorem represents the induced quotient
endomorphism in the paper, also for nonbijective fiber maps.

The quotient matrix has integer polynomial entries in these coordinates.
This gives integrality of `P_F` directly. The manuscript instead deduces
integrality from the monic characteristic-polynomial factorization; the
two proofs establish the same statement.

## Results and proof routes

- **Theorem 2.3:** `quotientDeterminant_coeff_nonnegative` proves
  coefficient nonnegativity for every finite-fiber system.
- **Lemma 2.4 and (2.7):** `arborescence_sum_identity` and
  `laplacianCharacteristicFactorization` apply to arbitrary fiber maps.
  The characteristic polynomial is defined as `(-M).charpoly`, hence it
  is `det(z I + M)`. Taking the coefficient of `z` and applying the
  directed matrix-tree theorem gives the root-sum identity, as in the
  manuscript. Empty vertex sets are covered as well.
- **Proposition 2.5:** `covering_tree_identity` proves the integer
  polynomial identity `k * A_lift = A_base * P_F`.
  `arborescenceRatio_eq_normalized_determinant` gives the ratio `P_F/k`
  when the base arborescence polynomial is nonzero. The library uses a
  direct cofactor decomposition for this covering identity, rather than
  assuming a result from the literature.
- **Lemma 2.6:** the polarization construction and sourcewise homogeneity
  are in `FiniteFiber.lean`; the factorial coefficient reduction is used
  in `MainTheorem.lean` and `CoefficientPositivity.lean`.
- **Lemma 3.2:** `loopCharacteristicDerivative` proves the derivative
  formula for `shiftedQuotientDeterminant F z` over any commutative
  coefficient ring. Taking `R = Polynomial Z` and `z = Polynomial.X`
  makes `z` an independent indeterminate. Edge differentiation fixes it.
  Contraction here retains the base edge; it removes one fiber element.
  The earlier `loopDeterminantDerivative` is the corresponding formula
  at `z = 0`.
- **Corollary 3.4:** `loopCoefficientRecurrence` additionally specializes
  the loop variable to zero, so the child system deletes that base edge.
  This is the balanced contraction used in the induction.
- **Lemma 4.1:** `FiniteFiberSystem.exists_elimination_vertex` does not
  assume that the base is loopless. The loopless hypothesis belongs to
  the subsequent elimination construction.
- **Lemma 4.2 and Proposition 4.4:** the Schur complement and coefficient
  extraction are proved in the elimination modules; the final statement
  is `eliminationCoefficientRecurrence`. The all-compositions system is
  the paper's `hat F`, not `tilde F`.
- **Section 5 and Theorem 1.1:** `balancedCoefficient_nonnegative`,
  `quotientDeterminant_coeff_nonnegative`, and
  `arborescenceRatio_nonnegative_integer_polynomial` complete the
  induction, polarization, and covering application. The last theorem
  includes integrality as well as nonnegativity, with no assumed
  recurrence or matrix-tree identity.

Section 6's cited double-cover formula and its general combinatorial
problem are not separately formalized. Neither are the individual
expository examples or the figures. A successful build verifies the
declarations above, not every sentence of the manuscript. `Verification.lean`
prints the axiom dependencies of the principal results, including the
new arbitrary-map and scalar-parameter identities.
