import Positivity.CoveringMatrix
import Positivity.CoefficientPositivity

namespace Positivity.FiniteFiberSystem
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Coefficient positivity for the matrix used in the covering
matrix-tree identity. -/
theorem coveringLaplacian_det_coeff_nonnegative (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (α : E →₀ ℕ) :
    0 ≤ (F.coveringLaplacian hbij).det.coeff α := by
  rw [F.coveringLaplacian_det hbij]
  exact quotientDeterminant_coeff_nonnegative F α

/-- Dividing by a positive sheet count preserves rational coefficient
nonnegativity. Identification with the arborescence ratio is separate. -/
theorem normalized_quotientDeterminant_coeff_nonnegative (F : FiniteFiberSystem V E)
    (k : ℕ) (hk : 0 < k) (α : E →₀ ℕ) :
    0 ≤ (((k : ℚ)⁻¹) • F.quotientDeterminant.map (Int.castRingHom ℚ)).coeff α := by
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
  change 0 ≤ (k : ℚ)⁻¹ * (F.quotientDeterminant.coeff α : ℚ)
  apply mul_nonneg
  · positivity
  · exact_mod_cast quotientDeterminant_coeff_nonnegative F α

end Positivity.FiniteFiberSystem
