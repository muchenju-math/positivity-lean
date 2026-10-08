import Positivity.DeterminantDerivative

namespace Positivity
variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem det_updateRow_finset_sum (A : Matrix ι ι R) (i : ι)
    (s : Finset κ) (v : κ → ι → R) :
    (A.updateRow i (∑ k ∈ s, v k)).det = ∑ k ∈ s, (A.updateRow i (v k)).det :=
  (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).map_update_sum s i v A

/-- The coefficient of a rank-one direction in the determinant differential. -/
noncomputable def rankOneDetCoefficient (A : Matrix ι ι R) (a l : ι → R) : R :=
  ∑ i, a i * (A.updateRow i l).det

theorem det_row_sum_rankOne [Fintype κ] (A : Matrix ι ι R)
    (a l : κ → ι → R) :
    (∑ i, (A.updateRow i (fun j => ∑ k, a k i * l k j)).det) =
      ∑ k, rankOneDetCoefficient A (a k) (l k) := by
  classical
  have hrow (i : ι) : (fun j => ∑ k, a k i * l k j) = ∑ k, a k i • l k := by
    funext j
    simp
  simp_rw [hrow, det_updateRow_finset_sum, Matrix.det_updateRow_smul]
  exact Finset.sum_comm

theorem derivative_det_rankOne_at_zero (A : Matrix ι ι R) (a l : ι → R) :
    (Polynomial.derivative (Matrix.det (fun i j => Polynomial.C (A i j) +
      Polynomial.X * Polynomial.C (a i * l j)))).eval 0 =
        rankOneDetCoefficient A a l := by
  apply (derivative_det_affineMatrix_at_zero A (fun i j => a i * l j)).trans
  unfold rankOneDetCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  exact Matrix.det_updateRow_smul A i (a i) l

end Positivity
