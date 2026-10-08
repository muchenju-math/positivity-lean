import Mathlib

/-!
# Formal derivatives of determinants

The Leibniz formula and the product rule express a determinant derivative
as a sum of single-row or single-column replacements. These identities
work over commutative rings and do not require the matrix to be invertible.
-/


namespace Positivity
variable {ι R A : Type*} [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A]

theorem derivation_finset_prod (D : Derivation R A A) (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
    simp only [smul_eq_mul, Finset.erase_insert ha, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := ne_of_mem_of_not_mem hi ha
    rw [Finset.erase_insert_of_ne hia.symm]
    rw [Finset.prod_insert (by simp [ha])]
    ring

theorem derivation_det_columns [Fintype ι] (D : Derivation R A A) (M : Matrix ι ι A) :
    D M.det = ∑ j, (M.updateCol j (fun i => D (M i j))).det := by
  classical
  rw [Matrix.det_apply', map_sum]
  simp only [D.leibniz, D.map_intCast, mul_zero, add_zero, smul_eq_mul,
    derivation_finset_prod, Finset.mul_sum]
  simp_rw [Matrix.det_apply']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  simp only [Matrix.updateCol_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp [Finset.ne_of_mem_erase hk]

theorem derivation_det_rows [Fintype ι] (D : Derivation R A A) (M : Matrix ι ι A) :
    D M.det = ∑ j, (M.updateRow j (fun i => D (M j i))).det := by
  classical
  rw [← Matrix.det_transpose M, derivation_det_columns]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.det_transpose]
  congr 1
  funext k l
  simp [Matrix.transpose_apply, Matrix.updateCol_apply, Matrix.updateRow_apply]

end Positivity

open scoped BigOperators
open Polynomial

namespace Positivity

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem derivative_det_columns (A : Matrix ι ι (Polynomial R)) :
    derivative A.det = ∑ j, (A.updateCol j (fun i => derivative (A i j))).det := by
  classical
  rw [Matrix.det_apply']
  simp only [derivative_sum, derivative_mul, derivative_intCast, zero_mul, zero_add,
    derivative_prod_finset, Finset.mul_sum]
  simp_rw [Matrix.det_apply']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  simp only [Matrix.updateCol_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp [Finset.ne_of_mem_erase hk]

theorem derivative_det_rows (A : Matrix ι ι (Polynomial R)) :
    derivative A.det = ∑ j, (A.updateRow j (fun i => derivative (A j i))).det := by
  classical
  rw [← Matrix.det_transpose A, derivative_det_columns]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.det_transpose]
  congr 1
  ext k l
  simp [Matrix.transpose_apply, Matrix.updateCol_apply, Matrix.updateRow_apply]

theorem derivative_det_affineMatrix_at_zero (A B : Matrix ι ι R) :
    (derivative (Matrix.det (fun i j => C (A i j) + X * C (B i j)))).eval 0 =
      ∑ i, (A.updateRow i (B i)).det := by
  classical
  let N : Matrix ι ι (Polynomial R) := fun i j => C (A i j) + X * C (B i j)
  change (derivative N.det).eval 0 = _
  rw [derivative_det_rows, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  change (evalRingHom (0 : R)) (N.updateRow i (fun j => derivative (N i j))).det = _
  rw [RingHom.map_det]
  congr 1
  ext j k
  simp only [RingHom.mapMatrix_apply, Matrix.updateRow_apply]
  by_cases h : j = i <;> simp [Matrix.updateRow, h, N]

end Positivity
