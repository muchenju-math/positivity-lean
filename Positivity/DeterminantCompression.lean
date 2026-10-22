import Positivity.LoopContraction
import Positivity.DirectionalDeterminant

namespace Positivity
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A normalized replacement row gives the determinant of the induced
compression to its kernel. -/
theorem det_updateRow_compression (A : Matrix ι ι R) (p : ι) (l : ι → R)
    (hl : l p = 1) :
    (A.updateRow p l).det =
      Matrix.det (fun i j : {i : ι // i ≠ p} => A i j - A i p * l j) := by
  classical
  let e : {i : ι // i ≠ p} ⊕ PUnit.{1} ≃ ι := Equiv.subtypeNeSumPUnit p
  let B : Matrix {i : ι // i ≠ p} {i : ι // i ≠ p} R := fun i j => A i j
  let C : Matrix {i : ι // i ≠ p} PUnit.{1} R := fun i _ => A i p
  let D : Matrix PUnit.{1} {i : ι // i ≠ p} R := fun _ j => l j
  have hblocks : (A.updateRow p l).submatrix e e = Matrix.fromBlocks B C D 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [e, Equiv.subtypeNeSumPUnit, Matrix.updateRow_apply, i.property, B, Matrix.fromBlocks]
      | inr j => simp [e, Equiv.subtypeNeSumPUnit, Matrix.updateRow_apply, i.property, C, Matrix.fromBlocks]
    | inr i =>
      cases j with
      | inl j => simp [e, Equiv.subtypeNeSumPUnit, Matrix.updateRow_apply, D, Matrix.fromBlocks]
      | inr j => simp [e, Equiv.subtypeNeSumPUnit, Matrix.updateRow_apply, hl, Matrix.fromBlocks]
  rw [← Matrix.det_submatrix_equiv_self e, hblocks, Matrix.det_fromBlocks_one₂₂]
  congr 1
  ext i j
  change A i j - (∑ _k : PUnit.{1}, A i p * l j) = _
  simp

theorem det_updateRow_delta (A : Matrix ι ι R) (p : ι) :
    (A.updateRow p (fun j => if j = p then 1 else 0)).det =
      (A.submatrix (Subtype.val : {i : ι // i ≠ p} → ι) Subtype.val).det := by
  rw [det_updateRow_compression A p _ (by simp)]
  congr 1
  funext i j
  simp [j.property, Matrix.submatrix_apply]

theorem det_updateRow_difference (A : Matrix ι ι R) (p q : ι) (hpq : p ≠ q) :
    (A.updateRow p (fun j => (if j = p then 1 else 0) -
      (if j = q then 1 else 0))).det =
      Matrix.det (fun i j : {i : ι // i ≠ p} =>
        A i j + if j.val = q then A i p else 0) := by
  rw [det_updateRow_compression A p _ (by simp [hpq])]
  congr 1
  funext i j
  simp only [j.property, ite_eq_right, zero_sub, mul_neg, sub_neg_eq_add]
  by_cases hj : j.val = q <;> simp [hj]

/-- The normalized row-supported compression identity used in the proof
of Lemma 3.2, over any commutative ring. -/
theorem deriv_det_rankOneRowUpdate_compression [Nonempty ι]
    (A : Matrix ι ι R) (p : ι) (l : ι → R) (hl : l p = 1) :
    ((rankOneRowUpdate A p l).det.derivative).eval 0 =
      Matrix.det (fun i j : {i : ι // i ≠ p} => A i j - A i p * l j) := by
  rw [deriv_det_rankOneRowUpdate_at_zero, det_updateRow_compression A p l hl]

set_option backward.isDefEq.respectTransparency false

theorem derivative_det_affineMatrix_at_zero_columns (A B : Matrix ι ι R) :
    (Polynomial.derivative (Matrix.det (fun i j => Polynomial.C (A i j) +
      Polynomial.X * Polynomial.C (B i j)))).eval 0 =
        ∑ j, (A.updateCol j (fun i => B i j)).det := by
  classical
  let N : Matrix ι ι (Polynomial R) := fun i j => Polynomial.C (A i j) +
    Polynomial.X * Polynomial.C (B i j)
  change (Polynomial.derivative N.det).eval 0 = _
  rw [← Matrix.det_transpose N]
  apply (derivative_det_affineMatrix_at_zero A.transpose B.transpose).trans
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.updateRow_transpose, Matrix.det_transpose]
  rfl

theorem rankOneDetCoefficient_columns (A : Matrix ι ι R) (a l : ι → R) :
    rankOneDetCoefficient A a l = ∑ j, l j * (A.updateCol j a).det := by
  classical
  rw [← derivative_det_rankOne_at_zero]
  apply (derivative_det_affineMatrix_at_zero_columns A (fun i j => a i * l j)).trans
  apply Finset.sum_congr rfl
  intro j hj
  have hv : (fun i => a i * l j) = l j • a := by ext i; simp [mul_comm]
  rw [hv, Matrix.det_updateCol_smul]

theorem det_updateCol_compression (A : Matrix ι ι R) (p : ι) (a : ι → R)
    (ha : a p = 1) :
    (A.updateCol p a).det =
      Matrix.det (fun i j : {i : ι // i ≠ p} => A i j - a i * A p j) := by
  rw [← Matrix.det_transpose, ← Matrix.updateRow_transpose, det_updateRow_compression _ p a ha]
  rw [← Matrix.det_transpose]
  congr 1
  funext i j
  simp [Matrix.transpose_apply, mul_comm]


end Positivity
