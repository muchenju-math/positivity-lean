import Mathlib

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {I J R : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [CommRing R]

/-- Adjugates respect a direct sum, with the determinant of the other
block multiplying each diagonal block. -/
theorem adjugate_block_diagonal (A : Matrix I I R) (B : Matrix J J R) :
    (Matrix.fromBlocks A 0 0 B).adjugate =
      Matrix.fromBlocks (B.det • A.adjugate) 0 0 (A.det • B.adjugate) := by
  classical
  funext i j
  rw [Matrix.adjugate_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hm : (Matrix.fromBlocks A 0 0 B).updateRow (Sum.inl j) (Pi.single (Sum.inl i) 1) =
          Matrix.fromBlocks (A.updateRow j (Pi.single i 1)) 0 0 B := by
        ext a b
        cases a <;> cases b <;> simp [Matrix.updateRow_apply, Pi.single_apply]
      rw [hm, Matrix.det_fromBlocks_zero₂₁]
      simp [Matrix.adjugate_apply, mul_comm]
    | inr j =>
      have hm : (Matrix.fromBlocks A 0 0 B).updateRow (Sum.inr j) (Pi.single (Sum.inl i) 1) =
          Matrix.fromBlocks A 0 (Matrix.of (fun a b => if a = j then (if b = i then (1 : R) else 0) else 0))
            (B.updateRow j 0) := by
        ext a b
        cases a <;> cases b <;> simp [Matrix.updateRow_apply, Pi.single_apply]
      rw [hm, Matrix.det_fromBlocks_zero₁₂]
      rw [Matrix.det_eq_zero_of_row_eq_zero j (by intro k; simp), mul_zero]
      rfl
  | inr i =>
    cases j with
    | inl j =>
      have hm : (Matrix.fromBlocks A 0 0 B).updateRow (Sum.inl j) (Pi.single (Sum.inr i) 1) =
          Matrix.fromBlocks (A.updateRow j 0)
            (Matrix.of (fun a b => if a = j then (if b = i then (1 : R) else 0) else 0)) 0 B := by
        ext a b
        cases a <;> cases b <;> simp [Matrix.updateRow_apply, Pi.single_apply]
      rw [hm, Matrix.det_fromBlocks_zero₂₁]
      rw [Matrix.det_eq_zero_of_row_eq_zero j (by intro k; simp), zero_mul]
      rfl
    | inr j =>
      have hm : (Matrix.fromBlocks A 0 0 B).updateRow (Sum.inr j) (Pi.single (Sum.inr i) 1) =
          Matrix.fromBlocks A 0 0 (B.updateRow j (Pi.single i 1)) := by
        ext a b
        cases a <;> cases b <;> simp [Matrix.updateRow_apply, Pi.single_apply]
      rw [hm, Matrix.det_fromBlocks_zero₂₁]
      simp [Matrix.adjugate_apply]

theorem adjugate_conjugation (A S T : Matrix I I R) (hST : S * T = 1) (hTS : T * S = 1) :
    (S * A * T).adjugate = S * A.adjugate * T := by
  have hT : T.adjugate = T.det • S := by
    calc
      T.adjugate = T.adjugate * (T * S) := by rw [hTS, Matrix.mul_one]
      _ = T.det • S := by rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hS : S.adjugate = S.det • T := by
    calc
      S.adjugate = S.adjugate * (S * T) := by rw [hST, Matrix.mul_one]
      _ = S.det • T := by rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hd : T.det * S.det = 1 := by rw [← Matrix.det_mul, hTS, Matrix.det_one]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hT, hS,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd, one_smul, Matrix.mul_assoc]

end Positivity
