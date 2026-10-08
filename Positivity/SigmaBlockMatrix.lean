import Mathlib

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V R : Type*} {n : V → Type*} [Fintype V] [∀ v, Fintype (n v)] [CommRing R]

theorem mul_blockDiagonal'_entry (M : Matrix (Sigma n) (Sigma n) R)
    (H : ∀ v, Matrix (n v) (n v) R) (u v : V) (i : n u) (j : n v) :
    (M * Matrix.blockDiagonal' H) ⟨u, i⟩ ⟨v, j⟩ =
      ∑ k : n v, M ⟨u, i⟩ ⟨v, k⟩ * H v k j := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single v]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hw, mul_zero]
  · simp

theorem blockDiagonal'_mul_entry (M : Matrix (Sigma n) (Sigma n) R)
    (H : ∀ v, Matrix (n v) (n v) R) (u v : V) (i : n u) (j : n v) :
    (Matrix.blockDiagonal' H * M) ⟨u, i⟩ ⟨v, j⟩ =
      ∑ k : n u, H u i k * M ⟨u, k⟩ ⟨v, j⟩ := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single u]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hw), zero_mul]
  · simp

/-- Extend a rectangular fiber block by zero to the full coordinate space. -/
noncomputable def sigmaBlock (u v : V) (M : Matrix (n u) (n v) R) :
    Matrix (Sigma n) (Sigma n) R :=
  fun i j => if hi : i.1 = u then if hj : j.1 = v then M (hi ▸ i.2) (hj ▸ j.2) else 0 else 0

theorem sigmaBlock_mul_diagonal (u v : V) (M : Matrix (n u) (n v) R)
    (H : ∀ w, Matrix (n w) (n w) R) :
    sigmaBlock u v M * Matrix.blockDiagonal' H = sigmaBlock u v (M * H v) := by
  classical
  funext i j
  rcases i with ⟨a, i⟩
  rcases j with ⟨b, j⟩
  rw [mul_blockDiagonal'_entry]
  by_cases ha : a = u
  · subst a
    by_cases hb : b = v
    · subst b
      simp only [sigmaBlock, dite_true, Matrix.mul_apply]
    · simp [sigmaBlock, hb]
  · simp [sigmaBlock, ha]

theorem diagonal_mul_sigmaBlock (u v : V) (M : Matrix (n u) (n v) R)
    (H : ∀ w, Matrix (n w) (n w) R) :
    Matrix.blockDiagonal' H * sigmaBlock u v M = sigmaBlock u v (H u * M) := by
  classical
  funext i j
  rcases i with ⟨a, i⟩
  rcases j with ⟨b, j⟩
  rw [blockDiagonal'_mul_entry]
  by_cases ha : a = u
  · subst a
    by_cases hb : b = v
    · subst b
      simp only [sigmaBlock, dite_true, Matrix.mul_apply]
    · simp [sigmaBlock, hb]
  · simp [sigmaBlock, ha]

end Positivity
