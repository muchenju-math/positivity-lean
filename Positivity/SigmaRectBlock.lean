import Positivity.SigmaBlockMatrix

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V R : Type*} {n m l : V → Type*} [Fintype V]
    [∀ v, Fintype (n v)] [∀ v, Fintype (m v)] [∀ v, Fintype (l v)] [CommRing R]

noncomputable def sigmaRectBlock (u v : V) (M : Matrix (n u) (m v) R) :
    Matrix (Sigma n) (Sigma m) R :=
  fun i j => if hi : i.1 = u then if hj : j.1 = v then M (hi ▸ i.2) (hj ▸ j.2) else 0 else 0

theorem mul_blockDiagonal'_rect_entry (M : Matrix (Sigma n) (Sigma m) R)
    (H : ∀ v, Matrix (m v) (l v) R) (u v : V) (i : n u) (j : l v) :
    (M * Matrix.blockDiagonal' H) ⟨u, i⟩ ⟨v, j⟩ =
      ∑ k : m v, M ⟨u, i⟩ ⟨v, k⟩ * H v k j := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single v]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hw, mul_zero]
  · simp

theorem blockDiagonal'_mul_rect_entry (M : Matrix (Sigma m) (Sigma l) R)
    (H : ∀ v, Matrix (n v) (m v) R) (u v : V) (i : n u) (j : l v) :
    (Matrix.blockDiagonal' H * M) ⟨u, i⟩ ⟨v, j⟩ =
      ∑ k : m u, H u i k * M ⟨u, k⟩ ⟨v, j⟩ := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single u]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hw), zero_mul]
  · simp

theorem sigmaRectBlock_mul_diagonal (u v : V) (M : Matrix (n u) (m v) R)
    (H : ∀ w, Matrix (m w) (l w) R) :
    sigmaRectBlock u v M * Matrix.blockDiagonal' H = sigmaRectBlock u v (M * H v) := by
  classical
  funext i j
  rcases i with ⟨a, i⟩
  rcases j with ⟨b, j⟩
  rw [mul_blockDiagonal'_rect_entry]
  by_cases ha : a = u
  · subst a
    by_cases hb : b = v
    · subst b
      simp only [sigmaRectBlock, dite_true, Matrix.mul_apply]
    · simp [sigmaRectBlock, hb]
  · simp [sigmaRectBlock, ha]

theorem diagonal_mul_sigmaRectBlock (u v : V) (M : Matrix (m u) (l v) R)
    (H : ∀ w, Matrix (n w) (m w) R) :
    Matrix.blockDiagonal' H * sigmaRectBlock u v M = sigmaRectBlock u v (H u * M) := by
  classical
  funext i j
  rcases i with ⟨a, i⟩
  rcases j with ⟨b, j⟩
  rw [blockDiagonal'_mul_rect_entry]
  by_cases ha : a = u
  · subst a
    by_cases hb : b = v
    · subst b
      simp only [sigmaRectBlock, dite_true, Matrix.mul_apply]
    · simp [sigmaRectBlock, hb]
  · simp [sigmaRectBlock, ha]

end Positivity
