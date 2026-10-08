import Positivity.SigmaRectBlock

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E R : Type*} {n m : V → Type*} [Fintype V] [Fintype E]
    [∀ v, Fintype (n v)] [∀ v, Fintype (m v)] [CommRing R]

noncomputable def blockLaplacian (src tgt : E → V)
    (P : ∀ e, Matrix (n (src e)) (n (tgt e)) R) (w : E → R) :
    Matrix (Sigma n) (Sigma n) R :=
  ∑ e, w e • (sigmaRectBlock (src e) (src e) (1 : Matrix (n (src e)) _ R) -
    sigmaRectBlock (src e) (tgt e) (P e))

theorem blockLaplacian_intertwine (src tgt : E → V)
    (P : ∀ e, Matrix (n (src e)) (n (tgt e)) R)
    (Q : ∀ e, Matrix (m (src e)) (m (tgt e)) R)
    (S : ∀ v, Matrix (n v) (m v) R) (w : E → R)
    (h : ∀ e, P e * S (tgt e) = S (src e) * Q e) :
    blockLaplacian src tgt P w * Matrix.blockDiagonal' S =
      Matrix.blockDiagonal' S * blockLaplacian src tgt Q w := by
  classical
  rw [blockLaplacian, blockLaplacian, Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [Matrix.sub_mul, Matrix.mul_sub, sigmaRectBlock_mul_diagonal,
    sigmaRectBlock_mul_diagonal, diagonal_mul_sigmaRectBlock,
    diagonal_mul_sigmaRectBlock, Matrix.one_mul, Matrix.mul_one, h]

noncomputable def sigmaSplitEquiv (n : V → Type*) :
    (Σ v, PUnit.{1} ⊕ n v) ≃ V ⊕ Sigma n where
  toFun x := match x with
    | ⟨v, Sum.inl _⟩ => Sum.inl v
    | ⟨v, Sum.inr p⟩ => Sum.inr ⟨v, p⟩
  invFun x := match x with
    | Sum.inl v => ⟨v, Sum.inl PUnit.unit⟩
    | Sum.inr ⟨v, p⟩ => ⟨v, Sum.inr p⟩
  left_inv := by rintro ⟨v, p | p⟩ <;> rfl
  right_inv := by rintro (v | ⟨v, p⟩) <;> rfl

noncomputable def scalarLaplacian (src tgt : E → V) (w : E → R) : Matrix V V R :=
  ∑ e, w e • (Matrix.single (src e) (src e) 1 - Matrix.single (src e) (tgt e) 1)

theorem sigmaRectBlock_split (u v : V) (c : R) (M : Matrix (n u) (n v) R) :
    Matrix.reindex (sigmaSplitEquiv n) (sigmaSplitEquiv n)
      (sigmaRectBlock u v (Matrix.fromBlocks (Matrix.of (fun _ _ : PUnit.{1} => c)) 0 0 M)) =
        Matrix.fromBlocks (Matrix.single u v c) 0 0 (sigmaRectBlock u v M) := by
  classical
  funext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hi : i = u <;> by_cases hj : j = v <;> subst_vars <;>
        simp_all [Matrix.reindex_apply, sigmaSplitEquiv, sigmaRectBlock, Matrix.single, eq_comm]
    | inr j =>
      rcases j with ⟨j, q⟩
      by_cases hi : i = u <;> by_cases hj : j = v <;> subst_vars <;>
        simp_all [Matrix.reindex_apply, sigmaSplitEquiv, sigmaRectBlock, eq_comm]
  | inr i =>
    rcases i with ⟨i, p⟩
    cases j with
    | inl j =>
      by_cases hi : i = u <;> by_cases hj : j = v <;> subst_vars <;>
        simp_all [Matrix.reindex_apply, sigmaSplitEquiv, sigmaRectBlock, eq_comm]
    | inr j =>
      rcases j with ⟨j, q⟩
      by_cases hi : i = u <;> by_cases hj : j = v <;> subst_vars <;>
        simp_all [Matrix.reindex_apply, sigmaSplitEquiv, sigmaRectBlock, eq_comm]

theorem blockLaplacian_split (src tgt : E → V)
    (P : ∀ e, Matrix (n (src e)) (n (tgt e)) R) (w : E → R) :
    Matrix.reindex (sigmaSplitEquiv n) (sigmaSplitEquiv n)
      (blockLaplacian src tgt
        (fun e => Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} R) 0 0 (P e)) w) =
      Matrix.fromBlocks (scalarLaplacian src tgt w) 0 0 (blockLaplacian src tgt P w) := by
  classical
  let e := sigmaSplitEquiv n
  have hdiag (v : V) : (1 : Matrix (PUnit.{1} ⊕ n v) (PUnit.{1} ⊕ n v) R) =
      Matrix.fromBlocks (Matrix.of (fun _ _ : PUnit.{1} => (1 : R))) 0 0 1 := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]
  have hone : (1 : Matrix PUnit.{1} PUnit.{1} R) = Matrix.of (fun _ _ => (1 : R)) := by
    ext i j
    simp
  have hedge (a : E) :
      Matrix.reindex e e (sigmaRectBlock (src a) (src a)
        (1 : Matrix (PUnit.{1} ⊕ n (src a)) _ R) -
        sigmaRectBlock (src a) (tgt a)
          (Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} R) 0 0 (P a))) =
      Matrix.fromBlocks (Matrix.single (src a) (src a) 1 - Matrix.single (src a) (tgt a) 1) 0 0
        (sigmaRectBlock (src a) (src a) (1 : Matrix (n (src a)) _ R) -
          sigmaRectBlock (src a) (tgt a) (P a)) := by
    change Matrix.reindex e e (sigmaRectBlock (src a) (src a) 1) -
      Matrix.reindex e e (sigmaRectBlock (src a) (tgt a) (Matrix.fromBlocks 1 0 0 (P a))) = _
    rw [hdiag, hone, sigmaRectBlock_split, sigmaRectBlock_split]
    ext i j
    cases i <;> cases j <;> simp
  have hsum : Matrix.reindex e e (blockLaplacian src tgt
      (fun a => Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} R) 0 0 (P a)) w) =
      ∑ a, w a • Matrix.reindex e e (sigmaRectBlock (src a) (src a)
        (1 : Matrix (PUnit.{1} ⊕ n (src a)) _ R) -
        sigmaRectBlock (src a) (tgt a) (Matrix.fromBlocks 1 0 0 (P a))) := by
    ext i j
    simp [blockLaplacian, Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply]
    simp only [sigmaRectBlock, Matrix.one_apply]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> rfl
  rw [hsum]
  simp_rw [hedge]
  ext i j
  cases i <;> cases j <;>
    simp [scalarLaplacian, blockLaplacian, Matrix.sum_apply, Matrix.smul_apply]

end Positivity
