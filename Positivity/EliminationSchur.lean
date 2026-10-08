import Positivity.EliminationBlocks

namespace Positivity
open FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E R α β : Type*} [Fintype V] [Fintype E]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [CommRing R]

theorem quotientDeterminant_map_schur (F : FiniteFiberSystem V E)
    (φ : MvPolynomial E ℤ →+* R) (e : F.Coord ≃ α ⊕ β)
    [Invertible ((quotientBlock₁₁ F e).map φ)] :
    φ F.quotientDeterminant =
      ((quotientBlock₁₁ F e).map φ).det *
        ((quotientBlock₂₂ F e).map φ - (quotientBlock₂₁ F e).map φ *
          ⅟ ((quotientBlock₁₁ F e).map φ) * (quotientBlock₁₂ F e).map φ).det := by
  classical
  change φ F.quotientLaplacian.det = _
  rw [RingHom.map_det, ← Matrix.det_reindex_self e]
  have hblocks : Matrix.reindex e e (F.quotientLaplacian.map φ) =
      Matrix.fromBlocks ((quotientBlock₁₁ F e).map φ) ((quotientBlock₁₂ F e).map φ)
        ((quotientBlock₂₁ F e).map φ) ((quotientBlock₂₂ F e).map φ) := by
    ext i j
    cases i <;> cases j <;> rfl
  erw [hblocks]
  exact Matrix.det_fromBlocks₁₁ _ _ _ _

theorem quotientBlock_elimination_map_scalar (F : FiniteFiberSystem V E)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (u : V) (φ : MvPolynomial E ℤ →+* R) :
    (quotientBlock₁₁ F (F.eliminationCoordEquiv u)).map φ =
      φ (F.outgoingWeightSum u) • (1 : Matrix (F.CoordAt u) (F.CoordAt u) R) := by
  rw [F.quotientBlock_elimination_scalar hloop u]
  funext i j
  by_cases hij : i = j <;>
    simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, hij]

end Positivity

namespace Positivity
open FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E K : Type*} [Fintype V] [Fintype E] [Field K]

/-- The concrete scalar-block Schur formula after evaluating edge variables
in a field where the outgoing weight sum is nonzero. -/
theorem quotientDeterminant_elimination_schur (F : FiniteFiberSystem V E)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (u : V)
    (φ : MvPolynomial E ℤ →+* K) (hs : φ (F.outgoingWeightSum u) ≠ 0) :
    φ F.quotientDeterminant = φ (F.outgoingWeightSum u) ^ F.fiberDimension u *
      ((quotientBlock₂₂ F (F.eliminationCoordEquiv u)).map φ -
        (φ (F.outgoingWeightSum u))⁻¹ •
          ((quotientBlock₂₁ F (F.eliminationCoordEquiv u)).map φ *
            (quotientBlock₁₂ F (F.eliminationCoordEquiv u)).map φ)).det := by
  classical
  let e := F.eliminationCoordEquiv u
  let s := φ (F.outgoingWeightSum u)
  let A := (quotientBlock₁₁ F e).map φ
  let B := (quotientBlock₁₂ F e).map φ
  let C := (quotientBlock₂₁ F e).map φ
  let D := (quotientBlock₂₂ F e).map φ
  have hA : A = s • (1 : Matrix (F.CoordAt u) (F.CoordAt u) K) :=
    quotientBlock_elimination_map_scalar F hloop u φ
  letI : Invertible A := {
    invOf := s⁻¹ • (1 : Matrix (F.CoordAt u) (F.CoordAt u) K)
    invOf_mul_self := by rw [hA]; simp [smul_mul_smul_comm, s, hs]
    mul_invOf_self := by rw [hA]; simp [smul_mul_smul_comm, s, hs] }
  have hdet : A.det = s ^ F.fiberDimension u := by
    rw [hA, Matrix.det_smul, Matrix.det_one, mul_one, F.card_coordAt]
  have h := quotientDeterminant_map_schur F φ e
  change φ F.quotientDeterminant = A.det *
    (D - C * (s⁻¹ • (1 : Matrix (F.CoordAt u) (F.CoordAt u) K)) * B).det at h
  rw [hdet] at h
  simpa only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] using h

end Positivity
