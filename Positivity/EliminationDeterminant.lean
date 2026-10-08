import Positivity.EliminationEvaluation
import Positivity.EliminationSchur

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Field K]

/-- Vertex elimination replaces each virtual edge weight by `a * b / s`
and contributes the scalar factor `s` to the power of the eliminated dimension. -/
theorem quotientDeterminant_elimination_evaluation (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (φ : MvPolynomial E ℤ →+* K)
    (hs : φ (F.outgoingWeightSum u) ≠ 0) :
    φ F.quotientDeterminant = φ (F.outgoingWeightSum u) ^ F.fiberDimension u *
      F.eliminationEvaluation u φ (F.eliminateSystemAllCompositions u hloop).quotientDeterminant := by
  classical
  letI : Fintype {i : F.Coord // i.1 ≠ u} :=
    @Subtype.fintype _ _ (fun i => @instDecidableNot (i.1 = u)
      (Classical.propDecidable _)) F.coordFintype
  rw [Positivity.quotientDeterminant_elimination_schur F hloop u φ hs]
  congr 1
  let e := F.auxiliaryCoordEquiv u hloop
  let M := (quotientBlock₂₂ F (F.eliminationCoordEquiv u)).map φ -
    (φ (F.outgoingWeightSum u))⁻¹ •
      ((quotientBlock₂₁ F (F.eliminationCoordEquiv u)).map φ *
        (quotientBlock₁₂ F (F.eliminationCoordEquiv u)).map φ)
  change M.det = _
  change M.det = (F.eliminationEvaluation u φ)
    (F.eliminateSystemAllCompositions u hloop).quotientLaplacian.det
  rw [RingHom.map_det, ← Matrix.det_reindex_self e]
  congr 1
  funext i j
  change φ (F.quotientLaplacian (e.symm i).val (e.symm j).val) -
    (φ (F.outgoingWeightSum u))⁻¹ *
      (∑ k : F.CoordAt u, φ (F.quotientLaplacian (e.symm i).val ⟨u, k⟩) *
        φ (F.quotientLaplacian ⟨u, k⟩ (e.symm j).val)) = _
  exact (F.eliminationEvaluation_quotientLaplacian u hloop φ hs i j).symm

end Positivity.FiniteFiberSystem
