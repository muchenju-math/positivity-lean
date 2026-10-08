import Positivity.DirectedMatrixTree
import Positivity.BlockLaplacian
import Positivity.CofactorDecomposition

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E R : Type*} [Fintype V] [Fintype E] [CommRing R]

theorem outgoingLaplacian_map (src tgt : E → V) (φ : MvPolynomial E ℤ →+* R) :
    (outgoingLaplacian src tgt).map φ =
      scalarLaplacian src tgt (fun e => φ (MvPolynomial.X e)) := by
  classical
  funext v w
  simp only [outgoingLaplacian, Matrix.map_apply, map_sum, map_mul, map_sub,
    apply_ite φ, map_one, map_zero, scalarLaplacian, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul]
  erw [← Finset.sum_subtype (Finset.univ.filter (fun e => src e = v)) (by simp)
    (fun e => φ (MvPolynomial.X e) *
      ((if v = w then 1 else 0) - (if tgt e = w then 1 else 0)))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : src e = v
  · simp [Matrix.single, h, eq_comm]
  · simp [Matrix.single, h, Ne.symm h]

theorem weighted_matrix_tree (src tgt : E → V) (w : E → R) (r : V) :
    (scalarLaplacian src tgt w).adjugate r r =
      MvPolynomial.eval₂Hom (Int.castRingHom R) w (arborescencePolynomial src tgt r) := by
  classical
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom R) w
  have hmap : (outgoingLaplacian src tgt).map φ = scalarLaplacian src tgt w := by
    simpa [φ] using outgoingLaplacian_map src tgt φ
  rw [← hmap, adjugate_diagonal_eq_minor]
  have hm : ((outgoingLaplacian src tgt).map φ).submatrix
      (Subtype.val : {v : V // v ≠ r} → V) Subtype.val =
      (reducedLaplacian src tgt r).map φ := rfl
  rw [hm]
  erw [← RingHom.map_det φ (reducedLaplacian src tgt r)]
  exact congrArg φ (directed_matrix_tree src tgt r)

end Positivity
