import Positivity.FullCoverDecomposition

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

theorem zeroGraphMatrix_eq_map (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) :
    F.zeroGraphMatrix hbij =
      (F.coveringLaplacian hbij).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  classical
  funext i j
  simp only [zeroGraphMatrix, blockLaplacian, coveringLaplacian, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul, map_sum,
    map_mul, MvPolynomial.map_X]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  simp only [coveringEdgeCoefficient, Matrix.sub_apply, Matrix.map_apply,
    map_sub, MvPolynomial.map_C]
  simp only [sigmaRectBlock, sigmaBlock]
  split_ifs <;> simp only [zeroLocalPullback, coveringPullback, zeroSumPullback,
    Matrix.map_apply, Matrix.one_apply, map_sub, apply_ite, map_one, map_zero,
    Int.cast_one, Int.cast_zero] <;> split_ifs <;> rfl

theorem zeroGraphMatrix_det (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) :
    (F.zeroGraphMatrix hbij).det = F.quotientDeterminant.map (Int.castRingHom ℚ) := by
  rw [zeroGraphMatrix_eq_map]
  erw [← RingHom.map_det (MvPolynomial.map (Int.castRingHom ℚ)) (F.coveringLaplacian hbij)]
  rw [coveringLaplacian_det]

end Positivity.FiniteFiberSystem
