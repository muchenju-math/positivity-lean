import Positivity.LiftedLaplacian
import Positivity.WeightedMatrixTree
import Positivity.CoverDeterminantCast

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

/-- The lifted arborescence polynomial with the weight of every lifted
edge identified with the variable of its base edge. -/
noncomputable def liftedArborescencePolynomial (F : FiniteFiberSystem V E)
    (r : V) (p : F.Fiber r) : MvPolynomial E ℤ :=
  MvPolynomial.rename Sigma.fst (arborescencePolynomial F.liftedSrc F.liftedTgt ⟨r, p⟩)

theorem baseGraphMatrix_cofactor (F : FiniteFiberSystem V E) (r : V) :
    F.baseGraphMatrix.adjugate r r =
      (arborescencePolynomial F.src F.tgt r).map (Int.castRingHom ℚ) := by
  rw [baseGraphMatrix, weighted_matrix_tree]
  have hh : MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial E ℚ)) MvPolynomial.X =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro e
      simp
  rw [hh]

theorem fullGraphMatrix_cofactor_tree (F : FiniteFiberSystem V E) (r : V) (p : F.Fiber r) :
    F.fullGraphMatrix.adjugate ⟨r, p⟩ ⟨r, p⟩ =
      (F.liftedArborescencePolynomial r p).map (Int.castRingHom ℚ) := by
  rw [fullGraphMatrix_eq_lifted, weighted_matrix_tree]
  have hh : MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial E ℚ))
      (fun a : F.LiftedEdge => (MvPolynomial.X a.1 : MvPolynomial E ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℚ)).comp (MvPolynomial.rename Sigma.fst).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro a
      simp
  rw [hh]
  rfl

/-- The exact covering identity over the integer polynomial ring. -/
theorem covering_tree_identity (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (r : V) (p : F.Fiber r) :
    MvPolynomial.C (F.fiberSize r : ℤ) * F.liftedArborescencePolynomial r p =
      arborescencePolynomial F.src F.tgt r * F.quotientDeterminant := by
  have h := F.fullGraphMatrix_cofactor hbij r p
  rw [F.fullGraphMatrix_cofactor_tree, F.baseGraphMatrix_cofactor, F.zeroGraphMatrix_det] at h
  have hk : (F.fiberSize r : ℚ) ≠ 0 := by
    have hp : 0 < F.fiberSize r := by
      letI := F.fiberFintype r
      exact Fintype.card_pos_iff.mpr ⟨F.reference r⟩
    exact_mod_cast Nat.ne_of_gt hp
  have hkk : (MvPolynomial.C (F.fiberSize r : ℚ) : MvPolynomial E ℚ) *
      MvPolynomial.C ((F.fiberSize r : ℚ)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hk, map_one]
  have hh := congrArg (fun q : MvPolynomial E ℚ => MvPolynomial.C (F.fiberSize r : ℚ) * q) h
  rw [← mul_assoc, ← mul_assoc, hkk, one_mul] at hh
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simpa only [map_mul, MvPolynomial.map_C, map_natCast] using hh

end Positivity.FiniteFiberSystem
