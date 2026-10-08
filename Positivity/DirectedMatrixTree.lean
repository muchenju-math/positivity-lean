import Positivity.FunctionalTreeDeterminant
import Positivity.DeterminantRowExpansion

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def outgoingLaplacian (src tgt : E → V) : Matrix V V (MvPolynomial E ℤ) :=
  fun v w => ∑ e : {e : E // src e = v}, MvPolynomial.X e.val *
    ((if v = w then 1 else 0) - (if tgt e.val = w then 1 else 0))

noncomputable def reducedLaplacian (src tgt : E → V) (r : V) :
    Matrix {v : V // v ≠ r} {v : V // v ≠ r} (MvPolynomial E ℤ) :=
  (outgoingLaplacian src tgt).submatrix Subtype.val Subtype.val

noncomputable def rootChoiceEquiv (src : E → V) (r : V) :
    RootChoice src r ≃ (∀ v : {v : V // v ≠ r}, {e : E // src e = v.val}) where
  toFun t v := ⟨t.val v, t.property v⟩
  invFun t := ⟨fun v => (t v).val, fun v => (t v).property⟩
  left_inv t := rfl
  right_inv t := rfl

theorem selected_row_determinant (src tgt : E → V) (r : V) (t : RootChoice src r) :
    Matrix.det (fun v w : {v : V // v ≠ r} =>
      MvPolynomial.X (t.val v) *
        ((if v.val = w.val then 1 else 0) - (if tgt (t.val v) = w.val then 1 else 0))) =
      if t.ReachesRoot tgt then MvPolynomial.monomial t.exponent (1 : ℤ) else 0 := by
  classical
  erw [Matrix.det_mul_column]
  have hm : (fun v w : {v : V // v ≠ r} =>
      ((if v.val = w.val then 1 else 0) - (if tgt (t.val v) = w.val then 1 else 0) : MvPolynomial E ℤ)) =
      (1 - reducedTransition r (t.next tgt)).map MvPolynomial.C := by
    funext v w
    simp [Matrix.one_apply, reducedTransition, RootChoice.next, v.property, Subtype.ext_iff]
  rw [hm]
  erw [← RingHom.map_det (MvPolynomial.C (σ := E)) (1 - reducedTransition r (t.next tgt))]
  rw [reducedTransition_det r (t.next tgt) (by simp [RootChoice.next])]
  have hp : (∏ v : {v : V // v ≠ r}, (MvPolynomial.X (t.val v) : MvPolynomial E ℤ)) =
      MvPolynomial.monomial t.exponent 1 := (monomial_choiceExponent t.val).symm
  rw [hp]
  simp only [RootChoice.ReachesRoot]
  split_ifs <;> simp only [map_one, map_zero, mul_one, mul_zero]

/-- The weighted directed matrix-tree theorem for finite labeled
multigraphs, including loops and parallel edges. -/
theorem directed_matrix_tree (src tgt : E → V) (r : V) :
    (reducedLaplacian src tgt r).det = arborescencePolynomial src tgt r := by
  classical
  change Matrix.det (fun v w : {v : V // v ≠ r} =>
    ∑ e : {e : E // src e = v.val}, MvPolynomial.X e.val *
      ((if v.val = w.val then 1 else 0) - (if tgt e.val = w.val then 1 else 0))) = _
  rw [determinant_row_sum_dependent]
  rw [← (rootChoiceEquiv src r).sum_comp]
  change (∑ t : RootChoice src r, Matrix.det (fun v w : {v : V // v ≠ r} =>
    MvPolynomial.X (t.val v) *
      ((if v.val = w.val then 1 else 0) - (if tgt (t.val v) = w.val then 1 else 0)))) = _
  simp_rw [selected_row_determinant]
  unfold arborescencePolynomial
  symm
  apply Finset.sum_bij_ne_zero (fun (t : DirectedArborescence src tgt r) _ _ => t.val)
  · intros; exact Finset.mem_univ _
  · intros; apply Subtype.ext; assumption
  · intro t _ ht
    have htree : t.ReachesRoot tgt := by
      by_contra hn
      simp [hn] at ht
    refine ⟨⟨t, htree⟩, Finset.mem_univ _, ?_, rfl⟩
    simpa [htree] using ht
  · intro t _ _
    simp [t.property]

end Positivity
