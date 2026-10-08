import Positivity.CoverCoordinateChange

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

abbrev SplitFiber (a : α) := PUnit.{1} ⊕ {p : α // p ≠ a}

noncomputable def splitFiberEquiv (a : α) : α ≃ SplitFiber a :=
  (Equiv.subtypeNeSumPUnit a).symm.trans (Equiv.sumComm _ _)

/-- Coordinates consisting of a fiber constant and zero-sum coordinates. -/
noncomputable def fiberZeroSumBasis (a : α) : Matrix α (SplitFiber a) ℚ :=
  fun p c => match c with
    | Sum.inl _ => 1
    | Sum.inr q => (if p = q.val then 1 else 0) - (if p = a then 1 else 0)

noncomputable def fiberZeroSumBasisInv (a : α) : Matrix (SplitFiber a) α ℚ :=
  fun c p => match c with
    | Sum.inl _ => (Fintype.card α : ℚ)⁻¹
    | Sum.inr q => (if q.val = p then 1 else 0) - (Fintype.card α : ℚ)⁻¹

theorem fiberZeroSumBasis_left_inverse (a : α) :
    fiberZeroSumBasisInv a * fiberZeroSumBasis a = 1 := by
  classical
  have hn : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨a⟩)
  funext i j
  rw [Matrix.mul_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [fiberZeroSumBasisInv, fiberZeroSumBasis, Matrix.one_apply, hn]
    | inr j =>
      simp [fiberZeroSumBasisInv, fiberZeroSumBasis, mul_sub,
        Finset.sum_sub_distrib, Matrix.one_apply]
  | inr i =>
    cases j with
    | inl j =>
      simp [fiberZeroSumBasisInv, fiberZeroSumBasis, Finset.sum_sub_distrib,
        Matrix.one_apply, hn]
    | inr j =>
      simp [fiberZeroSumBasisInv, fiberZeroSumBasis, mul_sub, sub_mul,
        Finset.sum_sub_distrib, Matrix.one_apply, i.property, Subtype.ext_iff]

theorem fiberZeroSumBasis_right_inverse (a : α) :
    fiberZeroSumBasis a * fiberZeroSumBasisInv a = 1 := by
  classical
  exact (Matrix.mul_eq_one_comm_of_equiv (splitFiberEquiv a)).mpr (fiberZeroSumBasis_left_inverse a)

noncomputable def fullPullback (f : α → β) : Matrix α β ℚ :=
  fun p q => if f p = q then 1 else 0

theorem zeroSumPullback_reconstruction (a : α) (b : β) (f : α ≃ β)
    (p : α) (q : {q : β // q ≠ b}) :
    (∑ x : {x : α // x ≠ a},
      ((if p = x.val then (1 : ℚ) else 0) - (if p = a then 1 else 0)) *
        zeroSumPullback a b f x q) =
      (if f p = q.val then 1 else 0) - (if f p = b then 1 else 0) := by
  classical
  by_cases hp : p = a
  · subst p
    simp only [show ∀ x : {x : α // x ≠ a}, ¬ a = x.val from fun x => Ne.symm x.property,
      ite_false, ite_true, zero_sub, neg_one_mul, Finset.sum_neg_distrib, zeroSumPullback,
      Finset.sum_sub_distrib]
    rw [sum_nonreference_equiv_indicator, sum_nonreference_equiv_indicator]
    ring
  · simp only [hp, ite_false, sub_zero]
    rw [Finset.sum_eq_single (⟨p, hp⟩ : {x : α // x ≠ a})]
    · simp [zeroSumPullback]
    · intro x _ hxp
      have hpx : p ≠ x.val := fun h => hxp (Subtype.ext h.symm)
      simp [hpx]
    · simp

theorem fullPullback_zeroSumBasis (a : α) (b : β) (f : α ≃ β) :
    fullPullback f * fiberZeroSumBasis b =
      fiberZeroSumBasis a * Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} ℚ) 0 0
        (zeroSumPullback a b f) := by
  classical
  funext p c
  cases c with
  | inl c =>
    simp [Matrix.mul_apply, fullPullback, fiberZeroSumBasis, Fintype.sum_sum_type]
  | inr q =>
    simp only [Matrix.mul_apply, fullPullback, fiberZeroSumBasis, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add]
    rw [zeroSumPullback_reconstruction]
    simp [Finset.mul_sum, Finset.sum_ite_eq, mul_sub]

end Positivity
