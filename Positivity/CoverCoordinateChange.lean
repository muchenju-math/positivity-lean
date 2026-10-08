import Positivity.NormalizedPullback

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {α β R : Type*} [Fintype α] [Fintype β] [CommRing R]

theorem sum_nonreference_add_reference (a : α) (f : α → R) :
    (∑ x : {x : α // x ≠ a}, f x) + f a = ∑ x : α, f x := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun x : α => x ≠ a) f
  have hz : (∑ x : {x : α // ¬ x ≠ a}, f x) = f a := by
    rw [Finset.sum_eq_single (⟨a, by simp⟩ : {x : α // ¬ x ≠ a})]
    · intro x _ hx
      exact False.elim (hx (Subtype.ext (not_ne_iff.mp x.property)))
    · simp
  rw [hz] at h
  exact h

noncomputable def referenceShiftMatrix (a : α) :
    Matrix {x : α // x ≠ a} {x : α // x ≠ a} R :=
  1 + Matrix.of (fun _ _ => 1)

/-- Pullback in coordinates on the zero-sum subspace of a fiber. -/
noncomputable def zeroSumPullback (a : α) (b : β) (f : α ≃ β) :
    Matrix {x : α // x ≠ a} {y : β // y ≠ b} R :=
  fun x y => (if f x.val = y.val then 1 else 0) - (if f x.val = b then 1 else 0)

theorem sum_nonreference_indicator (a x : α) :
    (∑ y : {y : α // y ≠ a}, if x = y.val then (1 : R) else 0) =
      1 - (if x = a then 1 else 0) := by
  have h := sum_nonreference_add_reference a (fun y => if x = y then (1 : R) else 0)
  simpa using eq_sub_of_add_eq (by simpa using h)

theorem sum_nonreference_equiv_indicator (a : α) (f : α ≃ β) (y : β) :
    (∑ x : {x : α // x ≠ a}, if f x.val = y then (1 : R) else 0) =
      1 - (if f a = y then 1 else 0) := by
  have h := sum_nonreference_add_reference a (fun x => if f x = y then (1 : R) else 0)
  rw [f.sum_comp (fun z : β => if z = y then (1 : R) else 0)] at h
  simpa using eq_sub_of_add_eq (by simpa using h)

theorem normalizedPullback_referenceShift (a : α) (b : β) (f : α ≃ β) :
    (normalizedPullback a b f : Matrix _ _ R) * referenceShiftMatrix b =
      referenceShiftMatrix a * zeroSumPullback a b f := by
  classical
  rw [referenceShiftMatrix, Matrix.mul_add, Matrix.mul_one,
    referenceShiftMatrix, Matrix.add_mul, Matrix.one_mul]
  funext x y
  change normalizedPullback (R := R) a b f x y +
    (∑ z : {z : β // z ≠ b}, normalizedPullback (R := R) a b f x z * 1) =
    zeroSumPullback (R := R) a b f x y +
      ∑ z : {z : α // z ≠ a}, 1 * zeroSumPullback (R := R) a b f z y
  simp only [normalizedPullback, zeroSumPullback, mul_one, one_mul, Finset.sum_sub_distrib]
  rw [sum_nonreference_indicator, sum_nonreference_indicator,
    sum_nonreference_equiv_indicator, sum_nonreference_equiv_indicator]
  ring

theorem referenceShiftMatrix_det (a : α) :
    (referenceShiftMatrix (R := R) a).det = (Fintype.card α : R) := by
  classical
  have hones : (Matrix.of (fun _ _ => (1 : R)) : Matrix {x : α // x ≠ a} {x : α // x ≠ a} R) =
      Matrix.replicateCol PUnit.{1} (fun _ => (1 : R)) * Matrix.replicateRow PUnit.{1} (fun _ => (1 : R)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [referenceShiftMatrix, hones, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hc : Fintype.card {x : α // x ≠ a} + 1 = Fintype.card α := by
    have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
    simp only [Fintype.card_subtype_compl, Fintype.card_unique]
    omega
  rw [add_comm, ← Nat.cast_one, ← Nat.cast_add, hc]

end Positivity
