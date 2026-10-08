import Mathlib

namespace Positivity
variable {α β γ R : Type*} [Fintype β] [DecidableEq β] [CommRing R]

/-- The matrix of pullback on functions modulo constants. -/
noncomputable def normalizedPullback (a : α) (b : β) (f : α → β) :
    Matrix {x : α // x ≠ a} {y : β // y ≠ b} R := by
  classical
  exact fun x y => (if f x = y then 1 else 0) - (if f a = y then 1 else 0)

theorem sum_nonreference_delta (b x : β) (h : β → R) (hb : h b = 0) :
    (∑ y : {y : β // y ≠ b}, (if x = y then (1 : R) else 0) * h y) = h x := by
  classical
  by_cases hx : x = b
  · subst x
    rw [hb]
    apply Finset.sum_eq_zero
    intro y hy
    simp [Ne.symm y.property]
  · rw [Finset.sum_eq_single (⟨x, hx⟩ : {y : β // y ≠ b})]
    · simp
    · intro y hy hyx
      have hxy : x ≠ y := fun h => hyx (Subtype.ext h.symm)
      simp [hxy]
    · simp

theorem normalizedPullback_comp [DecidableEq γ] (a : α) (b : β) (c : γ)
    (f : α → β) (g : β → γ) :
    (normalizedPullback a b f : Matrix _ _ R) * normalizedPullback b c g =
      normalizedPullback (R := R) a c (g ∘ f) := by
  classical
  ext x z
  change (∑ y : {y : β // y ≠ b},
    ((if f x = y then (1 : R) else 0) - (if f a = y then 1 else 0)) *
    ((if g y = z then (1 : R) else 0) - (if g b = z then 1 else 0))) =
    (if g (f x) = z then 1 else 0) - (if g (f a) = z then 1 else 0)
  rw [Finset.sum_congr rfl (fun y _ => sub_mul _ _ _), Finset.sum_sub_distrib]
  rw [sum_nonreference_delta b (f x)
      (fun y => (if g y = z then (1 : R) else 0) - (if g b = z then 1 else 0)) (by simp),
    sum_nonreference_delta b (f a)
      (fun y => (if g y = z then (1 : R) else 0) - (if g b = z then 1 else 0)) (by simp)]
  ring

theorem normalizedPullback_id (b : β) :
    normalizedPullback (R := R) b b id = 1 := by
  classical
  ext x y
  change (if x.val = y.val then (1 : R) else 0) -
    (if b = y.val then 1 else 0) = if x = y then 1 else 0
  simp [Ne.symm y.property, Subtype.ext_iff]

theorem normalizedPullback_change_reference [Fintype α] [DecidableEq α]
    (a a' : α) (b b' : β) (f : α → β) :
    normalizedPullback (R := R) a a' id * normalizedPullback (R := R) a' b' f *
      normalizedPullback (R := R) b' b id = normalizedPullback (R := R) a b f := by
  have h := normalizedPullback_comp (R := R) a a' b' id f
  have h' := normalizedPullback_comp (R := R) a b' b (f ∘ id) id
  exact (congrArg (fun (M : Matrix {x : α // x ≠ a} {y : β // y ≠ b'} R) =>
    (M * normalizedPullback (R := R) b' b id : Matrix _ _ R)) h).trans h'

theorem normalizedPullback_reference_inverse (b b' : β) :
    normalizedPullback (R := R) b b' id * normalizedPullback (R := R) b' b id = 1 := by
  exact (normalizedPullback_comp (R := R) b b' b id id).trans (normalizedPullback_id b)

end Positivity
