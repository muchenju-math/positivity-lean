import Positivity.CoverCoordinateChange
import Positivity.DirectedArborescence

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

noncomputable def reducedTransition (r : V) (f : V → V) :
    Matrix {v : V // v ≠ r} {v : V // v ≠ r} ℤ :=
  fun v w => if f v.val = w.val then 1 else 0

theorem iterate_root (r : V) (f : V → V) (hf : f r = r) (n : ℕ) : f^[n] r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply, hf] using ih

theorem reducedTransition_pow (r : V) (f : V → V) (hf : f r = r) (n : ℕ)
    (v w : {v : V // v ≠ r}) :
    (reducedTransition r f ^ n) v w = if f^[n] v.val = w.val then 1 else 0 := by
  classical
  induction n generalizing v w with
  | zero => simp [Matrix.one_apply, Subtype.ext_iff]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [reducedTransition, ih]
    rw [sum_nonreference_delta r (f v.val)
      (fun x => if f^[n] x = w.val then (1 : ℤ) else 0)
      (by simp [iterate_root r f hf, Ne.symm w.property])]
    rw [Function.iterate_succ_apply]

theorem exists_uniform_root_iterate (r : V) (f : V → V) (hf : f r = r)
    (h : ∀ v, ∃ n : ℕ, f^[n] v = r) : ∃ n : ℕ, ∀ v, f^[n] v = r := by
  classical
  choose n hn using h
  refine ⟨Finset.univ.sup n, ?_⟩
  intro v
  have hle : n v ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ v)
  rw [← Nat.sub_add_cancel hle, Function.iterate_add_apply, hn, iterate_root r f hf]

theorem reducedTransition_nilpotent (r : V) (f : V → V) (hf : f r = r)
    (h : ∀ v, ∃ n : ℕ, f^[n] v = r) : IsNilpotent (reducedTransition r f) := by
  obtain ⟨n, hn⟩ := exists_uniform_root_iterate r f hf h
  refine ⟨n, ?_⟩
  funext v w
  rw [reducedTransition_pow r f hf n, hn]
  simp [Ne.symm w.property]

theorem det_one_sub_of_nilpotent_int {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℤ) (h : IsNilpotent M) : (1 - M).det = 1 := by
  have hc := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have he : M.charpoly = Polynomial.X ^ Fintype.card I := sub_eq_zero.mp hc.eq_zero
  have hv := congrArg (Polynomial.eval (1 : ℤ)) he
  simpa [Matrix.eval_charpoly] using hv

theorem reaches_next_iff (r : V) (f : V → V) (hf : f r = r) (v : V) :
    (∃ n : ℕ, f^[n] (f v) = r) ↔ ∃ n : ℕ, f^[n] v = r := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [Function.iterate_succ_apply] using hn⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      change v = r at hn
      subst v
      exact ⟨0, hf⟩
    | succ n => exact ⟨n, by simpa only [Function.iterate_succ_apply] using hn⟩

theorem reducedTransition_det_of_not_reaches (r : V) (f : V → V) (hf : f r = r)
    (h : ¬ ∀ v, ∃ n : ℕ, f^[n] v = r) : (1 - reducedTransition r f).det = 0 := by
  classical
  push_neg at h
  obtain ⟨v, hv⟩ := h
  have hvr : v ≠ r := by intro he; exact hv 0 he
  let g : V → ℤ := fun v => if ∃ n : ℕ, f^[n] v = r then 0 else 1
  have hgr : g r = 0 := by simp only [g, if_pos (show ∃ n : ℕ, f^[n] r = r from ⟨0, rfl⟩)]
  have hgf (x : V) : g (f x) = g x := by
    simp only [g, reaches_next_iff r f hf x]
  have hmul : Matrix.mulVec (1 - reducedTransition r f) (fun w : {w : V // w ≠ r} => g w.val) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    funext w
    change g w.val - (∑ z : {z : V // z ≠ r},
      (if f w.val = z.val then (1 : ℤ) else 0) * g z.val) = 0
    rw [sum_nonreference_delta r (f w.val) g hgr, hgf, sub_self]
  by_contra hdet
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have hzv := congrFun hz (⟨v, hvr⟩ : {v : V // v ≠ r})
  simp [g, hv] at hzv

/-- A selected functional digraph contributes determinant one exactly
when every path reaches the root, and contributes zero otherwise. -/
theorem reducedTransition_det (r : V) (f : V → V) (hf : f r = r) :
    (1 - reducedTransition r f).det = if ∀ v, ∃ n : ℕ, f^[n] v = r then 1 else 0 := by
  classical
  split_ifs with h
  · exact det_one_sub_of_nilpotent_int _ (reducedTransition_nilpotent r f hf h)
  · exact reducedTransition_det_of_not_reaches r f hf h

end Positivity
