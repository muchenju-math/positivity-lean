import Mathlib

namespace Positivity
variable {α β κ K : Type*} [Fintype α] [Fintype β] [Fintype κ] [Field K]

/-- Distributing a Schur complement across incoming/outgoing pairs. -/
theorem schurWeightExpansion (wa : α → K) (wb : β → K)
    (A : α → K) (C : α → κ → K) (B : β → κ → K)
    (hs : (∑ b, wb b) ≠ 0) :
    (∑ a, wa a * A a) - (∑ b, wb b)⁻¹ *
        (∑ k, (∑ a, wa a * C a k) * (∑ b, wb b * B b k)) =
      ∑ a, ∑ b, (wa a * wb b / (∑ b, wb b)) *
        (A a - ∑ k, C a k * B b k) := by
  classical
  let s := ∑ b, wb b
  have hfirst (a : α) : (∑ b, (wa a * wb b / s) * A a) = wa a * A a := by
    calc
      _ = (wa a * A a / s) * (∑ b, wb b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = _ := by change (wa a * A a / s) * s = _; exact div_mul_cancel₀ _ hs
  have hsecond : (∑ a, ∑ b, (wa a * wb b / s) * (∑ k, C a k * B b k)) =
      s⁻¹ * (∑ k, (∑ a, wa a * C a k) * (∑ b, wb b * B b k)) := by
    calc
      _ = ∑ a, ∑ b, ∑ k, (wa a * wb b / s) * (C a k * B b k) := by
        simp only [Finset.mul_sum]
      _ = ∑ a, ∑ k, ∑ b, (wa a * wb b / s) * (C a k * B b k) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, (wa a * wb b / s) * (C a k * B b k) := Finset.sum_comm
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
  symm
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [show (∑ b, wb b) = s from rfl]
  simp_rw [hfirst]
  rw [hsecond]

end Positivity
