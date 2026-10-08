import Positivity.DirectedArborescence

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {E : Type*}

theorem constant_relPrime_of_primitive (A : MvPolynomial E ℤ) (k : ℤ) (hk : k ≠ 0)
    (hprim : ∀ d : ℤ, (∀ α, d ∣ A.coeff α) → IsUnit d) :
    IsRelPrime (MvPolynomial.C k) A := by
  intro D hD hA
  obtain ⟨d, _, rfl⟩ := (MvPolynomial.dvd_C_iff_exists hk).mp hD
  exact (hprim d ((MvPolynomial.C_dvd_iff_dvd_coeff d A).mp hA)).map MvPolynomial.C

/-- The primitive base tree polynomial forces the positive normalized
determinant to have integer coefficients. -/
theorem primitive_positive_quotient (A P B : MvPolynomial E ℤ)
    (k : ℕ) (hk : 0 < k)
    (hprim : ∀ d : ℤ, (∀ α, d ∣ A.coeff α) → IsUnit d)
    (hid : MvPolynomial.C (k : ℤ) * B = A * P)
    (hP : ∀ α, 0 ≤ P.coeff α) :
    ∃ Q : MvPolynomial E ℤ, A * Q = B ∧ P = MvPolynomial.C (k : ℤ) * Q ∧
      ∀ α, 0 ≤ Q.coeff α := by
  have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hrel := constant_relPrime_of_primitive A (k : ℤ) hkz hprim
  have hd : MvPolynomial.C (k : ℤ) ∣ P :=
    hrel.dvd_of_dvd_mul_left ⟨B, hid.symm⟩
  obtain ⟨Q, hQ⟩ := hd
  refine ⟨Q, ?_, hQ, ?_⟩
  · have hne : (MvPolynomial.C (k : ℤ) : MvPolynomial E ℤ) ≠ 0 := by
      simpa using hkz
    apply mul_left_cancel₀ hne
    rw [mul_left_comm, ← hQ, ← hid]
  · intro α
    have hα := hP α
    rw [hQ, MvPolynomial.coeff_C_mul] at hα
    have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
    exact nonneg_of_mul_nonneg_right hα hkpos

end Positivity
