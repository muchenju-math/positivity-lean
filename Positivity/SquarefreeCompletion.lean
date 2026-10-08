import Positivity.MainTheorem

namespace Positivity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {B R : Type*} [Fintype B] [CommSemiring R]

/-- Completing any squarefree monomial with a power of the sum of all
variables gives the factorial of the number of missing variables. -/
theorem coeff_squarefree_completion (d : B →₀ ℕ)
    (hd : d ≤ squarefreeExponent) :
    ((MvPolynomial.monomial d (1 : R)) *
      (∑ b : B, MvPolynomial.X b) ^
        (Fintype.card B - d.sum (fun _ n => n))).coeff squarefreeExponent =
      (Nat.factorial (Fintype.card B - d.sum (fun _ n => n)) : R) := by
  classical
  let m := squarefreeExponent (E := B) - d
  have hm (b : B) : m b ≤ 1 := by
    simp [m, Finsupp.tsub_apply, squarefreeExponent]
  have hsum : m.sum (fun _ n => n) = Fintype.card B - d.sum (fun _ n => n) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype d _ (by simp)]
    change (∑ b : B, (1 - d b)) = Fintype.card B - ∑ b : B, d b
    rw [Finset.sum_tsub_distrib]
    · simp
    · intro b _
      simpa [squarefreeExponent] using hd b
  have hprod : m.prod (fun _ n => n.factorial) = 1 := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    apply Finset.prod_eq_one
    intro b _
    have := hm b
    interval_cases m b <;> rfl
  rw [MvPolynomial.coeff_monomial_mul', if_pos hd, one_mul,
    MvPolynomial.coeff_sum_X_pow_of_fintype]
  change ((if m.sum (fun _ n => n) = _ then m.multinomial else 0 : ℕ) : R) = _
  rw [if_pos hsum]
  congr 1
  unfold Finsupp.multinomial
  change Nat.factorial (m.sum (fun _ n => n)) / m.prod (fun _ n => n.factorial) = _
  rw [hsum, hprod, Nat.div_one]

variable {A : Type*} [Fintype A]

noncomputable def choiceExponent (τ : A → B) : B →₀ ℕ :=
  ∑ a, Finsupp.single (τ a) 1

theorem choiceExponent_sum (τ : A → B) :
    (choiceExponent τ).sum (fun _ n => n) = Fintype.card A := by
  classical
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [choiceExponent, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp

theorem choiceExponent_le_squarefree_iff (τ : A → B) :
    choiceExponent τ ≤ squarefreeExponent ↔ Function.Injective τ := by
  classical
  constructor
  · intro hd a a' heq
    by_contra hn
    have hsub : ({a, a'} : Finset A) ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset hsub (f := fun x => (Finsupp.single (τ x) 1 : B →₀ ℕ) (τ a))
    have htwo : 2 ≤ choiceExponent τ (τ a) := by
      simpa [choiceExponent, Finsupp.finsetSum_apply, hn, heq] using hle
    have hone : choiceExponent τ (τ a) ≤ 1 := by
      simpa [squarefreeExponent] using hd (τ a)
    omega
  · intro hτ b
    by_cases hb : b ∈ Set.range τ
    · obtain ⟨a, rfl⟩ := hb
      have hval : choiceExponent τ (τ a) = 1 := by
        simp only [choiceExponent, Finsupp.finsetSum_apply, Finsupp.single_apply]
        simp [hτ.eq_iff]
      simpa [squarefreeExponent, hval]
    · have hval : choiceExponent τ b = 0 := by
        simp only [choiceExponent, Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro a _
        exact Finsupp.single_eq_of_ne (fun h => hb ⟨a, h.symm⟩)
      simp [hval, squarefreeExponent]

/-- Repeated outgoing choices contribute zero; injective choices contribute
the factorial of the number of unused outgoing labels. -/
theorem coeff_choice_completion (τ : A → B) :
    (MvPolynomial.monomial (choiceExponent τ) (1 : R) *
      (∑ b : B, MvPolynomial.X b) ^ (Fintype.card B - Fintype.card A)).coeff
      squarefreeExponent =
      if Function.Injective τ then
        (Nat.factorial (Fintype.card B - Fintype.card A) : R) else 0 := by
  classical
  by_cases hτ : Function.Injective τ
  · rw [if_pos hτ]
    simpa only [choiceExponent_sum] using
      (coeff_squarefree_completion (R := R) (choiceExponent τ)
        ((choiceExponent_le_squarefree_iff τ).mpr hτ))
  · rw [if_neg hτ, MvPolynomial.coeff_monomial_mul',
      if_neg (fun h => hτ ((choiceExponent_le_squarefree_iff τ).mp h))]

end Positivity
