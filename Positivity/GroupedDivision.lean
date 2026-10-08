import Positivity.GroupedSquarefree

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {A B R K : Type*} [Fintype A] [Fintype B] [CommSemiring R] [Field K]

theorem coeff_groupedEvaluation_division (f : R →+* K) (w : B → K)
    (s : K) (hs : s ≠ 0) (d : ℕ) (hd : Fintype.card A ≤ d)
    (P : MvPolynomial (A × B) R) :
    (MvPolynomial.C (s ^ d) *
      groupedEvaluation (fun ab : A × B => w ab.2 / s) (P.map f)).coeff squarefreeExponent =
    ∑ τ : A → B, s ^ (d - Fintype.card A) *
      f (P.coeff (choiceExponent (fun a => (a, τ a)))) * ∏ a, w (τ a) := by
  classical
  rw [MvPolynomial.coeff_C_mul, coeff_groupedEvaluation_squarefree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [MvPolynomial.coeff_map, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hp : s ^ d = s ^ (d - Fintype.card A) * s ^ Fintype.card A := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  rw [hp]
  field_simp

end Positivity
