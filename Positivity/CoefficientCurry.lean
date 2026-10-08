import Positivity.MainTheorem

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]

theorem coeff_sumRingEquiv_finsupp (P : MvPolynomial (A ⊕ B) R) (a : A →₀ ℕ) (b : B →₀ ℕ) :
    ((MvPolynomial.sumRingEquiv R A B P).coeff a).coeff b =
      P.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b)) := by
  exact coeff_sumRingEquiv P a b

theorem squarefree_sumFinsupp :
    Finsupp.sumFinsuppAddEquivProdFinsupp.symm
      (squarefreeExponent (E := A), squarefreeExponent (E := B)) =
        squarefreeExponent (E := A ⊕ B) := by
  ext x
  cases x <;> rfl

theorem coeff_sumRingEquiv_squarefree (P : MvPolynomial (A ⊕ B) R) :
    ((MvPolynomial.sumRingEquiv R A B P).coeff squarefreeExponent).coeff squarefreeExponent =
      P.coeff squarefreeExponent := by
  rw [coeff_sumRingEquiv_finsupp, squarefree_sumFinsupp]

end Positivity
