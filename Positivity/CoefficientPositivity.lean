import Positivity.LoopRecurrence
import Positivity.EliminationRecurrence

namespace Positivity
open FiniteFiberSystem

/-- Every balanced finite-fiber system has a nonnegative squarefree
coefficient. Both recurrences used in the dimension induction are proved. -/
theorem balancedCoefficient_nonnegative
    {V E : Type*} [Fintype V] [Fintype E]
    (F : FiniteFiberSystem V E) (hF : F.Balanced) :
    0 ≤ balancedCoefficient F := by
  classical
  apply balancedCoefficient_nonnegative_of_recurrences
    (fun G _ e he => loopCoefficientRecurrence G e he)
    (fun G hG hloop u hu hle => eliminationCoefficientRecurrence G hG hloop u hu hle)
    F hF

/-- Coefficient positivity for arbitrary finite-fiber systems (Theorem 2.3).
No balance, bijectivity, or recurrence hypotheses are required. -/
theorem quotientDeterminant_coeff_nonnegative
    {V E : Type*} [Fintype V] [Fintype E]
    (F : FiniteFiberSystem V E) (α : E →₀ ℕ) :
    0 ≤ F.quotientDeterminant.coeff α := by
  classical
  have h := quotientDeterminant_coeff_nonneg_of_balancedCoefficient_nonneg_auto F
    (fun β hβ => balancedCoefficient_nonnegative (F.polarize β) hβ) α
  have he : exponentOfFunction α = α := by ext e; rfl
  simpa only [he] using h

end Positivity
