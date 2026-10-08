import Positivity.ReferenceContractionMatrix
import Positivity.MainTheorem

namespace Positivity
open FiniteFiberSystem
variable {V E : Type*} [Fintype V] [Fintype E]

theorem loopDirectionCoefficient_eq_contraction_reference
    (F : FiniteFiberSystem V E) (e : E) (he : F.src e = F.tgt e)
    (hpq : F.reference (F.src e) ≠ F.loopTargetInSource e he (F.reference (F.src e))) :
    loopDirectionCoefficient F e he (F.reference (F.src e)) =
      (F.contractMovedEdge (F.src e) (F.reference (F.src e))
        (F.loopTargetInSource e he (F.reference (F.src e))) hpq).quotientDeterminant := by
  rw [loopDirectionCoefficient_reference_compression F e he hpq]
  exact (F.contractMovedEdge_quotientDeterminant_reference (F.src e)
    (F.loopTargetInSource e he (F.reference (F.src e))) hpq).symm

theorem loopDirectionCoefficient_eq_contraction
    (F : FiniteFiberSystem V E) (e : E) (he : F.src e = F.tgt e)
    (p : F.Fiber (F.src e)) (hpq : p ≠ F.loopTargetInSource e he p) :
    loopDirectionCoefficient F e he p =
      (F.contractMovedEdge (F.src e) p (F.loopTargetInSource e he p) hpq).quotientDeterminant := by
  classical
  by_cases hp : p = F.reference (F.src e)
  · subst p
    exact loopDirectionCoefficient_eq_contraction_reference F e he hpq
  · exact loopDirectionCoefficient_eq_contraction_nonreference F e he p hp hpq

/-- The loop derivative identity needed for the coefficient recurrence.
All base-edge labels are retained in each contracted determinant. -/
theorem loopDeterminantDerivative (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e) :
    MvPolynomial.pderiv e F.quotientDeterminant =
      ∑ p : LoopChildIndex F e he,
        (F.contractMovedEdge (F.src e) p.val
          (F.loopTargetInSource e he p.val) p.property).quotientDeterminant := by
  classical
  have h := pderiv_quotientDeterminant_moved_directions F e he
  change MvPolynomial.pderiv e F.quotientDeterminant =
    ∑ p : LoopChildIndex F e he, loopDirectionCoefficient F e he p.val at h
  rw [h]
  apply Finset.sum_congr rfl
  intro p hp
  exact loopDirectionCoefficient_eq_contraction F e he p.val p.property

/-- The squarefree loop recurrence, with the base loop removed after
contracting each moved lift. -/
theorem loopCoefficientRecurrence (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e) :
    F.quotientDeterminant.coeff squarefreeExponent =
      ∑ p : LoopChildIndex F e he,
        (F.contractLoopEdge e he p.val p.property).quotientDeterminant.coeff squarefreeExponent := by
  exact loopCoefficientRecurrence_of_derivative_identity F e he (loopDeterminantDerivative F e he)

end Positivity
