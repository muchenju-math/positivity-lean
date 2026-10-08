import Positivity.LoopContraction
import Positivity.NormalizedPullback
import Positivity.DirectionalDeterminant

namespace Positivity
open FiniteFiberSystem
variable {V E : Type*} [Fintype V] [Fintype E]

/-- The class of the point indicator in reference coordinates. In particular,
the reference point gives minus the all-ones vector on its fiber. -/
noncomputable def quotientPointClass (F : FiniteFiberSystem V E) (u : V)
    (p : F.Fiber u) (i : F.Coord) : ℤ := by
  classical
  exact if h : i.1 = u then
    (if p = h ▸ i.2.val then 1 else 0) - (if p = F.reference u then 1 else 0)
    else 0

/-- The functional taking the difference of two values in one fiber. -/
noncomputable def quotientValueDifference (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (j : F.Coord) : ℤ := by
  classical
  exact if h : j.1 = u then
    (if p = h ▸ j.2.val then 1 else 0) - (if q = h ▸ j.2.val then 1 else 0)
    else 0

theorem quotientEdgeCoefficient_loop_global (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e) (i j : F.Coord) :
    F.quotientEdgeCoefficient e i j =
      @Finset.sum (F.Fiber (F.src e)) ℤ _ (@Finset.univ _ (F.fiberFintype _))
        (fun p => quotientPointClass F (F.src e) p i *
          quotientValueDifference F (F.src e) p (F.loopTargetInSource e he p) j) := by
  classical
  letI := F.fiberFintype (F.src e)
  obtain ⟨v, i⟩ := i
  obtain ⟨w, j⟩ := j
  by_cases hv : v = F.src e
  · subst v
    by_cases hw : w = F.src e
    · subst w
      simpa only [quotientPointClass, quotientValueDifference, dite_true] using
        F.quotientEdgeCoefficient_loop_rankOne_sum e he i j
    · have hij : (⟨F.src e, i⟩ : F.Coord) ≠ ⟨w, j⟩ := by
        intro h
        exact hw (congrArg Sigma.fst h).symm
      simp [quotientEdgeCoefficient, hij, ← he, hw, quotientValueDifference]
  · have hij : (⟨v, i⟩ : F.Coord) ≠ ⟨w, j⟩ ∨ v = w := by
      by_cases h : v = w
      · exact Or.inr h
      · exact Or.inl (fun h' => h (congrArg Sigma.fst h'))
    simp [quotientEdgeCoefficient, hv, Ne.symm hv, quotientPointClass]

theorem quotientValueDifference_pointClass (F : FiniteFiberSystem V E)
    (u : V) (p q : F.Fiber u) (hpq : p ≠ q) :
    (∑ i : F.Coord, quotientValueDifference F u p q i * quotientPointClass F u p i) = 1 := by
  classical
  letI := F.fiberFintype u
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single u]
  · simp only [quotientValueDifference, quotientPointClass, dite_true]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    rw [sum_nonreference_delta (F.reference u) p
        (fun x => (if p = x then (1 : ℤ) else 0) - (if p = F.reference u then 1 else 0)) (by simp),
      sum_nonreference_delta (F.reference u) q
        (fun x => (if p = x then (1 : ℤ) else 0) - (if p = F.reference u then 1 else 0)) (by simp)]
    simp [hpq]
  · intro v hv hvu
    simp [quotientValueDifference, hvu]
  · simp

/-- Differentiation along a base loop is the sum of its lifted rank-one
directions, including lifts whose source is the chosen reference point. -/
theorem pderiv_quotientDeterminant_loop_directions (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e) :
    MvPolynomial.pderiv e F.quotientDeterminant =
      @Finset.sum (F.Fiber (F.src e)) (MvPolynomial E ℤ) _
        (@Finset.univ _ (F.fiberFintype _))
        (fun p => rankOneDetCoefficient F.quotientLaplacian
          (fun i => MvPolynomial.C (quotientPointClass F (F.src e) p i))
          (fun j => MvPolynomial.C
            (quotientValueDifference F (F.src e) p (F.loopTargetInSource e he p) j))) := by
  classical
  letI := F.fiberFintype (F.src e)
  rw [pderiv_quotientDeterminant_rows]
  have hentry (i j : F.Coord) :
      (MvPolynomial.C (F.quotientEdgeCoefficient e i j) : MvPolynomial E ℤ) =
        ∑ p : F.Fiber (F.src e),
          MvPolynomial.C (quotientPointClass F (F.src e) p i) *
            MvPolynomial.C (quotientValueDifference F (F.src e) p
              (F.loopTargetInSource e he p) j) := by
    rw [quotientEdgeCoefficient_loop_global F e he i j, map_sum]
    simp only [map_mul]
  simp_rw [hentry]
  exact det_row_sum_rankOne F.quotientLaplacian _ _

noncomputable def loopDirectionCoefficient (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e) (p : F.Fiber (F.src e)) : MvPolynomial E ℤ :=
  rankOneDetCoefficient F.quotientLaplacian
    (fun i => MvPolynomial.C (quotientPointClass F (F.src e) p i))
    (fun j => MvPolynomial.C
      (quotientValueDifference F (F.src e) p (F.loopTargetInSource e he p) j))

theorem loopDirectionCoefficient_fixed (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p = F.loopTargetInSource e he p) : loopDirectionCoefficient F e he p = 0 := by
  classical
  unfold loopDirectionCoefficient rankOneDetCoefficient
  apply Finset.sum_eq_zero
  intro i hi
  have hz : (F.quotientLaplacian.updateRow i (fun j =>
      MvPolynomial.C (quotientValueDifference F (F.src e) p
        (F.loopTargetInSource e he p) j))).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    simp [quotientValueDifference, ← hp]
  rw [hz, mul_zero]

theorem pderiv_quotientDeterminant_moved_directions (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e) :
    letI := Classical.decEq (F.Fiber (F.src e))
    letI := F.fiberFintype (F.src e)
    MvPolynomial.pderiv e F.quotientDeterminant =
      ∑ p : {p : F.Fiber (F.src e) // p ≠ F.loopTargetInSource e he p},
        loopDirectionCoefficient F e he p := by
  classical
  letI := F.fiberFintype (F.src e)
  change MvPolynomial.pderiv e F.quotientDeterminant = _
  rw [pderiv_quotientDeterminant_loop_directions]
  change (∑ p : F.Fiber (F.src e), loopDirectionCoefficient F e he p) = _
  have hz : (∑ p : {p : F.Fiber (F.src e) // ¬p ≠ F.loopTargetInSource e he p},
      loopDirectionCoefficient F e he p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    exact loopDirectionCoefficient_fixed F e he p (not_ne_iff.mp p.property)
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun p : F.Fiber (F.src e) => p ≠ F.loopTargetInSource e he p)
    (loopDirectionCoefficient F e he)
  rw [hz, add_zero] at h
  exact h.symm


end Positivity
