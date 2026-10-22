import Positivity.LoopRecurrence

/-!
# The loop derivative with a scalar parameter

Lemma 3.2 of the manuscript dated 2026-10-22 concerns `det (z I + Q_F)`.
The older `loopDeterminantDerivative` is its specialization at `z = 0`.
Here `z` lies in the coefficient ring, so edge differentiation fixes it.
Taking `R = Polynomial ℤ` and `z = Polynomial.X` gives the stated identity
with an independent indeterminate.
-/

namespace Positivity
open FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E R : Type*} [Fintype V] [Fintype E] [CommRing R]

noncomputable def edgeCoefficientMap : MvPolynomial E ℤ →+* MvPolynomial E R :=
  MvPolynomial.map (Int.castRingHom R)

omit [Fintype E] in
@[simp] theorem edgeCoefficientMap_C (a : ℤ) :
    edgeCoefficientMap (E := E) (R := R) (MvPolynomial.C a) = MvPolynomial.C (a : R) := by
  simp [edgeCoefficientMap]

/-- The matrix of `z I + Q_F`, with `z` fixed by edge differentiation. -/
noncomputable def shiftedQuotientLaplacian (F : FiniteFiberSystem V E) (z : R) :
    Matrix F.Coord F.Coord (MvPolynomial E R) := by
  classical
  exact fun i j => edgeCoefficientMap (F.quotientLaplacian i j) +
    if i = j then MvPolynomial.C z else 0

noncomputable def shiftedQuotientDeterminant (F : FiniteFiberSystem V E) (z : R) :
    MvPolynomial E R := (shiftedQuotientLaplacian F z).det

theorem shiftedQuotientLaplacian_pderiv (F : FiniteFiberSystem V E) (z : R)
    (e : E) (i j : F.Coord) :
    MvPolynomial.pderiv e (shiftedQuotientLaplacian F z i j) =
      MvPolynomial.C (F.quotientEdgeCoefficient e i j : R) := by
  classical
  by_cases hij : i = j <;>
    simp [shiftedQuotientLaplacian, edgeCoefficientMap, quotientLaplacian,
      MvPolynomial.pderiv_X, Pi.single_apply, hij]

noncomputable def shiftedLoopDirection (F : FiniteFiberSystem V E) (z : R)
    (e : E) (he : F.src e = F.tgt e) (p : F.Fiber (F.src e)) : MvPolynomial E R :=
  rankOneDetCoefficient (shiftedQuotientLaplacian F z)
    (fun i => MvPolynomial.C (quotientPointClass F (F.src e) p i : R))
    (fun j => MvPolynomial.C
      (quotientValueDifference F (F.src e) p (F.loopTargetInSource e he p) j : R))

theorem shiftedQuotientDeterminant_loop_directions (F : FiniteFiberSystem V E) (z : R)
    (e : E) (he : F.src e = F.tgt e) :
    letI := F.fiberFintype (F.src e)
    MvPolynomial.pderiv e (shiftedQuotientDeterminant F z) =
      ∑ p : F.Fiber (F.src e), shiftedLoopDirection F z e he p := by
  classical
  let := F.fiberFintype (F.src e)
  unfold shiftedQuotientDeterminant
  rw [derivation_det_rows]
  simp_rw [shiftedQuotientLaplacian_pderiv]
  have hentry (i j : F.Coord) :
      (MvPolynomial.C (F.quotientEdgeCoefficient e i j : R) : MvPolynomial E R) =
        ∑ p : F.Fiber (F.src e),
          MvPolynomial.C (quotientPointClass F (F.src e) p i : R) *
            MvPolynomial.C (quotientValueDifference F (F.src e) p
              (F.loopTargetInSource e he p) j : R) := by
    rw [quotientEdgeCoefficient_loop_global F e he i j]
    simp only [Int.cast_sum, Int.cast_mul, map_sum, map_mul]
  simp_rw [hentry]
  exact det_row_sum_rankOne (shiftedQuotientLaplacian F z) _ _

theorem shiftedLoopDirection_fixed (F : FiniteFiberSystem V E) (z : R)
    (e : E) (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p = F.loopTargetInSource e he p) : shiftedLoopDirection F z e he p = 0 := by
  classical
  unfold shiftedLoopDirection rankOneDetCoefficient
  apply Finset.sum_eq_zero
  intro i _
  have hz : ((shiftedQuotientLaplacian F z).updateRow i (fun j =>
      MvPolynomial.C (quotientValueDifference F (F.src e) p
        (F.loopTargetInSource e he p) j : R))).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    simp [quotientValueDifference, ← hp]
  rw [hz, mul_zero]

theorem shiftedContraction_nonreference (F : FiniteFiberSystem V E) (z : R)
    (u : V) (p q : F.Fiber u) (hpq : p ≠ q) (hp : p ≠ F.reference u) :
    shiftedQuotientDeterminant (F.contractMovedEdge u p q hpq) z =
      Matrix.det (fun i j : {i : F.Coord // i ≠ ⟨u, p, hp⟩} =>
        shiftedQuotientLaplacian F z i j -
          shiftedQuotientLaplacian F z i ⟨u, p, hp⟩ *
            MvPolynomial.C (quotientValueDifference F u p q j : R)) := by
  classical
  let B : Matrix {i : F.Coord // i ≠ ⟨u, p, hp⟩}
      {i : F.Coord // i ≠ ⟨u, p, hp⟩} (MvPolynomial E R) := fun i j =>
    shiftedQuotientLaplacian F z i j -
      shiftedQuotientLaplacian F z i ⟨u, p, hp⟩ *
        MvPolynomial.C (quotientValueDifference F u p q j : R)
  change (shiftedQuotientLaplacian (F.contractMovedEdge u p q hpq) z).det = B.det
  rw [← Matrix.det_submatrix_equiv_self (F.contractionCoordEquiv u p q hpq hp) B]
  congr 1
  funext i j
  let emb := F.contractionCoordEmbedding u p q hpq hp
  have h := congrArg (edgeCoefficientMap (R := R))
    (F.contractMovedEdge_quotientLaplacian_nonreference u p q hpq hp i j)
  simp only [map_sub, map_mul, edgeCoefficientMap_C] at h
  change shiftedQuotientLaplacian (F.contractMovedEdge u p q hpq) z i j =
    shiftedQuotientLaplacian F z (emb i) (emb j) -
      shiftedQuotientLaplacian F z (emb i) ⟨u, p, hp⟩ *
        MvPolynomial.C (quotientValueDifference F u p q (emb j) : R)
  have hi : emb i ≠ ⟨u, p, hp⟩ := F.contractionCoordEmbedding_ne u p q hpq hp i
  simp only [shiftedQuotientLaplacian, h, emb.injective.eq_iff, ite_eq_right hi, add_zero]
  ring

theorem shiftedContraction_reference (F : FiniteFiberSystem V E) (z : R)
    (u : V) (q : F.Fiber u) (hrq : F.reference u ≠ q) :
    shiftedQuotientDeterminant (F.contractMovedEdge u (F.reference u) q hrq) z =
      Matrix.det (fun i j : {i : F.Coord // i ≠ ⟨u, q, hrq.symm⟩} =>
        shiftedQuotientLaplacian F z i j - (if i.val.1 = u then 1 else 0) *
          shiftedQuotientLaplacian F z ⟨u, q, hrq.symm⟩ j) := by
  classical
  let B : Matrix {i : F.Coord // i ≠ ⟨u, q, hrq.symm⟩}
      {i : F.Coord // i ≠ ⟨u, q, hrq.symm⟩} (MvPolynomial E R) := fun i j =>
    shiftedQuotientLaplacian F z i j - (if i.val.1 = u then 1 else 0) *
      shiftedQuotientLaplacian F z ⟨u, q, hrq.symm⟩ j
  change (shiftedQuotientLaplacian (F.contractMovedEdge u (F.reference u) q hrq) z).det = B.det
  rw [← Matrix.det_submatrix_equiv_self (F.referenceContractionCoordEquiv u q hrq) B]
  congr 1
  funext i j
  let emb := F.referenceContractionCoordEmbedding u q hrq
  have h := congrArg (edgeCoefficientMap (R := R))
    (F.contractMovedEdge_quotientLaplacian_reference u q hrq i j)
  simp only [map_sub, map_mul, apply_ite, map_one, map_zero] at h
  change shiftedQuotientLaplacian (F.contractMovedEdge u (F.reference u) q hrq) z i j =
    shiftedQuotientLaplacian F z (emb i) (emb j) - (if i.1 = u then 1 else 0) *
      shiftedQuotientLaplacian F z ⟨u, q, hrq.symm⟩ (emb j)
  have hj : (⟨u, q, hrq.symm⟩ : F.Coord) ≠ emb j :=
    (F.referenceContractionCoordEmbedding_ne u q hrq j).symm
  simp only [shiftedQuotientLaplacian, h, emb.injective.eq_iff, ite_eq_right hj, add_zero]
  ring

theorem shiftedLoopDirection_nonreference (F : FiniteFiberSystem V E) (z : R)
    (e : E) (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.reference (F.src e)) (hpq : p ≠ F.loopTargetInSource e he p) :
    shiftedLoopDirection F z e he p =
      shiftedQuotientDeterminant
        (F.contractMovedEdge (F.src e) p (F.loopTargetInSource e he p) hpq) z := by
  classical
  have hrow : shiftedLoopDirection F z e he p =
      ((shiftedQuotientLaplacian F z).updateRow ⟨F.src e, p, hp⟩
        (fun j => MvPolynomial.C (quotientValueDifference F (F.src e) p
          (F.loopTargetInSource e he p) j : R))).det := by
    simp [shiftedLoopDirection, rankOneDetCoefficient,
      quotientPointClass_nonreference F (F.src e) p hp, apply_ite]
  rw [hrow, det_updateRow_compression _ _ _ (by
    simp [quotientValueDifference, Ne.symm hpq])]
  exact (shiftedContraction_nonreference F z (F.src e) p
    (F.loopTargetInSource e he p) hpq hp).symm

theorem shiftedLoopDirection_reference (F : FiniteFiberSystem V E) (z : R)
    (e : E) (he : F.src e = F.tgt e)
    (hrq : F.reference (F.src e) ≠ F.loopTargetInSource e he (F.reference (F.src e))) :
    shiftedLoopDirection F z e he (F.reference (F.src e)) =
      shiftedQuotientDeterminant (F.contractMovedEdge (F.src e) (F.reference (F.src e))
        (F.loopTargetInSource e he (F.reference (F.src e))) hrq) z := by
  classical
  let A := shiftedQuotientLaplacian F z
  let a : F.Coord → MvPolynomial E R := fun i => if i.1 = F.src e then 1 else 0
  let iq : F.Coord :=
    ⟨F.src e, F.loopTargetInSource e he (F.reference (F.src e)), hrq.symm⟩
  have ha : (fun i => (MvPolynomial.C
      (quotientPointClass F (F.src e) (F.reference (F.src e)) i : R) : MvPolynomial E R)) =
      (-1 : MvPolynomial E R) • a := by
    funext i
    by_cases hi : i.1 = F.src e <;> simp [quotientPointClass_reference, hi, a]
  have hl : (fun j => (MvPolynomial.C (quotientValueDifference F (F.src e)
      (F.reference (F.src e)) (F.loopTargetInSource e he (F.reference (F.src e))) j : R) :
        MvPolynomial E R)) = (fun j => if j = iq then -1 else 0) := by
    funext j
    rw [quotientValueDifference_reference F (F.src e) _ hrq.symm]
    change MvPolynomial.C ((-(if j = iq then (1 : ℤ) else 0) : ℤ) : R) = _
    by_cases hj : j = iq <;> simp [hj]
  have hcol : shiftedLoopDirection F z e he (F.reference (F.src e)) =
      (A.updateCol iq a).det := by
    unfold shiftedLoopDirection
    rw [ha, hl, rankOneDetCoefficient_columns]
    simp [a, iq]
    change -(A.updateCol iq (-a)).det = (A.updateCol iq a).det
    rw [← neg_one_smul (MvPolynomial E R) a, Matrix.det_updateCol_smul]
    ring
  rw [hcol, det_updateCol_compression _ _ _ (by simp [a, iq])]
  exact (shiftedContraction_reference F z (F.src e)
    (F.loopTargetInSource e he (F.reference (F.src e))) hrq).symm

/-- Manuscript Lemma 3.2, including the independent scalar parameter. -/
theorem loopCharacteristicDerivative (F : FiniteFiberSystem V E) (z : R)
    (e : E) (he : F.src e = F.tgt e) :
    MvPolynomial.pderiv e (shiftedQuotientDeterminant F z) =
      ∑ p : LoopChildIndex F e he,
        shiftedQuotientDeterminant (F.contractMovedEdge (F.src e) p.val
          (F.loopTargetInSource e he p.val) p.property) z := by
  classical
  let := F.fiberFintype (F.src e)
  rw [shiftedQuotientDeterminant_loop_directions F z e he]
  have hz : (∑ p : {p : F.Fiber (F.src e) // ¬p ≠ F.loopTargetInSource e he p},
      shiftedLoopDirection F z e he p) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    exact shiftedLoopDirection_fixed F z e he p (not_ne_iff.mp p.property)
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun p : F.Fiber (F.src e) => p ≠ F.loopTargetInSource e he p)
    (shiftedLoopDirection F z e he)
  rw [hz, add_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  rintro ⟨p, hpq⟩ _
  by_cases hp : p = F.reference (F.src e)
  · subst p
    exact shiftedLoopDirection_reference F z e he hpq
  · exact shiftedLoopDirection_nonreference F z e he p hp hpq

end Positivity
