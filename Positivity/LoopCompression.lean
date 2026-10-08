import Positivity.LoopDirections
import Positivity.DeterminantCompression

namespace Positivity
open FiniteFiberSystem
variable {V E : Type*} [Fintype V] [Fintype E]
set_option backward.isDefEq.respectTransparency false

theorem quotientPointClass_nonreference (F : FiniteFiberSystem V E) (u : V)
    (p : F.Fiber u) (hp : p ≠ F.reference u) (i : F.Coord) :
    quotientPointClass F u p i = if i = ⟨u, p, hp⟩ then 1 else 0 := by
  classical
  obtain ⟨v, i⟩ := i
  by_cases hv : v = u
  · subst v
    simp [quotientPointClass, hp, Sigma.mk.inj_iff, Subtype.ext_iff, eq_comm]
  · have hi : (⟨v, i⟩ : F.Coord) ≠ ⟨u, p, hp⟩ :=
      fun h => hv (congrArg Sigma.fst h)
    simp [quotientPointClass, hv, hi]

theorem loopDirectionCoefficient_nonreference (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.reference (F.src e)) :
    loopDirectionCoefficient F e he p =
      (F.quotientLaplacian.updateRow ⟨F.src e, p, hp⟩
        (fun j => MvPolynomial.C (quotientValueDifference F (F.src e) p
          (F.loopTargetInSource e he p) j))).det := by
  classical
  simp [loopDirectionCoefficient, rankOneDetCoefficient,
    quotientPointClass_nonreference F (F.src e) p hp, apply_ite]

theorem loopDirectionCoefficient_nonreference_compression (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.reference (F.src e)) (hpq : p ≠ F.loopTargetInSource e he p) :
    loopDirectionCoefficient F e he p =
      Matrix.det (fun i j : {i : F.Coord // i ≠ ⟨F.src e, p, hp⟩} =>
        F.quotientLaplacian i j - F.quotientLaplacian i ⟨F.src e, p, hp⟩ *
          MvPolynomial.C (quotientValueDifference F (F.src e) p
            (F.loopTargetInSource e he p) j)) := by
  classical
  rw [loopDirectionCoefficient_nonreference F e he p hp]
  apply det_updateRow_compression
  simp [quotientValueDifference, Ne.symm hpq]

attribute [local instance] Classical.propDecidable

theorem quotientPointClass_reference (F : FiniteFiberSystem V E) (u : V) (i : F.Coord) :
    quotientPointClass F u (F.reference u) i = if i.1 = u then -1 else 0 := by
  obtain ⟨v, i⟩ := i
  by_cases hv : v = u
  · subst v
    simp [quotientPointClass, Ne.symm i.property]
  · simp [quotientPointClass, hv]

theorem quotientValueDifference_reference (F : FiniteFiberSystem V E) (u : V)
    (q : F.Fiber u) (hq : q ≠ F.reference u) (j : F.Coord) :
    quotientValueDifference F u (F.reference u) q j =
      -(if j = ⟨u, q, hq⟩ then 1 else 0) := by
  obtain ⟨v, j⟩ := j
  by_cases hv : v = u
  · subst v
    simp [quotientValueDifference, Ne.symm j.property, Subtype.ext_iff, eq_comm]
  · have hj : (⟨v, j⟩ : F.Coord) ≠ ⟨u, q, hq⟩ :=
      fun h => hv (congrArg Sigma.fst h)
    simp [quotientValueDifference, hv, hj]

theorem loopDirectionCoefficient_reference (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e)
    (hrq : F.reference (F.src e) ≠ F.loopTargetInSource e he (F.reference (F.src e))) :
    loopDirectionCoefficient F e he (F.reference (F.src e)) =
      (F.quotientLaplacian.updateCol
        ⟨F.src e, F.loopTargetInSource e he (F.reference (F.src e)), hrq.symm⟩
        (fun i => if i.1 = F.src e then 1 else 0)).det := by
  classical
  let a : F.Coord → MvPolynomial E ℤ := fun i => if i.1 = F.src e then 1 else 0
  let iq : F.Coord :=
    ⟨F.src e, F.loopTargetInSource e he (F.reference (F.src e)), hrq.symm⟩
  have ha : (fun i => (MvPolynomial.C
      (quotientPointClass F (F.src e) (F.reference (F.src e)) i) : MvPolynomial E ℤ)) =
      (-1 : MvPolynomial E ℤ) • a := by
    funext i
    by_cases hi : i.1 = F.src e <;> simp [quotientPointClass_reference, hi, a]
  have hl : (fun j => (MvPolynomial.C (quotientValueDifference F (F.src e)
      (F.reference (F.src e)) (F.loopTargetInSource e he (F.reference (F.src e))) j) :
        MvPolynomial E ℤ)) = (fun j => if j = iq then -1 else 0) := by
    funext j
    rw [quotientValueDifference_reference F (F.src e) _ hrq.symm]
    change MvPolynomial.C (-(if j = iq then (1 : ℤ) else 0)) = _
    by_cases hj : j = iq <;> simp [hj]
  unfold loopDirectionCoefficient
  rw [ha, hl, rankOneDetCoefficient_columns]
  simp [Matrix.det_updateCol_smul, a, iq]
  change -(F.quotientLaplacian.updateCol iq (-a)).det =
    (F.quotientLaplacian.updateCol iq a).det
  rw [← neg_one_smul (MvPolynomial E ℤ) a, Matrix.det_updateCol_smul]
  ring

theorem loopDirectionCoefficient_reference_compression (F : FiniteFiberSystem V E)
    (e : E) (he : F.src e = F.tgt e)
    (hrq : F.reference (F.src e) ≠ F.loopTargetInSource e he (F.reference (F.src e))) :
    loopDirectionCoefficient F e he (F.reference (F.src e)) =
      Matrix.det (fun i j : {i : F.Coord // i ≠
          ⟨F.src e, F.loopTargetInSource e he (F.reference (F.src e)), hrq.symm⟩} =>
        F.quotientLaplacian i j - (if i.val.1 = F.src e then 1 else 0) *
          F.quotientLaplacian
            ⟨F.src e, F.loopTargetInSource e he (F.reference (F.src e)), hrq.symm⟩ j) := by
  classical
  rw [loopDirectionCoefficient_reference F e he hrq]
  apply det_updateCol_compression
  simp


end Positivity
