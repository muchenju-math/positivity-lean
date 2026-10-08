import Positivity.ContractionCoordinates
import Positivity.LoopCompression

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local simp] cast_eq eq_mpr_eq_cast cast_cast
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

theorem quotientValueDifference_contractionCoordEmbedding (F : FiniteFiberSystem V E)
    (u : V) (p q : F.Fiber u) (hpq : p ≠ q) (hp : p ≠ F.reference u)
    (j : (F.contractMovedEdge u p q hpq).Coord) :
    quotientValueDifference F u p q (F.contractionCoordEmbedding u p q hpq hp j) =
      -(if (⟨j.1, F.contractedInclude u p j.1 j.2.val⟩ : Sigma F.Fiber) = ⟨u, q⟩
        then 1 else 0) := by
  classical
  obtain ⟨v, j⟩ := j
  by_cases hv : v = u
  · subst v
    have hj := F.contractedInclude_ne u p j.val
    simp [quotientValueDifference, contractionCoordEmbedding, Ne.symm hj, eq_comm]
  · have hj : (⟨v, F.contractedInclude u p v j.val⟩ : Sigma F.Fiber) ≠ ⟨u, q⟩ :=
      fun h => hv (congrArg Sigma.fst h)
    simp [quotientValueDifference, contractionCoordEmbedding, hv, hj]

theorem quotientEdgeCoefficient_at_source_target (F : FiniteFiberSystem V E)
    (e : E) (i : F.CoordAt (F.src e)) (j : F.CoordAt (F.tgt e)) :
    F.quotientEdgeCoefficient e ⟨F.src e, i⟩ ⟨F.tgt e, j⟩ =
      (if (⟨F.src e, i⟩ : F.Coord) = ⟨F.tgt e, j⟩ then 1 else 0) -
        ((if F.fiberMap e i.val = j.val then 1 else 0) -
          (if F.fiberMap e (F.reference (F.src e)) = j.val then 1 else 0)) := by
  classical
  simp [quotientEdgeCoefficient]

set_option maxHeartbeats 800000 in
theorem contractMovedEdge_entry_at_source_target_nonreference
    (F : FiniteFiberSystem V E) (u : V) (p q : F.Fiber u)
    (hpq : p ≠ q) (hp : p ≠ F.reference u) (e : E)
    (i : (F.contractMovedEdge u p q hpq).CoordAt (F.src e))
    (j : (F.contractMovedEdge u p q hpq).CoordAt (F.tgt e)) :
    let emb := F.contractionCoordEmbedding u p q hpq hp
    (F.contractMovedEdge u p q hpq).quotientEdgeCoefficient e ⟨F.src e, i⟩ ⟨F.tgt e, j⟩ =
      F.quotientEdgeCoefficient e (emb ⟨F.src e, i⟩) (emb ⟨F.tgt e, j⟩) -
      F.quotientEdgeCoefficient e (emb ⟨F.src e, i⟩) ⟨u, p, hp⟩ *
        quotientValueDifference F u p q (emb ⟨F.tgt e, j⟩) := by
  classical
  dsimp only
  rw [quotientValueDifference_contractionCoordEmbedding]
  have hi := F.contractionCoordEmbedding_ne u p q hpq hp ⟨F.src e, i⟩
  have hij := (F.contractionCoordEmbedding u p q hpq hp).injective.eq_iff
    (a := ⟨F.src e, i⟩) (b := ⟨F.tgt e, j⟩)
  erw [quotientEdgeCoefficient_at_source_target (F.contractMovedEdge u p q hpq) e i j]
  erw [contractMovedEdge_map, contractMovedEdge_map,
    contractedInclude_reference F u p q hpq hp]
  rw [contractedRedirect_delta, contractedRedirect_delta]
  change _ = F.quotientEdgeCoefficient e
    ⟨F.src e, ⟨_, _⟩⟩ ⟨F.tgt e, ⟨_, _⟩⟩ - _
  rw [quotientEdgeCoefficient_at_source_target]
  have hdiag : (if (⟨F.src e, i⟩ : (F.contractMovedEdge u p q hpq).Coord) =
      ⟨F.tgt e, j⟩ then (1 : ℤ) else 0) =
      (if F.contractionCoordEmbedding u p q hpq hp ⟨F.src e, i⟩ =
        F.contractionCoordEmbedding u p q hpq hp ⟨F.tgt e, j⟩ then 1 else 0) :=
    if_congr hij.symm rfl rfl
  erw [hdiag]
  dsimp only [contractionCoordEmbedding, Function.Embedding.coeFn_mk] at hi ⊢
  by_cases ht : F.tgt e = u
  · subst u
    erw [quotientEdgeCoefficient_at_source_target]
    simp only [hi, ite_eq_right, zero_sub, mul_neg, sub_neg_eq_add]
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, ite_false]
    ring
  · have hz : F.quotientEdgeCoefficient e
        (F.contractionCoordEmbedding u p q hpq hp ⟨F.src e, i⟩) ⟨u, p, hp⟩ = 0 := by
      simp [quotientEdgeCoefficient, hi, Ne.symm ht, contractionCoordEmbedding]
    erw [hz, zero_mul, sub_zero]
    have hne (x : F.Fiber (F.tgt e)) (y : F.Fiber u) :
        (⟨F.tgt e, x⟩ : Sigma F.Fiber) ≠ ⟨u, y⟩ := fun h => ht (congrArg Sigma.fst h)
    simp [hne]

theorem quotientEdgeCoefficient_at_source_off_target (F : FiniteFiberSystem V E)
    (e : E) (i : F.CoordAt (F.src e)) (j : F.Coord) (hj : j.1 ≠ F.tgt e) :
    F.quotientEdgeCoefficient e ⟨F.src e, i⟩ j =
      if (⟨F.src e, i⟩ : F.Coord) = j then 1 else 0 := by
  classical
  simp [quotientEdgeCoefficient, hj]

theorem contractMovedEdge_quotientEdgeCoefficient_nonreference
    (F : FiniteFiberSystem V E) (u : V) (p q : F.Fiber u)
    (hpq : p ≠ q) (hp : p ≠ F.reference u) (e : E)
    (i j : (F.contractMovedEdge u p q hpq).Coord) :
    let emb := F.contractionCoordEmbedding u p q hpq hp
    (F.contractMovedEdge u p q hpq).quotientEdgeCoefficient e i j =
      F.quotientEdgeCoefficient e (emb i) (emb j) -
        F.quotientEdgeCoefficient e (emb i) ⟨u, p, hp⟩ *
          quotientValueDifference F u p q (emb j) := by
  classical
  dsimp only
  obtain ⟨v, i⟩ := i
  obtain ⟨w, j⟩ := j
  by_cases hs : v = F.src e
  · subst v
    by_cases ht : w = F.tgt e
    · subst w
      exact contractMovedEdge_entry_at_source_target_nonreference F u p q hpq hp e i j
    · have hleft := quotientEdgeCoefficient_at_source_off_target
        (F.contractMovedEdge u p q hpq) e i ⟨w, j⟩ ht
      have hright := quotientEdgeCoefficient_at_source_off_target F e
        (F.contractionCoordEmbedding u p q hpq hp ⟨F.src e, i⟩).2
        (F.contractionCoordEmbedding u p q hpq hp ⟨w, j⟩) ht
      erw [hleft, hright]
      have hprod : F.quotientEdgeCoefficient e
          (F.contractionCoordEmbedding u p q hpq hp ⟨F.src e, i⟩) ⟨u, p, hp⟩ *
          quotientValueDifference F u p q (F.contractionCoordEmbedding u p q hpq hp ⟨w, j⟩) = 0 := by
        by_cases hw : w = u
        · subst w
          have hzero := quotientEdgeCoefficient_at_source_off_target F e
            (F.contractionCoordEmbedding u p q hpq hp ⟨F.src e, i⟩).2 ⟨u, p, hp⟩ ht
          erw [hzero]
          have hn : (⟨F.src e, (F.contractionCoordEmbedding u p q hpq hp
              ⟨F.src e, i⟩).2⟩ : F.Coord) ≠ ⟨u, p, hp⟩ :=
            F.contractionCoordEmbedding_ne u p q hpq hp ⟨F.src e, i⟩
          rw [ite_eq_right hn, zero_mul]
        · have hzero : quotientValueDifference F u p q
              (F.contractionCoordEmbedding u p q hpq hp ⟨w, j⟩) = 0 := by
            simp [quotientValueDifference, contractionCoordEmbedding, hw]
          rw [hzero, mul_zero]
      erw [hprod, sub_zero]
      exact if_congr ((F.contractionCoordEmbedding u p q hpq hp).injective.eq_iff).symm rfl rfl
  · have hleft := (F.contractMovedEdge u p q hpq).quotientEdgeCoefficient_eq_zero_of_src_ne
      e ⟨v, i⟩ ⟨w, j⟩ (Ne.symm hs)
    have hright := F.quotientEdgeCoefficient_eq_zero_of_src_ne e
      (F.contractionCoordEmbedding u p q hpq hp ⟨v, i⟩)
      (F.contractionCoordEmbedding u p q hpq hp ⟨w, j⟩) (Ne.symm hs)
    have hcorrection := F.quotientEdgeCoefficient_eq_zero_of_src_ne e
      (F.contractionCoordEmbedding u p q hpq hp ⟨v, i⟩) ⟨u, p, hp⟩ (Ne.symm hs)
    rw [hleft, hright, hcorrection, zero_mul, sub_zero]

theorem contractMovedEdge_quotientLaplacian_nonreference
    (F : FiniteFiberSystem V E) (u : V) (p q : F.Fiber u)
    (hpq : p ≠ q) (hp : p ≠ F.reference u)
    (i j : (F.contractMovedEdge u p q hpq).Coord) :
    let emb := F.contractionCoordEmbedding u p q hpq hp
    (F.contractMovedEdge u p q hpq).quotientLaplacian i j =
      F.quotientLaplacian (emb i) (emb j) -
        F.quotientLaplacian (emb i) ⟨u, p, hp⟩ *
          MvPolynomial.C (quotientValueDifference F u p q (emb j)) := by
  classical
  dsimp only
  simp only [quotientLaplacian, contractMovedEdge_quotientEdgeCoefficient_nonreference
    F u p q hpq hp, map_sub, map_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_mul, mul_assoc]

theorem contractMovedEdge_quotientDeterminant_nonreference
    (F : FiniteFiberSystem V E) (u : V) (p q : F.Fiber u)
    (hpq : p ≠ q) (hp : p ≠ F.reference u) :
    (F.contractMovedEdge u p q hpq).quotientDeterminant =
      Matrix.det (fun i j : {i : F.Coord // i ≠ ⟨u, p, hp⟩} =>
        F.quotientLaplacian i j - F.quotientLaplacian i ⟨u, p, hp⟩ *
          MvPolynomial.C (quotientValueDifference F u p q j)) := by
  classical
  let B : Matrix {i : F.Coord // i ≠ ⟨u, p, hp⟩} {i : F.Coord // i ≠ ⟨u, p, hp⟩}
      (MvPolynomial E ℤ) := fun i j =>
    F.quotientLaplacian i j - F.quotientLaplacian i ⟨u, p, hp⟩ *
      MvPolynomial.C (quotientValueDifference F u p q j)
  change (F.contractMovedEdge u p q hpq).quotientLaplacian.det = B.det
  rw [← Matrix.det_submatrix_equiv_self (F.contractionCoordEquiv u p q hpq hp) B]
  congr 1
  funext i j
  exact contractMovedEdge_quotientLaplacian_nonreference F u p q hpq hp i j

end Positivity.FiniteFiberSystem

namespace Positivity
open FiniteFiberSystem
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Every moved lift whose source is not the reference has precisely its
contracted child's determinant as its contribution to the loop derivative. -/
theorem loopDirectionCoefficient_eq_contraction_nonreference
    (F : FiniteFiberSystem V E) (e : E) (he : F.src e = F.tgt e)
    (p : F.Fiber (F.src e)) (hp : p ≠ F.reference (F.src e))
    (hpq : p ≠ F.loopTargetInSource e he p) :
    loopDirectionCoefficient F e he p =
      (F.contractMovedEdge (F.src e) p (F.loopTargetInSource e he p) hpq).quotientDeterminant := by
  rw [loopDirectionCoefficient_nonreference_compression F e he p hp hpq]
  exact (F.contractMovedEdge_quotientDeterminant_nonreference
    (F.src e) p (F.loopTargetInSource e he p) hpq hp).symm

end Positivity
