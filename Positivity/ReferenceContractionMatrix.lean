import Positivity.ReferenceContractionCoordinates
import Positivity.ContractionMatrix

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local simp] cast_eq eq_mpr_eq_cast cast_cast
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

theorem referenceContractionCoord_point_ne (F : FiniteFiberSystem V E) (u : V)
    (q : F.Fiber u) (hrq : F.reference u ≠ q) (v : V)
    (j : (F.contractMovedEdge u (F.reference u) q hrq).CoordAt v) :
    (⟨v, F.contractedInclude u (F.reference u) v j.val⟩ : Sigma F.Fiber) ≠ ⟨u, q⟩ := by
  intro h
  have hv : v = u := congrArg Sigma.fst h
  subst v
  apply F.referenceContractionCoordEmbedding_ne u q hrq ⟨u, j⟩
  apply congrArg (Sigma.mk u)
  apply Subtype.ext
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

theorem contractedRedirect_reference_delta (F : FiniteFiberSystem V E) (u : V)
    (q : F.Fiber u) (hrq : F.reference u ≠ q) (v : V) (x : F.Fiber v)
    (j : (F.contractMovedEdge u (F.reference u) q hrq).CoordAt v) :
    (if F.contractedRedirect u (F.reference u) q hrq v x = j.val then (1 : ℤ) else 0) =
      (if x = F.contractedInclude u (F.reference u) v j.val then 1 else 0) := by
  rw [contractedRedirect_delta,
    ite_eq_right (F.referenceContractionCoord_point_ne u q hrq v j), mul_zero, add_zero]

theorem contractMovedEdge_entry_at_source_target_reference
    (F : FiniteFiberSystem V E) (u : V) (q : F.Fiber u)
    (hrq : F.reference u ≠ q) (e : E)
    (i : (F.contractMovedEdge u (F.reference u) q hrq).CoordAt (F.src e))
    (j : (F.contractMovedEdge u (F.reference u) q hrq).CoordAt (F.tgt e)) :
    let emb := F.referenceContractionCoordEmbedding u q hrq
    (F.contractMovedEdge u (F.reference u) q hrq).quotientEdgeCoefficient e
        ⟨F.src e, i⟩ ⟨F.tgt e, j⟩ =
      F.quotientEdgeCoefficient e (emb ⟨F.src e, i⟩) (emb ⟨F.tgt e, j⟩) -
      (if F.src e = u then 1 else 0) *
        F.quotientEdgeCoefficient e ⟨u, q, hrq.symm⟩ (emb ⟨F.tgt e, j⟩) := by
  classical
  dsimp only
  have hne := (F.referenceContractionCoordEmbedding_ne u q hrq ⟨F.tgt e, j⟩).symm
  have hdiag : (if (⟨F.src e, i⟩ : (F.contractMovedEdge u (F.reference u) q hrq).Coord) =
      ⟨F.tgt e, j⟩ then (1 : ℤ) else 0) =
      (if F.referenceContractionCoordEmbedding u q hrq ⟨F.src e, i⟩ =
        F.referenceContractionCoordEmbedding u q hrq ⟨F.tgt e, j⟩ then 1 else 0) :=
    if_congr (F.referenceContractionCoordEmbedding u q hrq).injective.eq_iff.symm rfl rfl
  erw [quotientEdgeCoefficient_at_source_target
    (F.contractMovedEdge u (F.reference u) q hrq) e i j]
  erw [contractMovedEdge_map, contractMovedEdge_map]
  rw [contractedRedirect_reference_delta, contractedRedirect_reference_delta]
  change _ = F.quotientEdgeCoefficient e ⟨F.src e, ⟨_, _⟩⟩ ⟨F.tgt e, ⟨_, _⟩⟩ - _
  rw [quotientEdgeCoefficient_at_source_target]
  erw [hdiag]
  dsimp only [referenceContractionCoordEmbedding, Function.Embedding.coeFn_mk] at hne ⊢
  by_cases hs : F.src e = u
  · subst u
    erw [contractedInclude_reference_at_reference]
    erw [quotientEdgeCoefficient_at_source_target]
    simp only [hne, ite_false, ite_true, one_mul]
    ring
  · erw [contractedInclude_reference_of_ne F u (F.reference u) q hrq (F.src e) hs]
    simp only [hs, ite_false, zero_mul, sub_zero]

theorem contractMovedEdge_quotientEdgeCoefficient_reference
    (F : FiniteFiberSystem V E) (u : V) (q : F.Fiber u)
    (hrq : F.reference u ≠ q) (e : E)
    (i j : (F.contractMovedEdge u (F.reference u) q hrq).Coord) :
    let emb := F.referenceContractionCoordEmbedding u q hrq
    (F.contractMovedEdge u (F.reference u) q hrq).quotientEdgeCoefficient e i j =
      F.quotientEdgeCoefficient e (emb i) (emb j) -
        (if i.1 = u then 1 else 0) * F.quotientEdgeCoefficient e ⟨u, q, hrq.symm⟩ (emb j) := by
  classical
  dsimp only
  obtain ⟨v, i⟩ := i
  obtain ⟨w, j⟩ := j
  by_cases hs : v = F.src e
  · subst v
    by_cases ht : w = F.tgt e
    · subst w
      exact contractMovedEdge_entry_at_source_target_reference F u q hrq e i j
    · have hleft := quotientEdgeCoefficient_at_source_off_target
        (F.contractMovedEdge u (F.reference u) q hrq) e i ⟨w, j⟩ ht
      have hright := quotientEdgeCoefficient_at_source_off_target F e
        (F.referenceContractionCoordEmbedding u q hrq ⟨F.src e, i⟩).2
        (F.referenceContractionCoordEmbedding u q hrq ⟨w, j⟩) ht
      have hzero : F.quotientEdgeCoefficient e ⟨u, q, hrq.symm⟩
          (F.referenceContractionCoordEmbedding u q hrq ⟨w, j⟩) = 0 := by
        by_cases hsu : F.src e = u
        · subst u
          erw [quotientEdgeCoefficient_at_source_off_target F e ⟨q, hrq.symm⟩ _ ht]
          exact ite_eq_right (F.referenceContractionCoordEmbedding_ne (F.src e) q hrq ⟨w, j⟩).symm
        · exact F.quotientEdgeCoefficient_eq_zero_of_src_ne e _ _ hsu
      erw [hleft, hright, hzero, mul_zero, sub_zero]
      exact if_congr (F.referenceContractionCoordEmbedding u q hrq).injective.eq_iff.symm rfl rfl
  · have hleft := (F.contractMovedEdge u (F.reference u) q hrq).quotientEdgeCoefficient_eq_zero_of_src_ne
      e ⟨v, i⟩ ⟨w, j⟩ (Ne.symm hs)
    have hright := F.quotientEdgeCoefficient_eq_zero_of_src_ne e
      (F.referenceContractionCoordEmbedding u q hrq ⟨v, i⟩)
      (F.referenceContractionCoordEmbedding u q hrq ⟨w, j⟩) (Ne.symm hs)
    rw [hleft, hright]
    by_cases hv : v = u
    · subst v
      rw [F.quotientEdgeCoefficient_eq_zero_of_src_ne e _ _ (Ne.symm hs)]
      simp
    · simp [hv]

theorem contractMovedEdge_quotientLaplacian_reference
    (F : FiniteFiberSystem V E) (u : V) (q : F.Fiber u)
    (hrq : F.reference u ≠ q)
    (i j : (F.contractMovedEdge u (F.reference u) q hrq).Coord) :
    let emb := F.referenceContractionCoordEmbedding u q hrq
    (F.contractMovedEdge u (F.reference u) q hrq).quotientLaplacian i j =
      F.quotientLaplacian (emb i) (emb j) -
        (if i.1 = u then 1 else 0) * F.quotientLaplacian ⟨u, q, hrq.symm⟩ (emb j) := by
  classical
  dsimp only
  simp only [quotientLaplacian, contractMovedEdge_quotientEdgeCoefficient_reference
    F u q hrq, map_sub, map_mul, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  by_cases hi : i.1 = u <;> simp [hi]

theorem contractMovedEdge_quotientDeterminant_reference
    (F : FiniteFiberSystem V E) (u : V) (q : F.Fiber u)
    (hrq : F.reference u ≠ q) :
    (F.contractMovedEdge u (F.reference u) q hrq).quotientDeterminant =
      Matrix.det (fun i j : {i : F.Coord // i ≠ ⟨u, q, hrq.symm⟩} =>
        F.quotientLaplacian i j - (if i.val.1 = u then 1 else 0) *
          F.quotientLaplacian ⟨u, q, hrq.symm⟩ j) := by
  classical
  let B : Matrix {i : F.Coord // i ≠ ⟨u, q, hrq.symm⟩}
      {i : F.Coord // i ≠ ⟨u, q, hrq.symm⟩} (MvPolynomial E ℤ) := fun i j =>
    F.quotientLaplacian i j - (if i.val.1 = u then 1 else 0) *
      F.quotientLaplacian ⟨u, q, hrq.symm⟩ j
  change (F.contractMovedEdge u (F.reference u) q hrq).quotientLaplacian.det = B.det
  rw [← Matrix.det_submatrix_equiv_self (F.referenceContractionCoordEquiv u q hrq) B]
  congr 1
  funext i j
  exact contractMovedEdge_quotientLaplacian_reference F u q hrq i j

end Positivity.FiniteFiberSystem
