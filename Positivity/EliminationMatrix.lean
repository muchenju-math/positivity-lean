import Positivity.EliminationBlocks
import Positivity.EliminationPullback
import Positivity.ContractionMatrix

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local simp] cast_eq eq_mpr_eq_cast cast_cast
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem fiber_cast_eq_iff (F : FiniteFiberSystem V E) {v w : V} (h : v = w)
    (x : F.Fiber v) (y : F.Fiber w) : (h ▸ x) = y ↔ x = (h.symm ▸ y) := by
  cases h
  rfl

theorem reference_cast (F : FiniteFiberSystem V E) {v w : V} (h : v = w) :
    (h ▸ F.reference v) = F.reference w := by
  cases h
  rfl

noncomputable def auxiliaryCoordEquiv (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) :
    {i : F.Coord // i.1 ≠ u} ≃ (F.eliminateSystemAllCompositions u hloop).Coord where
  toFun i := ⟨⟨i.val.1, i.property⟩, i.val.2⟩
  invFun i := ⟨⟨i.1.val, i.2⟩, i.1.property⟩
  left_inv := by rintro ⟨⟨v, i⟩, hi⟩; rfl
  right_inv := by rintro ⟨⟨v, hv⟩, i⟩; rfl

noncomputable def auxiliaryCoordEmbedding (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) :
    (F.eliminateSystemAllCompositions u hloop).Coord ↪ F.Coord :=
  (F.auxiliaryCoordEquiv u hloop).symm.toEmbedding.trans (Function.Embedding.subtype _)

noncomputable def eliminationAuxCoordEquiv (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) :
    F.Coord ≃ F.CoordAt u ⊕ (F.eliminateSystemAllCompositions u hloop).Coord :=
  (F.eliminationCoordEquiv u).trans (Equiv.sumCongr (Equiv.refl _) (F.auxiliaryCoordEquiv u hloop))

theorem quotientEdgeCoefficient_incoming_block (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (a : F.Incoming u)
    (i : F.CoordAt (F.src a.val)) (j : F.CoordAt u) :
    F.quotientEdgeCoefficient a.val ⟨F.src a.val, i⟩ ⟨u, j⟩ =
      -F.incomingPullbackAt u a i j := by
  have hsrc : F.src a.val ≠ u := fun h => hloop a.val (h.trans a.property.symm)
  have hij : (⟨F.src a.val, i⟩ : F.Coord) ≠ ⟨u, j⟩ :=
    fun h => hsrc (congrArg Sigma.fst h)
  simp [quotientEdgeCoefficient, hij, a.property, incomingPullbackAt, normalizedPullback]
  simp only [F.fiber_cast_eq_iff a.property]

theorem quotientEdgeCoefficient_outgoing_block (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (b : F.Outgoing u)
    (i : F.CoordAt u) (j : F.CoordAt (F.tgt b.val)) :
    F.quotientEdgeCoefficient b.val ⟨u, i⟩ ⟨F.tgt b.val, j⟩ =
      -F.outgoingPullbackAt u b i j := by
  have htgt : u ≠ F.tgt b.val := fun h => hloop b.val (b.property.trans h)
  have hij : (⟨u, i⟩ : F.Coord) ≠ ⟨F.tgt b.val, j⟩ :=
    fun h => htgt (congrArg Sigma.fst h)
  simp [quotientEdgeCoefficient, hij, b.property, outgoingPullbackAt, normalizedPullback]
  simp only [F.reference_cast b.property.symm]

theorem quotientEdgeCoefficient_at_source_target_pullback (F : FiniteFiberSystem V E)
    (e : E) (i : F.CoordAt (F.src e)) (j : F.CoordAt (F.tgt e)) :
    F.quotientEdgeCoefficient e ⟨F.src e, i⟩ ⟨F.tgt e, j⟩ =
      (if (⟨F.src e, i⟩ : F.Coord) = ⟨F.tgt e, j⟩ then 1 else 0) - F.pullback e i j := by
  rw [quotientEdgeCoefficient_at_source_target]
  rfl

set_option maxHeartbeats 800000 in
theorem virtualEdgeCoefficient_elimination (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (a : F.Incoming u) (b : F.Outgoing u)
    (i j : (F.eliminateSystemAllCompositions u hloop).Coord) :
    let emb := F.auxiliaryCoordEmbedding u hloop
    (F.eliminateSystemAllCompositions u hloop).quotientEdgeCoefficient (Sum.inr (a, b)) i j =
      F.quotientEdgeCoefficient a.val (emb i) (emb j) -
        ∑ k : F.CoordAt u, F.quotientEdgeCoefficient a.val (emb i) ⟨u, k⟩ *
          F.quotientEdgeCoefficient b.val ⟨u, k⟩ (emb j) := by
  classical
  dsimp only
  have hdiag : (if i = j then (1 : ℤ) else 0) =
      (if F.auxiliaryCoordEmbedding u hloop i = F.auxiliaryCoordEmbedding u hloop j
        then 1 else 0) :=
    if_congr (F.auxiliaryCoordEmbedding u hloop).injective.eq_iff.symm rfl rfl
  obtain ⟨⟨v, hv⟩, i⟩ := i
  obtain ⟨⟨w, hw⟩, j⟩ := j
  have hwa : w ≠ F.tgt a.val := by simpa only [a.property] using hw
  by_cases hs : v = F.src a.val
  · subst v
    have hparent := quotientEdgeCoefficient_at_source_off_target F a.val i
      (F.auxiliaryCoordEmbedding u hloop ⟨⟨w, hw⟩, j⟩) hwa
    erw [hparent]
    by_cases ht : w = F.tgt b.val
    · subst w
      erw [quotientEdgeCoefficient_at_source_target_pullback
        (F.eliminateSystemAllCompositions u hloop) (Sum.inr (a, b)) i j, hdiag]
      have hm := congrFun (congrFun
        (F.eliminateSystemAllCompositions_pullback u hloop a b) i) j
      change (∑ k : F.CoordAt u, F.incomingPullbackAt u a i k * F.outgoingPullbackAt u b k j) = _ at hm
      have hsum : (∑ k : F.CoordAt u,
          F.quotientEdgeCoefficient a.val
            (F.auxiliaryCoordEmbedding u hloop ⟨⟨F.src a.val, hv⟩, i⟩) ⟨u, k⟩ *
          F.quotientEdgeCoefficient b.val ⟨u, k⟩
            (F.auxiliaryCoordEmbedding u hloop ⟨⟨F.tgt b.val, hw⟩, j⟩)) =
          (F.eliminateSystemAllCompositions u hloop).pullback (Sum.inr (a, b)) i j := by
        apply Eq.trans _ hm
        apply Finset.sum_congr rfl
        intro k hk
        change F.quotientEdgeCoefficient a.val ⟨F.src a.val, i⟩ ⟨u, k⟩ *
          F.quotientEdgeCoefficient b.val ⟨u, k⟩ ⟨F.tgt b.val, j⟩ = _
        rw [F.quotientEdgeCoefficient_incoming_block u hloop a,
          F.quotientEdgeCoefficient_outgoing_block u hloop b, neg_mul_neg]
      erw [hsum]
      rfl
    · have hvt : (⟨w, hw⟩ : {v : V // v ≠ u}) ≠
          (F.eliminateSystemAllCompositions u hloop).tgt (Sum.inr (a, b)) := by
        intro h
        exact ht (congrArg Subtype.val h)
      erw [quotientEdgeCoefficient_at_source_off_target
        (F.eliminateSystemAllCompositions u hloop) (Sum.inr (a, b)) i ⟨⟨w, hw⟩, j⟩ hvt,
        hdiag]
      have hz (k : F.CoordAt u) : F.quotientEdgeCoefficient b.val ⟨u, k⟩
          (F.auxiliaryCoordEmbedding u hloop ⟨⟨w, hw⟩, j⟩) = 0 := by
        have hkj : (⟨u, k⟩ : F.Coord) ≠ ⟨w, j⟩ := fun h => hw (congrArg Sigma.fst h).symm
        change F.quotientEdgeCoefficient b.val ⟨u, k⟩ ⟨w, j⟩ = 0
        simp [quotientEdgeCoefficient, b.property, ht, hkj]
      simp only [hz, mul_zero, Finset.sum_const_zero, sub_zero]
      rfl
  · have hvs : (F.eliminateSystemAllCompositions u hloop).src (Sum.inr (a, b)) ≠
          (⟨v, hv⟩ : {v : V // v ≠ u}) := by
      intro h
      exact hs (congrArg Subtype.val h).symm
    rw [(F.eliminateSystemAllCompositions u hloop).quotientEdgeCoefficient_eq_zero_of_src_ne
      (Sum.inr (a, b)) _ _ hvs]
    have hz (k : F.Coord) : F.quotientEdgeCoefficient a.val
        (F.auxiliaryCoordEmbedding u hloop ⟨⟨v, hv⟩, i⟩) k = 0 :=
      F.quotientEdgeCoefficient_eq_zero_of_src_ne a.val _ k (Ne.symm hs)
    simp only [hz, zero_mul, Finset.sum_const_zero, sub_zero]

theorem retainedEdgeCoefficient_elimination (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (a : F.Away u)
    (i j : (F.eliminateSystemAllCompositions u hloop).Coord) :
    (F.eliminateSystemAllCompositions u hloop).quotientEdgeCoefficient (Sum.inl a) i j =
      F.quotientEdgeCoefficient a.val (F.auxiliaryCoordEmbedding u hloop i)
        (F.auxiliaryCoordEmbedding u hloop j) := by
  classical
  have hdiag : (if i = j then (1 : ℤ) else 0) =
      (if F.auxiliaryCoordEmbedding u hloop i = F.auxiliaryCoordEmbedding u hloop j
        then 1 else 0) :=
    if_congr (F.auxiliaryCoordEmbedding u hloop).injective.eq_iff.symm rfl rfl
  obtain ⟨⟨v, hv⟩, i⟩ := i
  obtain ⟨⟨w, hw⟩, j⟩ := j
  by_cases hs : v = F.src a.val
  · subst v
    by_cases ht : w = F.tgt a.val
    · subst w
      erw [quotientEdgeCoefficient_at_source_target_pullback
        (F.eliminateSystemAllCompositions u hloop) (Sum.inl a) i j, hdiag]
      change _ = F.quotientEdgeCoefficient a.val ⟨F.src a.val, i⟩ ⟨F.tgt a.val, j⟩
      rw [quotientEdgeCoefficient_at_source_target_pullback]
      rfl
    · have hvt : (⟨w, hw⟩ : {v : V // v ≠ u}) ≠
          (F.eliminateSystemAllCompositions u hloop).tgt (Sum.inl a) := by
        intro h
        exact ht (congrArg Subtype.val h)
      erw [quotientEdgeCoefficient_at_source_off_target
        (F.eliminateSystemAllCompositions u hloop) (Sum.inl a) i ⟨⟨w, hw⟩, j⟩ hvt, hdiag]
      change _ = F.quotientEdgeCoefficient a.val ⟨F.src a.val, i⟩ ⟨w, j⟩
      rw [quotientEdgeCoefficient_at_source_off_target F a.val i ⟨w, j⟩ ht]
      rfl
  · have hvs : (F.eliminateSystemAllCompositions u hloop).src (Sum.inl a) ≠
          (⟨v, hv⟩ : {v : V // v ≠ u}) := by
      intro h
      exact hs (congrArg Subtype.val h).symm
    rw [(F.eliminateSystemAllCompositions u hloop).quotientEdgeCoefficient_eq_zero_of_src_ne
      (Sum.inl a) _ _ hvs]
    exact (F.quotientEdgeCoefficient_eq_zero_of_src_ne a.val _ _ (Ne.symm hs)).symm

end Positivity.FiniteFiberSystem
