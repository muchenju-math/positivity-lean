import Positivity.EliminationMatrix
import Positivity.EliminationEdgePartition
import Positivity.SchurWeightExpansion

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E R : Type*} [Fintype V] [Fintype E] [CommRing R]

theorem map_quotientLaplacian (F : FiniteFiberSystem V E)
    (φ : MvPolynomial E ℤ →+* R) (i j : F.Coord) :
    φ (F.quotientLaplacian i j) =
      ∑ e, φ (MvPolynomial.X e) * (F.quotientEdgeCoefficient e i j : R) := by
  have hC (z : ℤ) : φ (MvPolynomial.C z) = (z : R) := by
    simpa using map_intCast (φ.comp MvPolynomial.C) z
  simp only [quotientLaplacian, map_sum, map_mul, hC]

theorem map_outgoingWeightSum [DecidableEq V] (F : FiniteFiberSystem V E)
    (φ : MvPolynomial E ℤ →+* R) (u : V) :
    φ (F.outgoingWeightSum u) = ∑ b : F.Outgoing u, φ (MvPolynomial.X b.val) := by
  classical
  simp [outgoingWeightSum, map_sum, ← Finset.sum_subtype_eq_sum_filter]

theorem map_quotientLaplacian_remaining [DecidableEq V] [DecidableEq E]
    (F : FiniteFiberSystem V E) (φ : MvPolynomial E ℤ →+* R)
    (u : V) (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (i j : F.Coord) (hi : i.1 ≠ u) :
    φ (F.quotientLaplacian i j) =
      (∑ a : F.Away u, φ (MvPolynomial.X a.val) * (F.quotientEdgeCoefficient a.val i j : R)) +
      ∑ a : F.Incoming u, φ (MvPolynomial.X a.val) * (F.quotientEdgeCoefficient a.val i j : R) := by
  classical
  rw [map_quotientLaplacian, F.sum_eliminationEdgePartition u hloop]
  have hz (b : F.Outgoing u) : F.quotientEdgeCoefficient b.val i j = 0 :=
    F.quotientEdgeCoefficient_eq_zero_of_src_ne b.val i j
      (by simpa only [b.property] using Ne.symm hi)
  simp only [hz, Int.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]

theorem map_quotientLaplacian_into [DecidableEq V] [DecidableEq E]
    (F : FiniteFiberSystem V E) (φ : MvPolynomial E ℤ →+* R)
    (u : V) (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (i : F.Coord) (hi : i.1 ≠ u) (k : F.CoordAt u) :
    φ (F.quotientLaplacian i ⟨u, k⟩) =
      ∑ a : F.Incoming u, φ (MvPolynomial.X a.val) *
        (F.quotientEdgeCoefficient a.val i ⟨u, k⟩ : R) := by
  rw [map_quotientLaplacian_remaining F φ u hloop i ⟨u, k⟩ hi]
  have hz (a : F.Away u) : F.quotientEdgeCoefficient a.val i ⟨u, k⟩ = 0 := by
    have hik : i ≠ ⟨u, k⟩ := fun h => hi (congrArg Sigma.fst h)
    simp [quotientEdgeCoefficient, hik, Ne.symm a.property.2]
  simp only [hz, Int.cast_zero, mul_zero, Finset.sum_const_zero, zero_add]

theorem map_quotientLaplacian_outof [DecidableEq V] [DecidableEq E]
    (F : FiniteFiberSystem V E) (φ : MvPolynomial E ℤ →+* R)
    (u : V) (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (k : F.CoordAt u) (j : F.Coord) :
    φ (F.quotientLaplacian ⟨u, k⟩ j) =
      ∑ b : F.Outgoing u, φ (MvPolynomial.X b.val) *
        (F.quotientEdgeCoefficient b.val ⟨u, k⟩ j : R) := by
  rw [map_quotientLaplacian, F.sum_eliminationEdgePartition u hloop]
  have hza (a : F.Away u) : F.quotientEdgeCoefficient a.val ⟨u, k⟩ j = 0 :=
    F.quotientEdgeCoefficient_eq_zero_of_src_ne a.val _ _ a.property.1
  have hzi (a : F.Incoming u) : F.quotientEdgeCoefficient a.val ⟨u, k⟩ j = 0 :=
    F.quotientEdgeCoefficient_eq_zero_of_src_ne a.val _ _
      (fun h => hloop a.val (h.trans a.property.symm))
  simp only [hza, hzi, Int.cast_zero, mul_zero, Finset.sum_const_zero, zero_add]

end Positivity.FiniteFiberSystem

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Field K]

noncomputable def eliminationEvaluation (F : FiniteFiberSystem V E) (u : V)
    (φ : MvPolynomial E ℤ →+* K) :
    MvPolynomial (F.Away u ⊕ (F.Incoming u × F.Outgoing u)) ℤ →+* K :=
  MvPolynomial.eval₂Hom (Int.castRingHom K)
    (Sum.elim (fun a => φ (MvPolynomial.X a.val))
      (fun ab => φ (MvPolynomial.X ab.1.val) * φ (MvPolynomial.X ab.2.val) /
        φ (F.outgoingWeightSum u)))

/-- The evaluated auxiliary quotient matrix is exactly the Schur complement,
entry by entry, with virtual weights `a * b / s`. -/
theorem eliminationEvaluation_quotientLaplacian (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (φ : MvPolynomial E ℤ →+* K)
    (hs : φ (F.outgoingWeightSum u) ≠ 0)
    (i j : (F.eliminateSystemAllCompositions u hloop).Coord) :
    let emb := F.auxiliaryCoordEmbedding u hloop
    F.eliminationEvaluation u φ ((F.eliminateSystemAllCompositions u hloop).quotientLaplacian i j) =
      φ (F.quotientLaplacian (emb i) (emb j)) - (φ (F.outgoingWeightSum u))⁻¹ *
        ∑ k : F.CoordAt u, φ (F.quotientLaplacian (emb i) ⟨u, k⟩) *
          φ (F.quotientLaplacian ⟨u, k⟩ (emb j)) := by
  classical
  dsimp only
  let emb := F.auxiliaryCoordEmbedding u hloop
  have hi : (emb i).1 ≠ u := i.1.property
  have hs' : (∑ b : F.Outgoing u, φ (MvPolynomial.X b.val)) ≠ 0 := by
    rwa [← F.map_outgoingWeightSum φ u]
  have hschur := schurWeightExpansion
    (fun a : F.Incoming u => φ (MvPolynomial.X a.val))
    (fun b : F.Outgoing u => φ (MvPolynomial.X b.val))
    (fun a : F.Incoming u => (F.quotientEdgeCoefficient a.val (emb i) (emb j) : K))
    (fun (a : F.Incoming u) (k : F.CoordAt u) =>
      (F.quotientEdgeCoefficient a.val (emb i) ⟨u, k⟩ : K))
    (fun (b : F.Outgoing u) (k : F.CoordAt u) =>
      (F.quotientEdgeCoefficient b.val ⟨u, k⟩ (emb j) : K)) hs'
  rw [← F.map_outgoingWeightSum φ u] at hschur
  rw [map_quotientLaplacian_remaining F φ u hloop _ _ hi]
  have hsum :
      (∑ k : F.CoordAt u, φ (F.quotientLaplacian (emb i) ⟨u, k⟩) *
        φ (F.quotientLaplacian ⟨u, k⟩ (emb j))) =
      ∑ k : F.CoordAt u,
        (∑ a : F.Incoming u, φ (MvPolynomial.X a.val) *
          (F.quotientEdgeCoefficient a.val (emb i) ⟨u, k⟩ : K)) *
        (∑ b : F.Outgoing u, φ (MvPolynomial.X b.val) *
          (F.quotientEdgeCoefficient b.val ⟨u, k⟩ (emb j) : K)) := by
    apply Finset.sum_congr rfl
    intro k _
    erw [map_quotientLaplacian_into F φ u hloop _ hi,
      map_quotientLaplacian_outof F φ u hloop]
  erw [hsum]
  erw [add_sub_assoc, hschur]
  erw [map_quotientLaplacian (F.eliminateSystemAllCompositions u hloop)
    (F.eliminationEvaluation u φ) i j]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, eliminationEvaluation,
    MvPolynomial.eval₂Hom_X, Sum.elim_inl, Sum.elim_inr]
  simp only [retainedEdgeCoefficient_elimination, virtualEdgeCoefficient_elimination,
    Int.cast_sub, Int.cast_sum, Int.cast_mul]
  simp only [MvPolynomial.eval₂Hom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, MvPolynomial.eval₂_X, Sum.elim_inl, Sum.elim_inr]
  rfl

end Positivity.FiniteFiberSystem
