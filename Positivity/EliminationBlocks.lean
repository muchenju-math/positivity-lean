import Positivity.VertexElimination
import Positivity.NormalizedPullback

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def eliminationCoordEquiv (F : FiniteFiberSystem V E) (u : V) :
    F.Coord ≃ F.CoordAt u ⊕ {i : F.Coord // i.1 ≠ u} where
  toFun i := if h : i.1 = u then Sum.inl (h ▸ i.2) else Sum.inr ⟨i, h⟩
  invFun := Sum.elim (Sigma.mk u) Subtype.val
  left_inv := by
    rintro ⟨v, i⟩
    by_cases hv : v = u
    · subst v
      simp
    · simp [hv]
  right_inv := by
    intro i
    cases i with
    | inl i => simp
    | inr i =>
      simp
      exact i.property

noncomputable def outgoingWeightSum (F : FiniteFiberSystem V E) (u : V) :
    MvPolynomial E ℤ := ∑ e ∈ Finset.univ.filter (fun e => F.src e = u), MvPolynomial.X e

theorem quotientEdgeCoefficient_vertexBlock_loopless (F : FiniteFiberSystem V E)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (u : V) (e : E) (i j : F.CoordAt u) :
    F.quotientEdgeCoefficient e ⟨u, i⟩ ⟨u, j⟩ =
      if i = j then (if F.src e = u then 1 else 0) else 0 := by
  classical
  by_cases hs : F.src e = u
  · have ht : u ≠ F.tgt e := fun h => hloop e (hs.trans h)
    simp [quotientEdgeCoefficient, hs, ht]
  · simp [quotientEdgeCoefficient, hs, Ne.symm hs]

theorem quotientLaplacian_vertexBlock_loopless (F : FiniteFiberSystem V E)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (u : V) (i j : F.CoordAt u) :
    F.quotientLaplacian ⟨u, i⟩ ⟨u, j⟩ =
      (F.outgoingWeightSum u • (1 : Matrix (F.CoordAt u) (F.CoordAt u) (MvPolynomial E ℤ))) i j := by
  classical
  by_cases hij : i = j <;>
    simp [quotientLaplacian, F.quotientEdgeCoefficient_vertexBlock_loopless hloop,
      outgoingWeightSum, Finset.sum_filter, Matrix.smul_apply, Matrix.one_apply, hij, apply_ite]

theorem quotientBlock_elimination_scalar (F : FiniteFiberSystem V E)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (u : V) :
    quotientBlock₁₁ F (F.eliminationCoordEquiv u) =
      F.outgoingWeightSum u • (1 : Matrix (F.CoordAt u) (F.CoordAt u) (MvPolynomial E ℤ)) := by
  funext i j
  exact F.quotientLaplacian_vertexBlock_loopless hloop u i j

theorem outgoingWeightSum_ne_zero_of_edge (F : FiniteFiberSystem V E)
    (u : V) (e : E) (he : F.src e = u) : F.outgoingWeightSum u ≠ 0 := by
  classical
  intro h
  have hc := congrArg (fun P : MvPolynomial E ℤ => P.coeff (Finsupp.single e 1)) h
  simp [outgoingWeightSum, MvPolynomial.coeff_X, Finsupp.single_left_inj, he] at hc

theorem outgoingWeightSum_ne_zero (F : FiniteFiberSystem V E) (u : V)
    (hu : 0 < F.outdegree u) : F.outgoingWeightSum u ≠ 0 := by
  classical
  have hc : 0 < Fintype.card (F.Outgoing u) := by
    rwa [F.card_outgoing]
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp hc
  exact F.outgoingWeightSum_ne_zero_of_edge u e.val e.property

theorem quotientBlock_elimination_det (F : FiniteFiberSystem V E)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (u : V) :
    (quotientBlock₁₁ F (F.eliminationCoordEquiv u)).det =
      F.outgoingWeightSum u ^ F.fiberDimension u := by
  rw [F.quotientBlock_elimination_scalar hloop u, Matrix.det_smul,
    Matrix.det_one, mul_one, F.card_coordAt]

end Positivity.FiniteFiberSystem
