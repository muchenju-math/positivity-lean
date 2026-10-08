import Positivity.EliminationCurry
import Positivity.CoefficientCurry
import Positivity.EliminationSelection
import Positivity.SumGroupedSquarefree

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem coeff_rename_squarefree_equiv {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]
    (e : A ≃ B) (P : MvPolynomial A R) :
    (MvPolynomial.rename e P).coeff squarefreeExponent = P.coeff squarefreeExponent := by
  classical
  have he : (squarefreeExponent (E := A)).mapDomain e = squarefreeExponent (E := B) := by
    ext b
    rw [Finsupp.mapDomain_equiv_apply]
    rfl
  rw [← he]
  exact MvPolynomial.coeff_rename_mapDomain e e.injective P _

namespace FiniteFiberSystem
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem coeff_eliminationCurry (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) :
    ((F.eliminationCurryHom u hloop F.quotientDeterminant).coeff squarefreeExponent).coeff
      squarefreeExponent = balancedCoefficient F := by
  change ((MvPolynomial.sumRingEquiv ℤ _ _
    (MvPolynomial.rename (F.eliminationVariableEquiv u hloop) F.quotientDeterminant)).coeff
      squarefreeExponent).coeff squarefreeExponent = _
  rw [coeff_sumRingEquiv_squarefree, coeff_rename_squarefree_equiv]
  rfl

theorem selectedExponent_eq_mapDomain (F : FiniteFiberSystem V E) (u : V)
    (τ : F.Incoming u → F.Outgoing u) :
    selectedExponent (C := F.Away u) τ =
      (squarefreeExponent (E := F.Away u ⊕ F.Incoming u)).mapDomain
        (F.selectionEdgeEmbedding u τ) := by
  classical
  ext x
  rw [Finsupp.mapDomain_apply, Finsupp.sum_fintype _ _ (by simp)]
  cases x with
  | inl a =>
    simp only [selectionEdgeEmbedding, Function.Embedding.coeFn_mk, Finsupp.single_apply]
    rw [Fintype.sum_sum_type]
    simp [squarefreeExponent, selectedExponent_inl]
  | inr ab =>
    rcases ab with ⟨a, b⟩
    simp only [Fintype.sum_sum_type, selectionEdgeEmbedding, Function.Embedding.coeFn_mk,
      Sum.map_inl, Sum.map_inr, id_eq, Finsupp.single_apply, Sum.inl.injEq,
      Sum.inr.injEq, Sum.inl_ne_inr, ite_false, Finset.sum_const_zero, zero_add,
      Prod.mk.injEq]
    rw [Finset.sum_eq_single a]
    · simp [selectedExponent_inr, squarefreeExponent]
    · intro a' _ ha'
      simp [ha']
    · simp

theorem coeff_auxiliary_selected (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (τ : F.Incoming u → F.Outgoing u) :
    (F.eliminateSystemAllCompositions u hloop).quotientDeterminant.coeff
      (selectedExponent τ) = balancedCoefficient (F.eliminateSystem (u := u) hloop τ) := by
  rw [selectedExponent_eq_mapDomain, coeff_selected_quotientDeterminant]

end FiniteFiberSystem
end Positivity
