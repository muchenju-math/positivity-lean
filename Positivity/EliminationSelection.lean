import Positivity.EliminationEvaluation
import Positivity.MainTheorem

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem killCompl_X_of_not_mem_range {α β R : Type*} [CommSemiring R]
    (f : α ↪ β) (b : β) (hb : b ∉ Set.range f) :
    MvPolynomial.killCompl f.injective (MvPolynomial.X b : MvPolynomial β R) = 0 := by
  classical
  simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X]
  exact dif_neg hb

theorem killCompl_X_embedding {α β R : Type*} [CommSemiring R]
    (f : α ↪ β) (a : α) :
    MvPolynomial.killCompl f.injective (MvPolynomial.X (f a) : MvPolynomial β R) =
      MvPolynomial.X a := by
  simpa only [MvPolynomial.rename_X] using
    MvPolynomial.killCompl_rename_app f.injective (MvPolynomial.X a : MvPolynomial α R)

theorem killCompl_sum_X_mul_C {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R]
    (f : α ↪ β) (c : β → R) :
    MvPolynomial.killCompl f.injective (∑ b, MvPolynomial.X b * MvPolynomial.C (c b)) =
      ∑ a, MvPolynomial.X a * MvPolynomial.C (c (f a)) := by
  classical
  simp only [map_sum, map_mul, MvPolynomial.killCompl_C]
  symm
  apply Finset.sum_bij_ne_zero (fun a _ _ => f a)
  · intros; exact Finset.mem_univ _
  · intros; apply f.injective; assumption
  · intro b _ hb
    have hr : b ∈ Set.range f := by
      by_contra hn
      rw [killCompl_X_of_not_mem_range f b hn, zero_mul] at hb
      exact hb rfl
    obtain ⟨a, rfl⟩ := hr
    exact ⟨a, Finset.mem_univ _, by simpa only [killCompl_X_embedding] using hb, rfl⟩
  · intro a _ _
    rw [killCompl_X_embedding]

namespace FiniteFiberSystem
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def selectionEdgeEmbedding (F : FiniteFiberSystem V E) (u : V)
    (τ : F.Incoming u → F.Outgoing u) :
    (F.Away u ⊕ F.Incoming u) ↪ (F.Away u ⊕ (F.Incoming u × F.Outgoing u)) where
  toFun := Sum.map id (fun a => (a, τ a))
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all

theorem selected_quotientEdgeCoefficient (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (τ : F.Incoming u → F.Outgoing u)
    (a : F.Away u ⊕ F.Incoming u)
    (i j : (F.eliminateSystem (u := u) hloop τ).Coord) :
    (F.eliminateSystemAllCompositions u hloop).quotientEdgeCoefficient
      (F.selectionEdgeEmbedding u τ a) i j =
    (F.eliminateSystem (u := u) hloop τ).quotientEdgeCoefficient a i j := by
  cases a <;> rfl

theorem selection_quotientLaplacian (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (τ : F.Incoming u → F.Outgoing u)
    (i j : (F.eliminateSystem (u := u) hloop τ).Coord) :
    MvPolynomial.killCompl (F.selectionEdgeEmbedding u τ).injective
      ((F.eliminateSystemAllCompositions u hloop).quotientLaplacian i j) =
    (F.eliminateSystem (u := u) hloop τ).quotientLaplacian i j := by
  change MvPolynomial.killCompl _ (∑ a, MvPolynomial.X a * MvPolynomial.C
    ((F.eliminateSystemAllCompositions u hloop).quotientEdgeCoefficient a i j)) = _
  rw [killCompl_sum_X_mul_C]
  apply Finset.sum_congr rfl
  intro a _
  rw [selected_quotientEdgeCoefficient]

theorem selection_quotientDeterminant (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (τ : F.Incoming u → F.Outgoing u) :
    MvPolynomial.killCompl (F.selectionEdgeEmbedding u τ).injective
      (F.eliminateSystemAllCompositions u hloop).quotientDeterminant =
    (F.eliminateSystem (u := u) hloop τ).quotientDeterminant := by
  change MvPolynomial.killCompl _ (F.eliminateSystemAllCompositions u hloop).quotientLaplacian.det = _
  rw [AlgHom.map_det]
  congr 1
  funext i j
  exact F.selection_quotientLaplacian u hloop τ i j

theorem coeff_selected_quotientDeterminant (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (τ : F.Incoming u → F.Outgoing u) :
    (F.eliminateSystemAllCompositions u hloop).quotientDeterminant.coeff
      ((squarefreeExponent (E := F.Away u ⊕ F.Incoming u)).mapDomain
        (F.selectionEdgeEmbedding u τ)) =
    balancedCoefficient (F.eliminateSystem (u := u) hloop τ) := by
  rw [← MvPolynomial.coeff_killCompl (F.selectionEdgeEmbedding u τ).injective,
    selection_quotientDeterminant]
  rfl

end FiniteFiberSystem
end Positivity
