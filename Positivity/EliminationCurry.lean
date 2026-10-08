import Positivity.EliminationLocalization
import Positivity.EliminationEdgePartition

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def eliminationVariableEquiv (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) :
    E ≃ (F.Away u ⊕ F.Incoming u) ⊕ F.Outgoing u :=
  (F.eliminationEdgePartition u hloop).trans (Equiv.sumAssoc _ _ _).symm

noncomputable def eliminationCurryHom (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) :
    MvPolynomial E ℤ →+* MvPolynomial (F.Away u ⊕ F.Incoming u) (MvPolynomial (F.Outgoing u) ℤ) :=
  (MvPolynomial.sumRingEquiv ℤ _ _).toRingHom.comp
    (MvPolynomial.rename (F.eliminationVariableEquiv u hloop)).toRingHom

theorem eliminationVariableEquiv_away (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (a : F.Away u) :
    F.eliminationVariableEquiv u hloop a.val = Sum.inl (Sum.inl a) := by
  exact (F.eliminationVariableEquiv u hloop).eq_symm_apply.mp rfl

theorem eliminationCurryHom_X_away (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (a : F.Away u) :
    F.eliminationCurryHom u hloop (MvPolynomial.X a.val) = MvPolynomial.X (Sum.inl a) := by
  have he : F.eliminationVariableEquiv u hloop a.val = Sum.inl (Sum.inl a) :=
    (F.eliminationVariableEquiv u hloop).eq_symm_apply.mp rfl
  simp [eliminationCurryHom, he]

theorem eliminationCurryHom_X_incoming (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (a : F.Incoming u) :
    F.eliminationCurryHom u hloop (MvPolynomial.X a.val) = MvPolynomial.X (Sum.inr a) := by
  have he : F.eliminationVariableEquiv u hloop a.val = Sum.inl (Sum.inr a) :=
    (F.eliminationVariableEquiv u hloop).eq_symm_apply.mp rfl
  simp [eliminationCurryHom, he]

theorem eliminationCurryHom_X_outgoing (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (b : F.Outgoing u) :
    F.eliminationCurryHom u hloop (MvPolynomial.X b.val) = MvPolynomial.C (MvPolynomial.X b) := by
  have he : F.eliminationVariableEquiv u hloop b.val = Sum.inr b :=
    (F.eliminationVariableEquiv u hloop).eq_symm_apply.mp rfl
  simp [eliminationCurryHom, he]

theorem eliminationCurryHom_outgoingWeightSum (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) :
    F.eliminationCurryHom u hloop (F.outgoingWeightSum u) =
      MvPolynomial.C (∑ b : F.Outgoing u, MvPolynomial.X b) := by
  rw [map_outgoingWeightSum]
  simp only [eliminationCurryHom_X_outgoing, map_sum]

end Positivity.FiniteFiberSystem
