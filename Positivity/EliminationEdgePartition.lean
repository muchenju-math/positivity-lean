import Positivity.VertexElimination

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def eliminationEdgePartition (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) :
    E ≃ F.Away u ⊕ (F.Incoming u ⊕ F.Outgoing u) where
  toFun e := if hs : F.src e = u then Sum.inr (Sum.inr ⟨e, hs⟩)
    else if ht : F.tgt e = u then Sum.inr (Sum.inl ⟨e, ht⟩)
    else Sum.inl ⟨e, hs, ht⟩
  invFun := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  left_inv e := by
    dsimp only
    split_ifs <;> rfl
  right_inv := by
    intro e
    rcases e with a | a | b
    · dsimp only [Sum.elim]
      rw [dif_neg a.property.1, dif_neg a.property.2]
    · have hs : F.src a.val ≠ u := fun h => hloop a.val (h.trans a.property.symm)
      dsimp only [Sum.elim]
      rw [dif_neg hs, dif_pos a.property]
    · dsimp only [Sum.elim]
      rw [dif_pos b.property]

theorem sum_eliminationEdgePartition {R : Type*} [AddCommMonoid R] [DecidableEq V]
    (F : FiniteFiberSystem V E) (u : V) (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (f : E → R) :
    (∑ e, f e) = (∑ a : F.Away u, f a.val) +
      (∑ a : F.Incoming u, f a.val) + ∑ b : F.Outgoing u, f b.val := by
  classical
  rw [← Equiv.sum_comp (F.eliminationEdgePartition u hloop).symm f]
  simp [Fintype.sum_sum_type, eliminationEdgePartition, add_assoc]

end Positivity.FiniteFiberSystem
