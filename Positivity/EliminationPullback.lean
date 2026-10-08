import Positivity.VertexElimination
import Positivity.NormalizedPullback

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def incomingPullbackAt (F : FiniteFiberSystem V E) (u : V)
    (a : F.Incoming u) : Matrix (F.CoordAt (F.src a.val)) (F.CoordAt u) ℤ :=
  normalizedPullback (F.reference (F.src a.val)) (F.reference u)
    (fun x => a.property ▸ F.fiberMap a.val x)

noncomputable def outgoingPullbackAt (F : FiniteFiberSystem V E) (u : V)
    (b : F.Outgoing u) : Matrix (F.CoordAt u) (F.CoordAt (F.tgt b.val)) ℤ :=
  normalizedPullback (F.reference u) (F.reference (F.tgt b.val))
    (fun x => F.fiberMap b.val (b.property.symm ▸ x))

/-- The pullback on every virtual edge is exactly the product of the two
pullbacks along the incoming and outgoing edges. -/
theorem eliminateSystemAllCompositions_pullback [DecidableEq V] [DecidableEq E]
    (F : FiniteFiberSystem V E) (u : V) (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (a : F.Incoming u) (b : F.Outgoing u) :
    F.incomingPullbackAt u a * F.outgoingPullbackAt u b =
      (F.eliminateSystemAllCompositions u hloop).pullback (Sum.inr (a, b)) := by
  classical
  letI := F.fiberFintype u
  change (normalizedPullback (F.reference (F.src a.val)) (F.reference u)
      (fun x => a.property ▸ F.fiberMap a.val x) : Matrix _ _ ℤ) *
      normalizedPullback (F.reference u) (F.reference (F.tgt b.val))
        (fun x => F.fiberMap b.val (b.property.symm ▸ x)) =
    normalizedPullback (F.reference (F.src a.val)) (F.reference (F.tgt b.val))
      (fun x => F.fiberMap b.val (b.property.symm ▸ (a.property ▸ F.fiberMap a.val x)))
  exact normalizedPullback_comp _ _ _ _ _

end Positivity.FiniteFiberSystem
