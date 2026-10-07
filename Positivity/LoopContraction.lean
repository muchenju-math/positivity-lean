import Positivity.FiniteFiber

/-!
# Contraction over a base loop

Formalization of the finite-fiber contraction used in Section 3.  A moved
lift `p → q` is contracted by removing `p`, and every surviving map whose
value was `p` is redirected to `q`.  Edge identities are retained, so
parallel edges remain distinct and the other lifts of the base loop are
still present after contraction.

The determinant derivative and coefficient recurrence require the forest
identity and a comparison of quotient determinants across different finite
coordinate types.  Those results are not asserted here until that comparison
is proved.
-/

namespace Positivity

open FiniteFiberSystem

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The contracted fiber over `v`.  At the contracted vertex, the element
`p` is removed; fibers over all other vertices are unchanged. -/
noncomputable def contractedFiber (F : FiniteFiberSystem V E) (u : V)
    (p : F.Fiber u) (v : V) : Type := by
  classical
  exact if h : v = u then {x : F.Fiber u // x ≠ p} else F.Fiber v

/-- Redirect a value equal to the deleted point to the retained point. -/
def redirectValue {α : Type*} [DecidableEq α] (p q : α) (hpq : p ≠ q)
    (x : α) : {y : α // y ≠ p} := by
  by_cases h : x = p
  · subst x
    exact ⟨q, hpq.symm⟩
  · exact ⟨x, h⟩

@[simp] theorem redirectValue_eq_of_ne {α : Type*} [DecidableEq α]
    (p q x : α) (hpq : p ≠ q) (h : x ≠ p) :
    redirectValue p q hpq x = ⟨x, h⟩ := by
  simp [redirectValue, h]

@[simp] theorem redirectValue_eq_of_eq {α : Type*} [DecidableEq α]
    (p q x : α) (hpq : p ≠ q) (h : x = p) :
    redirectValue p q hpq x = ⟨q, hpq.symm⟩ := by
  subst x
  simp [redirectValue, hpq]

/-- Contract a moved lifted edge `p → q` while retaining all base-edge
labels.  At the contracted vertex, maps are restricted to the surviving
source fiber and their target values are redirected along `p ↦ q`. -/
noncomputable def contractMovedEdge (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) : FiniteFiberSystem V E := by
  classical
  let CF : V → Type := fun v => F.contractedFiber u p v
  letI : ∀ v, Fintype (CF v) := by
    intro v
    by_cases h : v = u
    · simp only [CF, contractedFiber, dif_pos h]
      letI := F.fiberFintype u
      infer_instance
    · simp only [CF, contractedFiber, dif_neg h]
      exact F.fiberFintype v
  let cref : ∀ v, CF v := by
    intro v
    by_cases h : v = u
    · subst v
      exact ⟨q, hpq.symm⟩
    · exact F.reference v
  let cmap : ∀ e, CF (F.src e) → CF (F.tgt e) := by
    intro e x
    by_cases hs : F.src e = u
    · by_cases ht : F.tgt e = u
      · simp only [CF, contractedFiber, dif_pos hs, dif_pos ht] at x ⊢
        exact redirectValue p q hpq (ht ▸ F.fiberMap e (hs.symm ▸ x.1))
      · simp only [CF, contractedFiber, dif_pos hs, dif_neg ht] at x ⊢
        exact F.fiberMap e (hs.symm ▸ x.1)
    · by_cases ht : F.tgt e = u
      · simp only [CF, contractedFiber, dif_neg hs, dif_pos ht] at x ⊢
        exact redirectValue p q hpq (ht ▸ F.fiberMap e x)
      · simp only [CF, contractedFiber, dif_neg hs, dif_neg ht] at x ⊢
        exact F.fiberMap e x
  exact {
    src := F.src
    tgt := F.tgt
    Fiber := CF
    fiberFintype := fun v => by infer_instance
    reference := cref
    fiberMap := cmap
  }

/-- The contracted fiber at the base-loop vertex is exactly the subtype
obtained by deleting the source sheet. -/
@[simp] theorem contractedFiber_at (F : FiniteFiberSystem V E) (u : V)
    (p : F.Fiber u) : F.contractedFiber u p u = {x : F.Fiber u // x ≠ p} := by
  classical
  simp [contractedFiber]

/-- In the contracted system, an edge with both endpoints at the contracted
vertex acts by the original fiber map followed by `p ↦ q`. -/
theorem contractMovedEdge_loopMap (F : FiniteFiberSystem V E) (u : V)
    (e : E) (heSrc : F.src e = u) (heTgt : F.tgt e = u)
    (p q : F.Fiber u) (hpq : p ≠ q) (x : (F.contractMovedEdge u p q hpq).Fiber (F.src e)) :
    (F.contractMovedEdge u p q hpq).fiberMap e x =
      redirectValue p q hpq (heTgt ▸ F.fiberMap e (heSrc.symm ▸ x.1)) := by
  classical
  simp [contractMovedEdge, heSrc, heTgt]

end Positivity
