import Positivity.LoopDirections
import Positivity.DeterminantCompression

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local simp] cast_eq eq_mpr_eq_cast cast_cast
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Include a surviving sheet into the original fiber. -/
noncomputable def contractedInclude (F : FiniteFiberSystem V E) (u : V)
    (p : F.Fiber u) (v : V) (x : F.contractedFiber u p v) : F.Fiber v := by
  classical
  by_cases h : v = u
  · exact cast (congrArg F.Fiber h.symm)
      (cast (by simp [contractedFiber, h]) x : {x : F.Fiber u // x ≠ p}).val
  · exact cast (by simp [contractedFiber, h]) x

/-- Redirect the removed sheet, at its vertex, to the retained sheet. -/
noncomputable def contractedRedirect (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (v : V) (x : F.Fiber v) :
    F.contractedFiber u p v := by
  classical
  by_cases h : v = u
  · exact cast (by simp [contractedFiber, h])
      (redirectValue p q hpq (cast (congrArg F.Fiber h) x))
  · exact cast (by simp [contractedFiber, h]) x

theorem contractedRedirect_include (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (v : V) (x : F.contractedFiber u p v) :
    F.contractedRedirect u p q hpq v (F.contractedInclude u p v x) = x := by
  classical
  by_cases h : v = u
  · subst v
    have hx := (cast (F.contractedFiber_at u p) x).property
    simp_all [contractedRedirect, contractedInclude, contractedFiber, redirectValue]
  · simp [contractedRedirect, contractedInclude, contractedFiber, h]

theorem contractedInclude_injective (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (v : V) :
    Function.Injective (F.contractedInclude u p v) :=
  Function.LeftInverse.injective (F.contractedRedirect_include u p q hpq v)

theorem contractMovedEdge_reference (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (v : V) :
    (F.contractMovedEdge u p q hpq).reference v =
      F.contractedRedirect u p q hpq v (F.reference v) := by
  classical
  by_cases h : v = u
  · subst v
    simp [contractMovedEdge, contractedRedirect, contractedFiber]
  · simp [contractMovedEdge, contractedRedirect, contractedFiber, h]

theorem contractedInclude_reference (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (hp : p ≠ F.reference u) (v : V) :
    F.contractedInclude u p v ((F.contractMovedEdge u p q hpq).reference v) =
      F.reference v := by
  classical
  rw [contractMovedEdge_reference]
  by_cases h : v = u
  · subst v
    simp [contractedInclude, contractedRedirect, contractedFiber, Ne.symm hp]
  · simp [contractedInclude, contractedRedirect, contractedFiber, h]

theorem contractMovedEdge_map (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (e : E)
    (x : F.contractedFiber u p (F.src e)) :
    (F.contractMovedEdge u p q hpq).fiberMap e x =
      F.contractedRedirect u p q hpq (F.tgt e)
        (F.fiberMap e (F.contractedInclude u p (F.src e) x)) := by
  classical
  by_cases hs : F.src e = u <;> by_cases ht : F.tgt e = u <;>
    simp [contractMovedEdge, contractedRedirect, contractedInclude, contractedFiber,
      hs, ht, eqRec_eq_cast]

/-- Surviving quotient coordinates embed into the original coordinates
when the original reference point survives. -/
noncomputable def contractionCoordEmbedding (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (hp : p ≠ F.reference u) :
    (F.contractMovedEdge u p q hpq).Coord ↪ F.Coord where
  toFun i := ⟨i.1, ⟨F.contractedInclude u p i.1 i.2.val, by
    intro h
    apply i.2.property
    apply F.contractedInclude_injective u p q hpq i.1
    exact h.trans (F.contractedInclude_reference u p q hpq hp i.1).symm⟩⟩
  inj' := by
    rintro ⟨v, i⟩ ⟨w, j⟩ h
    have hv : v = w := congrArg Sigma.fst h
    cases hv
    apply congrArg (Sigma.mk v)
    apply Subtype.ext
    apply F.contractedInclude_injective u p q hpq v
    exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

theorem contractedInclude_ne (F : FiniteFiberSystem V E) (u : V)
    (p : F.Fiber u) (x : F.contractedFiber u p u) :
    F.contractedInclude u p u x ≠ p := by
  classical
  simpa [contractedInclude] using (cast (F.contractedFiber_at u p) x).property

theorem contractionCoordEmbedding_ne (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (hp : p ≠ F.reference u)
    (i : (F.contractMovedEdge u p q hpq).Coord) :
    F.contractionCoordEmbedding u p q hpq hp i ≠ ⟨u, p, hp⟩ := by
  classical
  obtain ⟨v, i⟩ := i
  intro h
  have hv : v = u := congrArg Sigma.fst h
  subst v
  apply F.contractedInclude_ne u p i.val
  exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

theorem contractedInclude_redirect_of_ne (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (v : V) (x : F.Fiber v)
    (hx : ∀ h : v = u, cast (congrArg F.Fiber h) x ≠ p) :
    F.contractedInclude u p v (F.contractedRedirect u p q hpq v x) = x := by
  classical
  by_cases h : v = u
  · subst v
    have hx' : x ≠ p := hx rfl
    simp [contractedInclude, contractedRedirect, hx']
  · simp [contractedInclude, contractedRedirect, h]

/-- Deleting a nonreference sheet deletes exactly its quotient coordinate. -/
noncomputable def contractionCoordEquiv (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (hp : p ≠ F.reference u) :
    (F.contractMovedEdge u p q hpq).Coord ≃ {i : F.Coord // i ≠ ⟨u, p, hp⟩} := by
  classical
  let f : (F.contractMovedEdge u p q hpq).Coord → {i : F.Coord // i ≠ ⟨u, p, hp⟩} :=
    fun i => ⟨F.contractionCoordEmbedding u p q hpq hp i,
      F.contractionCoordEmbedding_ne u p q hpq hp i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact (F.contractionCoordEmbedding u p q hpq hp).injective (congrArg Subtype.val h)
  · rintro ⟨⟨v, x⟩, hi⟩
    have hx : ∀ h : v = u, cast (congrArg F.Fiber h) x.val ≠ p := by
      intro h
      subst v
      intro heq
      apply hi
      apply congrArg (Sigma.mk u)
      exact Subtype.ext heq
    let y := F.contractedRedirect u p q hpq v x.val
    have hy : F.contractedInclude u p v y = x.val :=
      F.contractedInclude_redirect_of_ne u p q hpq v x.val hx
    have hyr : y ≠ (F.contractMovedEdge u p q hpq).reference v := by
      intro h
      apply x.property
      rw [← hy, h, contractedInclude_reference F u p q hpq hp v]
    refine ⟨⟨v, y, hyr⟩, ?_⟩
    apply Subtype.ext
    apply congrArg (Sigma.mk v)
    exact Subtype.ext hy

theorem redirectValue_delta {α : Type*} [DecidableEq α]
    (p q : α) (hpq : p ≠ q) (x : α) (y : {x : α // x ≠ p}) :
    (if redirectValue p q hpq x = y then (1 : ℤ) else 0) =
      (if x = y.val then 1 else 0) +
        (if x = p then 1 else 0) * (if q = y.val then 1 else 0) := by
  by_cases hx : x = p
  · subst x
    simp [redirectValue, Subtype.ext_iff, Ne.symm y.property]
  · simp [redirectValue, hx, Subtype.ext_iff]

theorem contractedRedirect_delta (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (v : V) (x : F.Fiber v)
    (y : F.contractedFiber u p v) :
    (if F.contractedRedirect u p q hpq v x = y then (1 : ℤ) else 0) =
      (if x = F.contractedInclude u p v y then 1 else 0) +
        (if (⟨v, x⟩ : Sigma F.Fiber) = ⟨u, p⟩ then 1 else 0) *
        (if (⟨v, F.contractedInclude u p v y⟩ : Sigma F.Fiber) = ⟨u, q⟩ then 1 else 0) := by
  classical
  by_cases hv : v = u
  · subst v
    obtain ⟨y, rfl⟩ := (Equiv.cast (F.contractedFiber_at u p).symm).surjective y
    simpa [contractedRedirect, contractedInclude, cast_inj, Sigma.mk.inj_iff, eq_comm] using
      redirectValue_delta p q hpq x y
  · have hp' : (⟨v, x⟩ : Sigma F.Fiber) ≠ ⟨u, p⟩ :=
      fun h => hv (congrArg Sigma.fst h)
    have ht : F.contractedFiber u p v = F.Fiber v := by simp [contractedFiber, hv]
    obtain ⟨y, rfl⟩ := (Equiv.cast ht.symm).surjective y
    simp [contractedRedirect, contractedInclude, hv, hp', cast_inj]

end Positivity.FiniteFiberSystem
