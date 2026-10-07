import Positivity.FiniteFiber

/-!
# Elimination in a loopless base

This file records the graph transformation used in Section 4.  An incoming
edge followed by a selected outgoing edge is replaced by a virtual edge
whose fiber map is the composition of the original maps.  The construction
keeps parallel edges distinct by retaining the incoming edge as the virtual
edge label.
-/

namespace Positivity

namespace FiniteFiberSystem

variable {V E : Type*} [Fintype V] [Fintype E]
variable (F : FiniteFiberSystem V E) (u : V)

/-- The edges entering `u`, with their original labels retained. -/
abbrev Incoming := {e : E // F.tgt e = u}

/-- The edges leaving `u`, with their original labels retained. -/
abbrev Outgoing := {e : E // F.src e = u}

/-- Edges whose source and target both survive deletion of `u`. -/
abbrev Away := {e : E // F.src e ≠ u ∧ F.tgt e ≠ u}

variable {F u}

/-- Delete `u` and all incident edges, then replace each incoming edge `a`
by one virtual edge.  The function `φ` chooses the outgoing edge paired with
each incoming edge.  The no-loop hypothesis ensures the source of every
incoming edge survives deletion.  Injectivity is not needed to define the
system; it is imposed by the coefficient recurrence in the paper. -/
noncomputable def eliminateSystem
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) :
    FiniteFiberSystem {v : V // v ≠ u}
      (Away F u ⊕ Incoming F u) := by
  classical
  letI : Fintype (Incoming F u) := inferInstance
  letI : Fintype (Outgoing F u) := inferInstance
  letI : Fintype (Away F u) := inferInstance
  refine
    { src := fun e => ?_
      tgt := fun e => ?_
      Fiber := fun v => F.Fiber v.1
      fiberFintype := fun v => F.fiberFintype v.1
      reference := fun v => F.reference v.1
      fiberMap := fun e => ?_ }
  · cases e with
    | inl e => exact ⟨F.src e.1, e.2.1⟩
    | inr e =>
        have hsrc : F.src e.1 ≠ u := by
          simpa [e.2] using hloop e.1
        exact ⟨F.src e.1, hsrc⟩
  · cases e with
    | inl e => exact ⟨F.tgt e.1, e.2.2⟩
    | inr e => exact ⟨F.tgt (φ e).1, by
        intro h
        have hs := (φ e).2
        exact hloop (φ e).1 (hs.trans h.symm)
      ⟩
  · intro e
    cases e with
    | inl e =>
        exact F.fiberMap e.1
    | inr e =>
        let mapIn : F.Fiber (F.src e.1) → F.Fiber u :=
          fun x => e.2 ▸ F.fiberMap e.1 x
        let mapOut : F.Fiber u → F.Fiber (F.tgt (φ e).1) :=
          fun x => (φ e).2 ▸ F.fiberMap (φ e).1 x
        exact mapOut ∘ mapIn

@[simp] theorem eliminateSystem_src_inl
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Away F u) :
    (eliminateSystem F u hloop φ).src (Sum.inl e) = ⟨F.src e.1, e.2.1⟩ := rfl

@[simp] theorem eliminateSystem_tgt_inl
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Away F u) :
    (eliminateSystem F u hloop φ).tgt (Sum.inl e) = ⟨F.tgt e.1, e.2.2⟩ := rfl

@[simp] theorem eliminateSystem_src_inr
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Incoming F u) :
    (eliminateSystem F u hloop φ).src (Sum.inr e) =
      ⟨F.src e.1, by simpa [e.2] using hloop e.1⟩ := rfl

@[simp] theorem eliminateSystem_tgt_inr
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Incoming F u) :
    (eliminateSystem F u hloop φ).tgt (Sum.inr e) =
      ⟨F.tgt (φ e).1, by
        intro h
        have hs := (φ e).2
        exact hloop (φ e).1 (hs.trans h.symm)⟩ := rfl

/-- The map carried by a virtual edge is the composite along its defining
two-edge path. -/
theorem eliminateSystem_virtual_map
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Incoming F u)
    (x : F.Fiber (F.src e.1)) :
    (eliminateSystem F u hloop φ).fiberMap (Sum.inr e) x =
      F.fiberMap (φ e).1 ((e.2 ▸ F.fiberMap e.1 x)) := by
  rfl

/-- The smaller system indexed by an injection of incoming edges into
outgoing edges. Keeping the injection as part of the index avoids choosing
enumerations of the finite edge types. -/
noncomputable def eliminateSystemInj
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u ↪ Outgoing F u) :
    FiniteFiberSystem {v : V // v ≠ u}
      (Away F u ⊕ Incoming F u) :=
  eliminateSystem F u hloop φ

@[simp] theorem eliminateSystemInj_virtual_map
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u ↪ Outgoing F u) (e : Incoming F u)
    (x : F.Fiber (F.src e.1)) :
    (eliminateSystemInj F u hloop φ).fiberMap (Sum.inr e) x =
      F.fiberMap (φ e).1 ((e.2 ▸ F.fiberMap e.1 x)) := by
  rfl

end FiniteFiberSystem

end Positivity
