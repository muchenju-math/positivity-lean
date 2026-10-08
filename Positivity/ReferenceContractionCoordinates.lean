import Positivity.ContractionCoordinates

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local simp] cast_eq eq_mpr_eq_cast cast_cast
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

theorem contractedInclude_reference_of_ne (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) (v : V) (hv : v ≠ u) :
    F.contractedInclude u p v ((F.contractMovedEdge u p q hpq).reference v) =
      F.reference v := by
  rw [contractMovedEdge_reference]
  simp [contractedInclude, contractedRedirect, hv]

theorem contractedInclude_reference_at_reference (F : FiniteFiberSystem V E) (u : V)
    (q : F.Fiber u) (hrq : F.reference u ≠ q) :
    F.contractedInclude u (F.reference u) u
      ((F.contractMovedEdge u (F.reference u) q hrq).reference u) = q := by
  rw [contractMovedEdge_reference]
  simp [contractedInclude, contractedRedirect, redirectValue]

theorem referenceContractionCoord_include_ne_reference (F : FiniteFiberSystem V E)
    (u : V) (q : F.Fiber u) (hrq : F.reference u ≠ q) (v : V)
    (i : (F.contractMovedEdge u (F.reference u) q hrq).CoordAt v) :
    F.contractedInclude u (F.reference u) v i.val ≠ F.reference v := by
  by_cases hv : v = u
  · subst v
    exact F.contractedInclude_ne u (F.reference u) i.val
  · intro h
    apply i.property
    apply F.contractedInclude_injective u (F.reference u) q hrq v
    exact h.trans (F.contractedInclude_reference_of_ne u (F.reference u) q hrq v hv).symm

noncomputable def referenceContractionCoordEmbedding (F : FiniteFiberSystem V E)
    (u : V) (q : F.Fiber u) (hrq : F.reference u ≠ q) :
    (F.contractMovedEdge u (F.reference u) q hrq).Coord ↪ F.Coord where
  toFun i := ⟨i.1, ⟨F.contractedInclude u (F.reference u) i.1 i.2.val,
    F.referenceContractionCoord_include_ne_reference u q hrq i.1 i.2⟩⟩
  inj' := by
    rintro ⟨v, i⟩ ⟨w, j⟩ h
    have hv : v = w := congrArg Sigma.fst h
    cases hv
    apply congrArg (Sigma.mk v)
    apply Subtype.ext
    apply F.contractedInclude_injective u (F.reference u) q hrq v
    exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

theorem referenceContractionCoordEmbedding_ne (F : FiniteFiberSystem V E)
    (u : V) (q : F.Fiber u) (hrq : F.reference u ≠ q)
    (i : (F.contractMovedEdge u (F.reference u) q hrq).Coord) :
    F.referenceContractionCoordEmbedding u q hrq i ≠ ⟨u, q, hrq.symm⟩ := by
  obtain ⟨v, i⟩ := i
  intro h
  have hv : v = u := congrArg Sigma.fst h
  subst v
  have heq : F.contractedInclude u (F.reference u) u i.val = q :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  apply i.property
  apply F.contractedInclude_injective u (F.reference u) q hrq u
  exact heq.trans (F.contractedInclude_reference_at_reference u q hrq).symm

noncomputable def referenceContractionCoordEquiv (F : FiniteFiberSystem V E)
    (u : V) (q : F.Fiber u) (hrq : F.reference u ≠ q) :
    (F.contractMovedEdge u (F.reference u) q hrq).Coord ≃
      {i : F.Coord // i ≠ ⟨u, q, hrq.symm⟩} := by
  classical
  let f : (F.contractMovedEdge u (F.reference u) q hrq).Coord →
      {i : F.Coord // i ≠ ⟨u, q, hrq.symm⟩} :=
    fun i => ⟨F.referenceContractionCoordEmbedding u q hrq i,
      F.referenceContractionCoordEmbedding_ne u q hrq i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact (F.referenceContractionCoordEmbedding u q hrq).injective (congrArg Subtype.val h)
  · rintro ⟨⟨v, x⟩, hi⟩
    have hx : ∀ h : v = u, cast (congrArg F.Fiber h) x.val ≠ F.reference u := by
      intro h
      subst v
      exact x.property
    let y := F.contractedRedirect u (F.reference u) q hrq v x.val
    have hy : F.contractedInclude u (F.reference u) v y = x.val :=
      F.contractedInclude_redirect_of_ne u (F.reference u) q hrq v x.val hx
    have hyr : y ≠ (F.contractMovedEdge u (F.reference u) q hrq).reference v := by
      intro h
      by_cases hv : v = u
      · subst v
        apply hi
        apply congrArg (Sigma.mk u)
        apply Subtype.ext
        rw [← hy, h, contractedInclude_reference_at_reference]
      · apply x.property
        rw [← hy, h, contractedInclude_reference_of_ne F u (F.reference u) q hrq v hv]
    refine ⟨⟨v, y, hyr⟩, ?_⟩
    apply Subtype.ext
    apply congrArg (Sigma.mk v)
    exact Subtype.ext hy

end Positivity.FiniteFiberSystem
