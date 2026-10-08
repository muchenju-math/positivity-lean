import Positivity.FiniteFiber
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Elimination in a loopless base

This file records the graph transformation used in Section 4.  An incoming
edge followed by a selected outgoing edge is replaced by a virtual edge
whose fiber map is the composition of the original maps.  The construction
keeps parallel edges distinct by retaining the incoming edge as the virtual
edge label.
-/

namespace Positivity

/-- The determinant identity for a block matrix with an invertible
top-left block. -/
theorem schurDeterminantIdentity
    {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [CommRing R]
    (A : Matrix ι ι R) (B : Matrix ι κ R)
    (C : Matrix κ ι R) (D : Matrix κ κ R) [Invertible A] :
    Matrix.det (Matrix.fromBlocks A B C D) =
      Matrix.det A * Matrix.det (D - C * ⅟ A * B) := by
  exact Matrix.det_fromBlocks₁₁ A B C D

/-- Scalar-diagonal instance of the Schur identity.  The hypothesis makes
the scalar block invertible in the ambient commutative ring. -/
theorem schurScalarBlockDeterminantIdentity
    {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [CommRing R]
    (s : R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (D : Matrix κ κ R)
    [Invertible (s • (1 : Matrix ι ι R))] :
    Matrix.det (Matrix.fromBlocks (s • (1 : Matrix ι ι R)) B C D) =
      Matrix.det (s • (1 : Matrix ι ι R)) *
        Matrix.det
          (D - C * ⅟ (s • (1 : Matrix ι ι R)) * B) := by
  exact schurDeterminantIdentity (s • (1 : Matrix ι ι R)) B C D

/-- The four blocks of the quotient Laplacian after any chosen equivalence
of its coordinates with a sum type. -/
noncomputable def quotientBlock₁₁
    {V E α β : Type*} [Fintype V] [Fintype E]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : FiniteFiberSystem V E) (e : F.Coord ≃ α ⊕ β) :
    Matrix α α (MvPolynomial E ℤ) :=
  fun i j => F.quotientLaplacian (e.symm (Sum.inl i)) (e.symm (Sum.inl j))

noncomputable def quotientBlock₁₂
    {V E α β : Type*} [Fintype V] [Fintype E]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : FiniteFiberSystem V E) (e : F.Coord ≃ α ⊕ β) :
    Matrix α β (MvPolynomial E ℤ) :=
  fun i j => F.quotientLaplacian (e.symm (Sum.inl i)) (e.symm (Sum.inr j))

noncomputable def quotientBlock₂₁
    {V E α β : Type*} [Fintype V] [Fintype E]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : FiniteFiberSystem V E) (e : F.Coord ≃ α ⊕ β) :
    Matrix β α (MvPolynomial E ℤ) :=
  fun i j => F.quotientLaplacian (e.symm (Sum.inr i)) (e.symm (Sum.inl j))

noncomputable def quotientBlock₂₂
    {V E α β : Type*} [Fintype V] [Fintype E]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : FiniteFiberSystem V E) (e : F.Coord ≃ α ⊕ β) :
    Matrix β β (MvPolynomial E ℤ) :=
  fun i j => F.quotientLaplacian (e.symm (Sum.inr i)) (e.symm (Sum.inr j))

/-- Once a coordinate split identifies the quotient matrix with its four
blocks and the first block is invertible, its determinant obeys the Schur
complement identity. This is the matrix-level interface for applying
vertex elimination to `FiniteFiberSystem.quotientLaplacian`. -/
theorem quotientDeterminant_schur
    {V E α β : Type*} [Fintype V] [Fintype E]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : FiniteFiberSystem V E) (e : F.Coord ≃ α ⊕ β)
    [Invertible (quotientBlock₁₁ F e)] :
    F.quotientDeterminant =
      Matrix.det (quotientBlock₁₁ F e) *
        Matrix.det
          (quotientBlock₂₂ F e -
            quotientBlock₂₁ F e * ⅟ (quotientBlock₁₁ F e) *
              quotientBlock₁₂ F e) := by
  let A := quotientBlock₁₁ F e
  let B := quotientBlock₁₂ F e
  let C := quotientBlock₂₁ F e
  let D := quotientBlock₂₂ F e
  have hblocks : Matrix.reindex e e F.quotientLaplacian =
      Matrix.fromBlocks A B C D := by
    ext i j
    cases i <;> cases j <;> rfl
  calc
    F.quotientDeterminant = Matrix.det F.quotientLaplacian := rfl
    _ = Matrix.det (Matrix.reindex e e F.quotientLaplacian) :=
      (Matrix.det_reindex_self e F.quotientLaplacian).symm
    _ = Matrix.det (Matrix.fromBlocks A B C D) := by rw [hblocks]
    _ = Matrix.det A * Matrix.det (D - C * ⅟ A * B) :=
      Matrix.det_fromBlocks₁₁ A B C D
    _ = Matrix.det (quotientBlock₁₁ F e) *
        Matrix.det
          (quotientBlock₂₂ F e -
            quotientBlock₂₁ F e * ⅟ (quotientBlock₁₁ F e) *
              quotientBlock₁₂ F e) := by rfl

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

/-- Incoming degree, counting parallel edges separately. -/
noncomputable def indegree (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter fun e : E => F.tgt e = v).card

/-- Incoming labels enumerate the edges counted by the indegree. -/
theorem card_incoming [DecidableEq V] (v : V) : Fintype.card (F.Incoming v) = F.indegree v := by
  classical
  letI : Fintype (F.Incoming v) := inferInstance
  simp [FiniteFiberSystem.Incoming, FiniteFiberSystem.indegree,
    Fintype.card_subtype] <;> (congr 1 <;> ext e <;> simp)

/-- Outgoing labels enumerate the edges counted by the outdegree. -/
theorem card_outgoing [DecidableEq V] (v : V) : Fintype.card (F.Outgoing v) = F.outdegree v := by
  classical
  letI : Fintype (F.Outgoing v) := inferInstance
  change Fintype.card {e : E // F.src e = v} = Nat.card {e : E // F.src e = v}
  exact Nat.card_eq_fintype_card.symm

/-- A degree inequality supplies an injection pairing each incoming edge
with a distinct outgoing edge. -/
theorem exists_incoming_embedding [DecidableEq V]
    (v : V) (h : F.indegree v ≤ F.outdegree v) :
    Nonempty (F.Incoming v ↪ F.Outgoing v) := by
  classical
  letI : Fintype (F.Incoming v) := inferInstance
  letI : Fintype (F.Outgoing v) := inferInstance
  apply Function.Embedding.nonempty_of_card_le
  rw [F.card_incoming, F.card_outgoing]
  exact h

private theorem sum_filter_le_univ (p : V → Prop) [DecidablePred p]
    (f : V → ℕ) :
    (∑ v ∈ Finset.univ.filter p, f v) ≤ ∑ v, f v := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ) p]
  exact Nat.le_add_right _ _

private theorem sum_filter_eq_univ_of_zero_off
    (p : V → Prop) [DecidablePred p] (f : V → ℕ)
    (hoff : ∀ v, ¬ p v → f v = 0) :
    (∑ v ∈ Finset.univ.filter p, f v) = ∑ v, f v := by
  classical
  have hzero : (∑ v ∈ Finset.univ.filter (fun v => ¬ p v), f v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact hoff v (Finset.mem_filter.mp hv).2
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ) p, hzero, add_zero]

/-- Summing the outdegrees counts every edge exactly once. -/
theorem sum_outdegree_eq_card :
    (∑ v : V, F.outdegree v) = Fintype.card E := by
  classical
  let SrcFiber : V → Type _ := fun v => {e : E // F.src e = v}
  let edgeEquiv : (Σ v : V, SrcFiber v) ≃ E := Equiv.sigmaFiberEquiv F.src
  calc
    (∑ v : V, F.outdegree v) =
        ∑ v : V, Fintype.card (SrcFiber v) := by
      apply Finset.sum_congr rfl
      intro v hv
      change F.outdegree v = Fintype.card (SrcFiber v)
      simp [FiniteFiberSystem.outdegree, SrcFiber, Fintype.card_subtype]
    _ = Fintype.card (Σ v : V, SrcFiber v) := by simp
    _ = Fintype.card E := Fintype.card_congr edgeEquiv

/-- Balance identifies the quotient dimension with the number of base
edges. This gives the dimension-decreasing induction its finite measure. -/
theorem Balanced.card_edges_eq_totalDimension
    (hF : F.Balanced) : Fintype.card E = F.totalDimension := by
  classical
  calc
    Fintype.card E = ∑ v : V, F.outdegree v := F.sum_outdegree_eq_card.symm
    _ = ∑ v : V, F.fiberDimension v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hF v
    _ = F.totalDimension := F.totalDimension_eq_sum_fiberDimension.symm

/-- In a balanced system of zero quotient dimension, every fiber has zero
quotient dimension. -/
theorem Balanced.fiberDimension_eq_zero_of_totalDimension_eq_zero
    (hF : F.Balanced) (hD : F.totalDimension = 0) (v : V) :
    F.fiberDimension v = 0 := by
  classical
  have hsum : (∑ w : V, F.fiberDimension w) = 0 := by
    rw [← F.totalDimension_eq_sum_fiberDimension, hD]
  have hle : F.fiberDimension v ≤ ∑ w : V, F.fiberDimension w := by
    exact Finset.single_le_sum (fun w hw => Nat.zero_le _) (Finset.mem_univ v)
  omega

/-- The base case of the balanced induction has no edges. -/
theorem Balanced.edge_card_eq_zero_of_totalDimension_eq_zero
    (hF : F.Balanced) (hD : F.totalDimension = 0) : Fintype.card E = 0 := by
  rw [hF.card_edges_eq_totalDimension, hD]

/-- Summing the indegrees also counts every edge exactly once. -/
theorem sum_indegree_eq_card :
    (∑ v : V, F.indegree v) = Fintype.card E := by
  classical
  let TgtFiber : V → Type _ := fun v => {e : E // F.tgt e = v}
  let edgeEquiv : (Σ v : V, TgtFiber v) ≃ E := Equiv.sigmaFiberEquiv F.tgt
  calc
    (∑ v : V, F.indegree v) =
        ∑ v : V, Fintype.card (TgtFiber v) := by
      apply Finset.sum_congr rfl
      intro v hv
      change F.indegree v = Fintype.card (TgtFiber v)
      simp [FiniteFiberSystem.indegree, TgtFiber, Fintype.card_subtype]
    _ = Fintype.card (Σ v : V, TgtFiber v) := by simp
    _ = Fintype.card E := Fintype.card_congr edgeEquiv

/-- A finite-sum selection principle: if the sum of `f` on `S` is at most
the sum of a strictly positive `g`, then some point has `f ≤ g`. -/
theorem exists_mem_le_of_sum_le_sum
    (S : Finset V) (f g : V → ℕ)
    (hS : S.Nonempty) (hg : ∀ v ∈ S, 0 < g v)
    (hsum : (∑ v ∈ S, f v) ≤ ∑ v ∈ S, g v) :
    ∃ v ∈ S, f v ≤ g v := by
  classical
  by_contra h
  push_neg at h
  have hstrict : ∑ v ∈ S, g v < ∑ v ∈ S, f v := by
    apply Finset.sum_lt_sum
    · intro v hv
      exact Nat.le_of_lt (h v hv)
    · obtain ⟨v, hv⟩ := hS
      exact ⟨v, hv, h v hv⟩
  omega

/-- The core vertex-selection lemma from Section 4, isolated from the graph
counting identities: the index set is the vertices of positive outdegree. -/
theorem exists_positiveOutdegree_with_indegree_le
    (S : Finset V) (hS : S.Nonempty)
    (hpositive : ∀ v ∈ S, 0 < F.outdegree v)
    (hbound : (∑ v ∈ S, F.indegree v) ≤ ∑ v ∈ S, F.outdegree v) :
    ∃ v ∈ S, F.indegree v ≤ F.outdegree v :=
  exists_mem_le_of_sum_le_sum S F.indegree F.outdegree hS hpositive hbound

/-- Every finite directed multigraph with an edge has a vertex of positive
outdegree whose indegree is at most its outdegree. -/
theorem exists_elimination_vertex [DecidableEq V] [DecidableEq E]
    (hE : Nonempty E) :
    ∃ u, 0 < F.outdegree u ∧ F.indegree u ≤ F.outdegree u := by
  classical
  let positive : Finset V := Finset.univ.filter fun v => 0 < F.outdegree v
  have hnonempty : positive.Nonempty := by
    obtain ⟨e⟩ := hE
    refine ⟨F.src e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    unfold FiniteFiberSystem.outdegree
    apply Nat.card_pos_iff.mpr
    exact ⟨⟨⟨e, rfl⟩⟩, inferInstance⟩
  have hpos : ∀ v ∈ positive, 0 < F.outdegree v := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hinBound :
      (∑ v ∈ positive, F.indegree v) ≤ ∑ v : V, F.indegree v := by
    exact sum_filter_le_univ (fun v => 0 < F.outdegree v) F.indegree
  have houtEq : (∑ v ∈ positive, F.outdegree v) = ∑ v : V, F.outdegree v := by
    apply sum_filter_eq_univ_of_zero_off
    intro v hv
    have hnot : ¬ 0 < F.outdegree v := hv
    omega
  have hsum :
      (∑ v ∈ positive, F.indegree v) ≤ ∑ v ∈ positive, F.outdegree v := by
    rw [houtEq]
    calc
      (∑ v ∈ positive, F.indegree v) ≤ ∑ v : V, F.indegree v := hinBound
      _ = Fintype.card E := F.sum_indegree_eq_card
      _ = ∑ v : V, F.outdegree v := F.sum_outdegree_eq_card.symm
  obtain ⟨u, hu, hle⟩ :=
    exists_positiveOutdegree_with_indegree_le (F := F) positive hnonempty hpos hsum
  exact ⟨u, hpos u hu, hle⟩

/-- Delete `u` and all incident edges, then replace each incoming edge `a`
by one virtual edge.  The function `φ` chooses the outgoing edge paired with
each incoming edge.  The no-loop hypothesis ensures the source of every
incoming edge survives deletion.  Injectivity is not needed to define the
system; it is imposed by the coefficient recurrence in the paper. -/
noncomputable def eliminateSystem
    [DecidableEq V] [DecidableEq E]
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
          intro hs
          apply hloop e.1
          exact hs.trans e.2.symm
        exact ⟨F.src e.1, hsrc⟩
  · cases e with
    | inl e => exact ⟨F.tgt e.1, e.2.2⟩
    | inr e => exact ⟨F.tgt (φ e).1, by
        intro h
        have hs := (φ e).2
        exact hloop (φ e).1 (hs.trans h.symm)
      ⟩
  · intro x
    cases e with
    | inl e =>
        exact F.fiberMap e.1 x
    | inr e =>
        let mapIn : F.Fiber (F.src e.1) → F.Fiber u :=
          fun x => e.2 ▸ F.fiberMap e.1 x
        let mapOut : F.Fiber u → F.Fiber (F.tgt (φ e).1) :=
          fun x => F.fiberMap (φ e).1 ((φ e).2.symm ▸ x)
        exact mapOut (mapIn x)

@[simp] theorem eliminateSystem_src_inl
    [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Away F u) :
    (eliminateSystem (F := F) (u := u) hloop φ).src (Sum.inl e) = ⟨F.src e.1, e.2.1⟩ := rfl

@[simp] theorem eliminateSystem_tgt_inl
    [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Away F u) :
    (eliminateSystem (F := F) (u := u) hloop φ).tgt (Sum.inl e) = ⟨F.tgt e.1, e.2.2⟩ := rfl

@[simp] theorem eliminateSystem_src_inr
    [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Incoming F u) :
    (eliminateSystem (F := F) (u := u) hloop φ).src (Sum.inr e) =
      ⟨F.src e.1, by
        intro hs
        apply hloop e.1
        exact hs.trans e.2.symm⟩ := rfl

@[simp] theorem eliminateSystem_tgt_inr
    [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Incoming F u) :
    (eliminateSystem (F := F) (u := u) hloop φ).tgt (Sum.inr e) =
      ⟨F.tgt (φ e).1, by
        intro h
        have hs := (φ e).2
        exact hloop (φ e).1 (hs.trans h.symm)⟩ := rfl

/-- The map carried by a virtual edge is the composite along its defining
two-edge path. -/
theorem eliminateSystem_virtual_map
    [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (e : Incoming F u)
    (x : F.Fiber (F.src e.1)) :
    (eliminateSystem (F := F) (u := u) hloop φ).fiberMap (Sum.inr e) x =
      F.fiberMap (φ e).1 ((φ e).2.symm ▸ (e.2 ▸ F.fiberMap e.1 x)) := by
  simp [eliminateSystem]

/-- The smaller system indexed by an injection of incoming edges into
outgoing edges. Keeping the injection as part of the index avoids choosing
enumerations of the finite edge types. -/
noncomputable def eliminateSystemInj
    [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u ↪ Outgoing F u) :
    FiniteFiberSystem {v : V // v ≠ u}
      (Away F u ⊕ Incoming F u) :=
  eliminateSystem (F := F) (u := u) hloop φ

@[simp] theorem eliminateSystemInj_virtual_map
    [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u ↪ Outgoing F u) (e : Incoming F u)
    (x : F.Fiber (F.src e.1)) :
    (eliminateSystemInj (F := F) (u := u) hloop φ).fiberMap (Sum.inr e) x =
      F.fiberMap (φ e).1 ((φ e).2.symm ▸ (e.2 ▸ F.fiberMap e.1 x)) := by
  simpa [eliminateSystemInj] using
    (eliminateSystem_virtual_map (F := F) (u := u) hloop φ e x)

/-- At a surviving vertex, the source-edge labels of an elimination child
are in bijection with the original outgoing edges: incoming edges become
virtual edges, and edges away from the eliminated vertex remain unchanged. -/
theorem eliminateSystem_outdegree [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) (v : V) (hv : v ≠ u) :
    (eliminateSystem (F := F) (u := u) hloop φ).outdegree ⟨v, hv⟩ =
      F.outdegree v := by
  classical
  let G := eliminateSystem (F := F) (u := u) hloop φ
  let ChildOut : Type _ := {a : Away F u ⊕ Incoming F u // G.src a = ⟨v, hv⟩}
  let BaseOut : Type _ := {e : E // F.src e = v}
  let toBase : ChildOut → BaseOut := fun
    | ⟨Sum.inl e, hsrc⟩ => ⟨e.1, by
        have hval := congrArg Subtype.val hsrc
        simpa only [G, eliminateSystem_src_inl] using hval⟩
    | ⟨Sum.inr e, hsrc⟩ => ⟨e.1, by
        have hval := congrArg Subtype.val hsrc
        simpa only [G, eliminateSystem_src_inr] using hval⟩
  let fromBase : BaseOut → ChildOut := fun e => by
    by_cases ht : F.tgt e.1 = u
    · exact ⟨Sum.inr ⟨e.1, ht⟩, by
        apply Subtype.ext
        exact e.2⟩
    · have hs : F.src e.1 ≠ u := by
        intro hsrc
        apply hv
        exact e.2.symm.trans hsrc
      exact ⟨Sum.inl ⟨e.1, hs, ht⟩, by
        apply Subtype.ext
        exact e.2⟩
  let equiv : ChildOut ≃ BaseOut := {
    toFun := toBase
    invFun := fromBase
    left_inv := by
      intro a
      rcases a with ⟨a, ha⟩
      cases a with
      | inl e =>
          simp [toBase, fromBase, G, e.2.2]
      | inr e =>
          simp [toBase, fromBase, G, e.2]
    right_inv := by
      intro e
      by_cases ht : F.tgt e.1 = u
      · apply Subtype.ext
        simp [toBase, fromBase, G, ht]
      · apply Subtype.ext
        simp [toBase, fromBase, G, ht]
  }
  exact Nat.card_congr equiv

/-- Vertex elimination preserves balance at every surviving vertex. -/
theorem Balanced.eliminateSystem_balanced [DecidableEq V] [DecidableEq E]
    (hF : F.Balanced)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) :
    (eliminateSystem (F := F) (u := u) hloop φ).Balanced := by
  intro v
  have hout := eliminateSystem_outdegree (F := F) (u := u) hloop φ v.1 v.2
  change (eliminateSystem (F := F) (u := u) hloop φ).outdegree v =
    F.fiberDimension v.1
  exact hout.trans (hF v.1)

/-- Deleting a vertex removes exactly its fiber's quotient dimension. -/
theorem eliminateSystem_totalDimension
    [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) :
    (eliminateSystem (F := F) (u := u) hloop φ).totalDimension +
      F.fiberDimension u = F.totalDimension := by
  classical
  let G := eliminateSystem (F := F) (u := u) hloop φ
  let e : {v : V // v ≠ u} ≃ {v // v ∈ Finset.univ.erase u} := {
    toFun := fun v => ⟨v.1, Finset.mem_erase.mpr ⟨v.2, Finset.mem_univ _⟩⟩
    invFun := fun v => ⟨v.1, (Finset.mem_erase.mp v.2).1⟩
    left_inv := by intro v; cases v; rfl
    right_inv := by intro v; cases v; rfl
  }
  have hsum : (∑ v : {v : V // v ≠ u}, F.fiberDimension v.1) =
      ∑ v ∈ Finset.univ.erase u, F.fiberDimension v := by
    calc
      (∑ v : {v : V // v ≠ u}, F.fiberDimension v.1) =
          ∑ v : {v // v ∈ Finset.univ.erase u}, F.fiberDimension v.1 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = ∑ v ∈ Finset.univ.erase u, F.fiberDimension v := by
        simp only [Finset.univ_eq_attach, Finset.sum_attach]
  rw [G.totalDimension_eq_sum_fiberDimension, F.totalDimension_eq_sum_fiberDimension]
  change (∑ v : {v : V // v ≠ u}, F.fiberDimension v.1) + F.fiberDimension u =
    ∑ v : V, F.fiberDimension v
  rw [hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ u)]

/-- In a balanced system, vertex elimination decreases the induction
measure by the outdegree of the eliminated vertex. -/
theorem Balanced.eliminateSystem_totalDimension
    (hF : F.Balanced) [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : Incoming F u → Outgoing F u) :
    (eliminateSystem (F := F) (u := u) hloop φ).totalDimension =
      F.totalDimension - F.outdegree u := by
  have h := Positivity.FiniteFiberSystem.eliminateSystem_totalDimension
    (F := F) (u := u) hloop φ
  rw [← hF u] at h
  omega

/-! The auxiliary vertex-deleted system used for the Schur identity has
one virtual edge for every incoming/outgoing pair.  Both edge labels are
retained so parallel paths stay distinct. -/
noncomputable def eliminateSystemAllCompositions
    {V E : Type*} [Fintype V] [Fintype E]
    (F : FiniteFiberSystem V E) (u : V)
    [DecidableEq V] [DecidableEq E]
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) :
    FiniteFiberSystem {v : V // v ≠ u}
      (F.Away u ⊕ (F.Incoming u × F.Outgoing u)) := by
  classical
  letI : Fintype (F.Incoming u) := inferInstance
  letI : Fintype (F.Outgoing u) := inferInstance
  letI : Fintype (F.Away u) := inferInstance
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
        have hsrc : F.src e.1.1 ≠ u := by
          intro hs
          exact hloop e.1.1 (hs.trans e.1.2.symm)
        exact ⟨F.src e.1.1, hsrc⟩
  · cases e with
    | inl e => exact ⟨F.tgt e.1, e.2.2⟩
    | inr e => exact ⟨F.tgt e.2.1, by
        intro h
        exact hloop e.2.1 (e.2.2.trans h.symm)
      ⟩
  · intro x
    cases e with
    | inl e => exact F.fiberMap e.1 x
    | inr e =>
        exact F.fiberMap e.2.1
          (e.2.2.symm ▸ (e.1.2 ▸ F.fiberMap e.1.1 x))

end FiniteFiberSystem

end Positivity
