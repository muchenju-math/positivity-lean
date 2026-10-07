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
def quotientBlock₁₁
    {V E α β : Type*} [Fintype V] [Fintype E]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : FiniteFiberSystem V E) (e : F.Coord ≃ α ⊕ β) :
    Matrix α α (MvPolynomial E ℤ) :=
  fun i j => F.quotientLaplacian (e.symm (Sum.inl i)) (e.symm (Sum.inl j))

def quotientBlock₁₂
    {V E α β : Type*} [Fintype V] [Fintype E]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : FiniteFiberSystem V E) (e : F.Coord ≃ α ⊕ β) :
    Matrix α β (MvPolynomial E ℤ) :=
  fun i j => F.quotientLaplacian (e.symm (Sum.inl i)) (e.symm (Sum.inr j))

def quotientBlock₂₁
    {V E α β : Type*} [Fintype V] [Fintype E]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : FiniteFiberSystem V E) (e : F.Coord ≃ α ⊕ β) :
    Matrix β α (MvPolynomial E ℤ) :=
  fun i j => F.quotientLaplacian (e.symm (Sum.inr i)) (e.symm (Sum.inl j))

def quotientBlock₂₂
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

private theorem sum_filter_le_univ (p : V → Prop) [DecidablePred p]
    (f : V → ℕ) :
    (∑ v in Finset.univ.filter p, f v) ≤ ∑ v, f v := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ) p]
  exact Nat.le_add_right _ _

private theorem sum_filter_eq_univ_of_zero_off
    (p : V → Prop) [DecidablePred p] (f : V → ℕ)
    (hoff : ∀ v, ¬ p v → f v = 0) :
    (∑ v in Finset.univ.filter p, f v) = ∑ v, f v := by
  classical
  have hzero : (∑ v in Finset.univ.filter (fun v => ¬ p v), f v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact hoff v (Finset.mem_filter.mp hv).2
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ) p, hzero, add_zero]

/-- Summing the outdegrees counts every edge exactly once. -/
theorem sum_outdegree_eq_card :
    (∑ v : V, F.outdegree v) = Fintype.card E := by
  classical
  let SrcFiber : V → Type := fun v => {e : E // F.src e = v}
  let edgeEquiv : (Σ v : V, SrcFiber v) ≃ E where
    toFun x := x.2.1
    invFun e := ⟨F.src e, ⟨e, rfl⟩⟩
    left_inv := by
      intro x
      rcases x with ⟨v, ⟨e, h⟩⟩
      simp [SrcFiber, h]
    right_inv := by
      intro e
      rfl
  calc
    (∑ v : V, F.outdegree v) =
        ∑ v : V, Fintype.card (SrcFiber v) := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [FiniteFiberSystem.outdegree, SrcFiber]
    _ = Fintype.card (Σ v : V, SrcFiber v) := by simp
    _ = Fintype.card E := Fintype.card_congr edgeEquiv

/-- Summing the indegrees also counts every edge exactly once. -/
theorem sum_indegree_eq_card :
    (∑ v : V, F.indegree v) = Fintype.card E := by
  classical
  let TgtFiber : V → Type := fun v => {e : E // F.tgt e = v}
  let edgeEquiv : (Σ v : V, TgtFiber v) ≃ E where
    toFun x := x.2.1
    invFun e := ⟨F.tgt e, ⟨e, rfl⟩⟩
    left_inv := by
      intro x
      rcases x with ⟨v, ⟨e, h⟩⟩
      simp [TgtFiber, h]
    right_inv := by
      intro e
      rfl
  calc
    (∑ v : V, F.indegree v) =
        ∑ v : V, Fintype.card (TgtFiber v) := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [FiniteFiberSystem.indegree, TgtFiber]
    _ = Fintype.card (Σ v : V, TgtFiber v) := by simp
    _ = Fintype.card E := Fintype.card_congr edgeEquiv

/-- A finite-sum selection principle: if the sum of `f` on `S` is at most
the sum of a strictly positive `g`, then some point has `f ≤ g`. -/
theorem exists_mem_le_of_sum_le_sum
    (S : Finset V) (f g : V → ℕ)
    (hS : S.Nonempty) (hg : ∀ v ∈ S, 0 < g v)
    (hsum : (∑ v in S, f v) ≤ ∑ v in S, g v) :
    ∃ v ∈ S, f v ≤ g v := by
  classical
  by_contra h
  push_neg at h
  have hstrict : ∑ v in S, g v < ∑ v in S, f v := by
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
    (hbound : (∑ v in S, F.indegree v) ≤ ∑ v in S, F.outdegree v) :
    ∃ v ∈ S, F.indegree v ≤ F.outdegree v :=
  exists_mem_le_of_sum_le_sum F S F.indegree F.outdegree hS hpositive hbound

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
    have he : e ∈ Finset.univ.filter (fun e : E => F.src e = F.src e) := by simp
    exact Finset.card_pos.mpr ⟨e, he⟩
  have hpos : ∀ v ∈ positive, 0 < F.outdegree v := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hinBound :
      (∑ v in positive, F.indegree v) ≤ ∑ v : V, F.indegree v := by
    exact sum_filter_le_univ (fun v => 0 < F.outdegree v) F.indegree
  have houtEq : (∑ v in positive, F.outdegree v) = ∑ v : V, F.outdegree v := by
    apply sum_filter_eq_univ_of_zero_off
    intro v hv
    have hnot : ¬ 0 < F.outdegree v := hv
    omega
  have hsum :
      (∑ v in positive, F.indegree v) ≤ ∑ v in positive, F.outdegree v := by
    rw [houtEq]
    calc
      (∑ v in positive, F.indegree v) ≤ ∑ v : V, F.indegree v := hinBound
      _ = Fintype.card E := F.sum_indegree_eq_card
      _ = ∑ v : V, F.outdegree v := F.sum_outdegree_eq_card.symm
  obtain ⟨u, hu, hle⟩ :=
    exists_positiveOutdegree_with_indegree_le F positive hnonempty hpos hsum
  exact ⟨u, hpos u hu, hle⟩

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

