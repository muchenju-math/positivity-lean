import Mathlib

/-!
# Finite-fiber systems and polarization

Formalization of the shared algebraic setup from Section 2 of
*Coefficient positivity for arborescences of covering digraphs*.
The base graph is given by finite vertex and edge types with source and
target maps, so parallel edges and loops are represented without any
special cases.  The chosen reference points provide explicit coordinates
on the quotient by fiber-constant functions.
-/

namespace Positivity

universe uCast

private theorem cast_eq_iff_reverse
    {α β : Type uCast} (h : α = β) (x : β) (y : α) :
    x = h ▸ y ↔ h.symm ▸ x = y := by
  constructor
  · intro hxy
    have hheq : y ≍ x := by
      rw [eq_comm, eqRec_eq_cast, cast_eq_iff_heq] at hxy
      exact hxy
    have hcast : cast h.symm x = y := cast_eq_iff_heq.mpr hheq.symm
    simpa only [eqRec_eq_cast] using hcast
  · intro hyx
    have hheq : x ≍ y := by
      rw [eqRec_eq_cast, cast_eq_iff_heq] at hyx
      exact hyx
    have hcast : cast h y = x := cast_eq_iff_heq.mpr hheq.symm
    simpa only [eqRec_eq_cast] using hcast.symm

private theorem depCast_eq_iff_reverse
    {α : Sort*} {P : α → Sort*} {a b : α} (h : a = b)
    (x : P b) (y : P a) : x = h ▸ y ↔ h.symm ▸ x = y := by
  cases h
  exact Iff.rfl

private theorem sum_delta_mul_composed_delta
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (a : α) (f : α → β) (b : β) :
    (∑ x : α, (if x = a then (1 : ℤ) else 0) *
      (if f x = b then 1 else 0)) = if f a = b then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro x hx hxa
    simp [hxa]
  · simp

private theorem sum_delta_mul_delta
    {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) :
    (∑ x : α, (if x = a then (1 : ℤ) else 0) *
      (if x = b then 1 else 0)) = if a = b then 1 else 0 := by
  simpa using sum_delta_mul_composed_delta a (fun x : α => x) b

/-- A finite directed multigraph together with a finite nonempty fiber at
each vertex and a map of fibers above each directed edge.  Distinct elements
of `E` remain distinct edges even when they have the same endpoints. -/
structure FiniteFiberSystem (V E : Type*) [Fintype V] [Fintype E] where
  src : E → V
  tgt : E → V
  Fiber : V → Type*
  fiberFintype : ∀ v, Fintype (Fiber v)
  reference : ∀ v, Fiber v
  fiberMap : ∀ e, Fiber (src e) → Fiber (tgt e)

namespace FiniteFiberSystem

variable {V E : Type*} [Fintype V] [Fintype E] (F : FiniteFiberSystem V E)

/-- The quotient coordinates in the fiber over `v`. -/
abbrev CoordAt (v : V) := {p : F.Fiber v // p ≠ F.reference v}

noncomputable instance coordAtFintype (v : V) : Fintype (F.CoordAt v) := by
  classical
  letI := F.fiberFintype v
  infer_instance

noncomputable instance coordAtDecidableEq (v : V) : DecidableEq (F.CoordAt v) := by
  classical infer_instance

/-- The total set of reference-point quotient coordinates. -/
abbrev Coord := Σ v : V, F.CoordAt v

noncomputable instance coordFintype : Fintype F.Coord := by
  classical
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  infer_instance

noncomputable instance coordDecidableEq : DecidableEq F.Coord := by
  classical infer_instance

/-- The integer matrix of the pullback induced by an edge map, after
normalizing functions to vanish at the reference point. -/
noncomputable def pullback (e : E) : Matrix (F.CoordAt (F.src e)) (F.CoordAt (F.tgt e)) ℤ := by
  classical
  exact fun p q =>
    (if F.fiberMap e p.1 = q.1 then 1 else 0) -
    (if F.fiberMap e (F.reference (F.src e)) = q.1 then 1 else 0)

/-- The cardinality of the fiber over a base vertex. -/
def fiberSize (v : V) : ℕ := @Fintype.card (F.Fiber v) (F.fiberFintype v)

/-- The number of quotient coordinates contributed by a fiber. -/
def fiberDimension (v : V) : ℕ := F.fiberSize v - 1

/-- Outdegree, counting parallel edges separately and counting a loop once. -/
noncomputable def outdegree (v : V) : ℕ := by
  classical
  exact Nat.card {e : E // F.src e = v}

/-- Total dimension of the quotient coordinate space. -/
noncomputable def totalDimension : ℕ := Fintype.card F.Coord

/-- A system is balanced when the base outdegree equals the quotient
dimension of every fiber. -/
def Balanced : Prop := ∀ v, F.outdegree v = F.fiberDimension v

/-- The integer coefficient contributed by a single edge to a quotient
Laplacian entry. -/
noncomputable def quotientEdgeCoefficient (e : E) (i j : F.Coord) : ℤ := by
  classical
  exact (if i = j then if F.src e = i.1 then 1 else 0 else 0) -
    (if hsrc : i.1 = F.src e then
      if htgt : j.1 = F.tgt e then
        (if F.fiberMap e (hsrc ▸ i.2.1) = htgt ▸ j.2.1 then 1 else 0) -
          (if F.fiberMap e (F.reference (F.src e)) = htgt ▸ j.2.1 then 1 else 0)
      else 0
    else 0)

/-- Express the target of a lifted loop edge in the source fiber. -/
def loopTargetInSource (e : E) (he : F.src e = F.tgt e)
    (p : F.Fiber (F.src e)) : F.Fiber (F.src e) :=
  he.symm ▸ F.fiberMap e p

/-- An edge contributes to a quotient-Laplacian row only when it leaves
the vertex indexing that row. -/
theorem quotientEdgeCoefficient_eq_zero_of_src_ne
    (e : E) (i j : F.Coord) (h : F.src e ≠ i.1) :
    F.quotientEdgeCoefficient e i j = 0 := by
  classical
  simp [quotientEdgeCoefficient, h, Ne.symm h]

/-- A loop edge block is the sum of rank-one contributions from its lifted
edges, after transporting target values back to the source fiber. -/
theorem quotientEdgeCoefficient_loop_rankOne_sum
    (e : E) (he : F.src e = F.tgt e)
    [Fintype (F.Fiber (F.src e))] [DecidableEq (F.Fiber (F.src e))]
    (i j : F.CoordAt (F.src e)) :
    F.quotientEdgeCoefficient e ⟨F.src e, i⟩ ⟨F.src e, j⟩ =
      ∑ p : F.Fiber (F.src e),
        ((if p = i.1 then (1 : ℤ) else 0) -
          (if p = F.reference (F.src e) then 1 else 0)) *
        ((if p = j.1 then (1 : ℤ) else 0) -
          (if F.loopTargetInSource e he p = j.1 then 1 else 0)) := by
  classical
  let loopMap : F.Fiber (F.src e) → F.Fiber (F.src e) :=
    fun p => F.loopTargetInSource e he p
  have hsum :
      (∑ p : F.Fiber (F.src e),
        ((if p = i.1 then (1 : ℤ) else 0) -
          (if p = F.reference (F.src e) then 1 else 0)) *
        ((if p = j.1 then (1 : ℤ) else 0) -
          (if loopMap p = j.1 then 1 else 0))) =
        (if i.1 = j.1 then (1 : ℤ) else 0) -
          ((if loopMap i.1 = j.1 then 1 else 0) -
            (if loopMap (F.reference (F.src e)) = j.1 then 1 else 0)) := by
    calc
      _ = ∑ p : F.Fiber (F.src e),
            ((if p = i.1 then (1 : ℤ) else 0) *
                (if p = j.1 then 1 else 0) -
              (if p = i.1 then (1 : ℤ) else 0) *
                (if loopMap p = j.1 then 1 else 0) -
              (if p = F.reference (F.src e) then (1 : ℤ) else 0) *
                (if p = j.1 then 1 else 0) +
              (if p = F.reference (F.src e) then (1 : ℤ) else 0) *
                (if loopMap p = j.1 then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib]
        rw [sum_delta_mul_delta, sum_delta_mul_composed_delta,
          sum_delta_mul_delta, sum_delta_mul_composed_delta]
        simp [Ne.symm j.2]
        ring
  have hmapI :
      (F.fiberMap e i.1 = he ▸ j.1) ↔ loopMap i.1 = j.1 := by
    exact depCast_eq_iff_reverse (P := F.Fiber) he
      (F.fiberMap e i.1) j.1
  have hmapRef :
    (F.fiberMap e (F.reference (F.src e)) = he ▸ j.1) ↔
        loopMap (F.reference (F.src e)) = j.1 := by
    exact depCast_eq_iff_reverse (P := F.Fiber) he
      (F.fiberMap e (F.reference (F.src e))) j.1
  calc
    F.quotientEdgeCoefficient e ⟨F.src e, i⟩ ⟨F.src e, j⟩ =
        (if i.1 = j.1 then (1 : ℤ) else 0) -
          ((if loopMap i.1 = j.1 then 1 else 0) -
            (if loopMap (F.reference (F.src e)) = j.1 then 1 else 0)) := by
          simp [quotientEdgeCoefficient, loopMap, he, Subtype.ext_iff,
            hmapI, hmapRef]
    _ = (∑ p : F.Fiber (F.src e),
          ((if p = i.1 then (1 : ℤ) else 0) -
            (if p = F.reference (F.src e) then 1 else 0)) *
          ((if p = j.1 then (1 : ℤ) else 0) -
            (if F.loopTargetInSource e he p = j.1 then 1 else 0))) := hsum.symm

/-- The block-entry quotient Laplacian, written as a sum of individual
edge contributions. -/
noncomputable def quotientLaplacian : Matrix F.Coord F.Coord (MvPolynomial E ℤ) := by
  classical
  exact fun i j =>
    ∑ e : E, MvPolynomial.X e * MvPolynomial.C (F.quotientEdgeCoefficient e i j)

/-- Restrict the row formula to edges with the correct source. -/
theorem quotientLaplacian_eq_sum_source_edges [DecidableEq V]
    (i j : F.Coord) :
    F.quotientLaplacian i j =
      ∑ e ∈ Finset.univ.filter (fun e : E => F.src e = i.1),
        MvPolynomial.X e * MvPolynomial.C (F.quotientEdgeCoefficient e i j) := by
  classical
  rw [quotientLaplacian]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hnot
  have hsrc : F.src e ≠ i.1 := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  rw [F.quotientEdgeCoefficient_eq_zero_of_src_ne e i j hsrc]
  simp

/-- The determinant polynomial of the induced quotient Laplacian. -/
noncomputable def quotientDeterminant : MvPolynomial E ℤ := Matrix.det F.quotientLaplacian

/-- The total exponent of a monomial on edges sourced at a fixed vertex. -/
noncomputable def sourceExponentDegree [DecidableEq V]
    (v : V) (d : E →₀ ℕ) : ℕ :=
  ∑ e ∈ Finset.univ.filter (fun e : E => F.src e = v), d e

@[simp] theorem sourceExponentDegree_single [DecidableEq V]
    (v : V) (e : E) :
    F.sourceExponentDegree v (Finsupp.single e 1) =
      if F.src e = v then 1 else 0 := by
  classical
  simp [sourceExponentDegree, Finsupp.single_apply]

theorem sourceExponentDegree_add [DecidableEq V]
    (v : V) (d₁ d₂ : E →₀ ℕ) :
    F.sourceExponentDegree v (d₁ + d₂) =
      F.sourceExponentDegree v d₁ + F.sourceExponentDegree v d₂ := by
  classical
  simp [sourceExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib]

/-- Source degree is preserved additively by polynomial multiplication. -/
theorem sourceExponentDegree_eq_of_mem_mul_support [DecidableEq V]
    (v : V) (P Q : MvPolynomial E ℤ) (a b : ℕ)
    (hP : ∀ d ∈ P.support, F.sourceExponentDegree v d = a)
    (hQ : ∀ d ∈ Q.support, F.sourceExponentDegree v d = b)
    {d : E →₀ ℕ} (hd : d ∈ (P * Q).support) :
    F.sourceExponentDegree v d = a + b := by
  classical
  have hmem := MvPolynomial.support_mul P Q hd
  rcases Finset.mem_add.mp hmem with ⟨d₁, hd₁, d₂, hd₂, rfl⟩
  rw [F.sourceExponentDegree_add, hP d₁ hd₁, hQ d₂ hd₂]

/-- A finite sum cannot introduce a source degree absent from every summand. -/
theorem sourceExponentDegree_eq_of_mem_sum_support [DecidableEq V]
    {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial E ℤ)
    (v : V) (k : ℕ)
    (hP : ∀ i ∈ s, ∀ d ∈ (P i).support,
      F.sourceExponentDegree v d = k)
    {d : E →₀ ℕ} (hd : d ∈ (∑ i ∈ s, P i).support) :
    F.sourceExponentDegree v d = k := by
  classical
  have hmem := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  obtain ⟨i, hi, hdi⟩ := hmem
  exact hP i hi d hdi

/-- The source degree of a supported product is the sum of the source
degrees of its factors. -/
theorem sourceExponentDegree_eq_of_mem_prod_support [DecidableEq V]
    {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial E ℤ)
    (v : V) (k : ι → ℕ)
    (hP : ∀ i ∈ s, ∀ d ∈ (P i).support,
      F.sourceExponentDegree v d = k i)
    {d : E →₀ ℕ} (hd : d ∈ (∏ i ∈ s, P i).support) :
    F.sourceExponentDegree v d = ∑ i ∈ s, k i := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty =>
      simpa [sourceExponentDegree] using
        (show F.sourceExponentDegree v d = 0 from by
          have : d = 0 := by simpa using hd
          subst d
          simp [sourceExponentDegree])
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha] at hd
      have hmul := F.sourceExponentDegree_eq_of_mem_mul_support
        v (P a) (∏ i ∈ s, P i) (k a) (∑ i ∈ s, k i)
        (fun d hd => hP a (Finset.mem_insert_self a s) d hd)
        (fun d hd => ih
          (fun i hi => hP i (Finset.mem_insert_of_mem hi)) hd) hd
      simpa [sourceExponentDegree, Finset.sum_insert, ha] using hmul

/-- Every monomial in a quotient-Laplacian row has source degree one at the
vertex indexing that row. -/
theorem quotientLaplacian_sourceExponentDegree [DecidableEq V]
    (i j : F.Coord) (v : V) {d : E →₀ ℕ}
    (hd : d ∈ (F.quotientLaplacian i j).support) :
    F.sourceExponentDegree v d = if i.1 = v then 1 else 0 := by
  classical
  rw [F.quotientLaplacian_eq_sum_source_edges i j] at hd
  apply F.sourceExponentDegree_eq_of_mem_sum_support
    (s := Finset.univ.filter (fun e : E => F.src e = i.1))
    (P := fun e => MvPolynomial.X e *
      MvPolynomial.C (F.quotientEdgeCoefficient e i j)) v
      (if i.1 = v then 1 else 0)
  · intro e he d hd
    have hsrc := (Finset.mem_filter.mp he).2
    have hX : ∀ d ∈ (MvPolynomial.X e : MvPolynomial E ℤ).support,
        F.sourceExponentDegree v d = if i.1 = v then 1 else 0 := by
      intro d hd
      rw [MvPolynomial.support_X] at hd
      have : d = Finsupp.single e 1 := Finset.mem_singleton.mp hd
      subst d
      simpa [sourceExponentDegree_single, hsrc]
    have hC : ∀ d ∈ (MvPolynomial.C (F.quotientEdgeCoefficient e i j) :
        MvPolynomial E ℤ).support, F.sourceExponentDegree v d = 0 := by
      intro d hd
      rw [MvPolynomial.support_C] at hd
      have : d = 0 := by
        by_cases hc : F.quotientEdgeCoefficient e i j = 0
        · have hfalse : False := by
            simpa [hc] using hd
          exact hfalse.elim
        · simpa [hc] using hd
      subst d
      simp [sourceExponentDegree]
    exact F.sourceExponentDegree_eq_of_mem_mul_support
      v (MvPolynomial.X e) (MvPolynomial.C (F.quotientEdgeCoefficient e i j))
      (if i.1 = v then 1 else 0) 0 hX hC hd
  · exact hd

/-- The number of quotient coordinates contributed by a fiber is one less
than its cardinality. -/
theorem card_coordAt (v : V) : Fintype.card (F.CoordAt v) = F.fiberDimension v := by
  classical
  letI := F.fiberFintype v
  have h := Fintype.card_subtype_compl (fun p : F.Fiber v => p = F.reference v)
  simpa [CoordAt, fiberDimension, fiberSize] using h

theorem sourceCoordinateCount [DecidableEq V] (v : V) :
    (∑ i : F.Coord, if i.1 = v then 1 else 0) = F.fiberDimension v := by
  classical
  rw [Fintype.sum_sigma]
  have hinner (w : V) :
      (∑ q : F.CoordAt w, if w = v then 1 else 0) =
        if w = v then Fintype.card (F.CoordAt w) else 0 := by
    by_cases h : w = v <;> simp [h]
  simp_rw [hinner]
  simp [Finset.sum_ite_eq', card_coordAt]

/-- The Leibniz expansion of the quotient determinant has the prescribed
source degree at every vertex. -/
theorem quotientDeterminant_sourceExponentDegree [DecidableEq V]
    (v : V) {d : E →₀ ℕ}
    (hd : d ∈ F.quotientDeterminant.support) :
    F.sourceExponentDegree v d = F.fiberDimension v := by
  classical
  change d ∈ (Matrix.det F.quotientLaplacian).support at hd
  rw [Matrix.det_apply] at hd
  apply F.sourceExponentDegree_eq_of_mem_sum_support
    (s := Finset.univ)
    (P := fun σ : Equiv.Perm F.Coord =>
      Equiv.Perm.sign σ • ∏ i : F.Coord, F.quotientLaplacian (σ i) i)
    v (F.fiberDimension v)
  · intro σ _ d hd
    have hdprod : d ∈ (∏ i : F.Coord, F.quotientLaplacian (σ i) i).support :=
      MvPolynomial.support_smul hd
    have hprod := F.sourceExponentDegree_eq_of_mem_prod_support
      (s := Finset.univ)
      (P := fun i : F.Coord => F.quotientLaplacian (σ i) i)
      v (fun i : F.Coord => if (σ i).1 = v then 1 else 0)
      (by
        intro i _ d' hd'
        exact F.quotientLaplacian_sourceExponentDegree (σ i) i v hd') hdprod
    have hcount :
        (∑ i : F.Coord, if (σ i).1 = v then 1 else 0) =
          ∑ i : F.Coord, if i.1 = v then 1 else 0 := by
      exact Fintype.sum_equiv σ _ _ (fun _ => by simp)
    rw [hcount, F.sourceCoordinateCount] at hprod
    exact hprod
  · exact hd

/-- The total quotient dimension is the sum of the fiber dimensions. -/
theorem totalDimension_eq_sum_fiberDimension :
    F.totalDimension = ∑ v : V, F.fiberDimension v := by
  classical
  simp [totalDimension, Fintype.card_sigma, card_coordAt]

end FiniteFiberSystem

namespace FiniteFiberSystem

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The labelled copies of edges used to polarize an exponent vector.
An edge `e` with exponent `α e` is replaced by `α e` distinct edges.
When `α e = 0`, it contributes no copy. -/
abbrev PolarizedEdge (α : E → ℕ) := Σ e : E, Fin (α e)

/-- Polarize a finite-fiber system by replacing each base edge with a
labelled number of parallel copies, retaining its fiber map on every copy.
The fibers and reference points are unchanged. -/
noncomputable def polarize (F : FiniteFiberSystem V E) (α : E → ℕ) :
    FiniteFiberSystem V (PolarizedEdge α) := by
  classical
  exact {
    src := fun e => F.src e.1
    tgt := fun e => F.tgt e.1
    Fiber := F.Fiber
    fiberFintype := F.fiberFintype
    reference := F.reference
    fiberMap := fun e => F.fiberMap e.1
  }

@[simp] theorem polarize_src (F : FiniteFiberSystem V E) (α : E → ℕ)
    (e : PolarizedEdge α) : (F.polarize α).src e = F.src e.1 := rfl

@[simp] theorem polarize_tgt (F : FiniteFiberSystem V E) (α : E → ℕ)
    (e : PolarizedEdge α) : (F.polarize α).tgt e = F.tgt e.1 := rfl

@[simp] theorem polarize_fiberMap (F : FiniteFiberSystem V E) (α : E → ℕ)
    (e : PolarizedEdge α) (p : F.Fiber (F.src e.1)) :
    (F.polarize α).fiberMap e p = F.fiberMap e.1 p := rfl

/-- Polarization replaces each outgoing edge by the prescribed number of
labelled copies in the outdegree count. -/
theorem polarize_outdegree [DecidableEq V]
    (F : FiniteFiberSystem V E) (α : E → ℕ) (v : V) :
    (F.polarize α).outdegree v =
      ∑ e ∈ Finset.univ.filter (fun e : E => F.src e = v), α e := by
  classical
  let equiv : {a : PolarizedEdge α // (F.polarize α).src a = v} ≃
      Σ e : {e : E // F.src e = v}, Fin (α e.1) := {
    toFun := fun a => ⟨⟨a.1.1, by simpa using a.2⟩, a.1.2⟩
    invFun := fun a => ⟨⟨a.1.1, a.2⟩, by simpa using a.1.2⟩
    left_inv := by intro a; cases a with | mk a h => cases a with | mk e t => rfl
    right_inv := by intro a; cases a with | mk a t => cases a with | mk e h => rfl
  }
  calc
    (F.polarize α).outdegree v =
        Nat.card {a : PolarizedEdge α // (F.polarize α).src a = v} := rfl
    _ = Nat.card (Σ e : {e : E // F.src e = v}, Fin (α e.1)) :=
      Nat.card_congr equiv
    _ = ∑ e : {e : E // F.src e = v}, α e.1 := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_fin]
    _ = ∑ e ∈ Finset.univ.filter (fun e : E => F.src e = v), α e := by
      let edgeEquiv : {e : E // F.src e = v} ≃
          {e : E // e ∈ Finset.univ.filter (fun e : E => F.src e = v)} := {
        toFun := fun e => ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩⟩
        invFun := fun e => ⟨e.1, (Finset.mem_filter.mp e.2).2⟩
        left_inv := by intro e; cases e; rfl
        right_inv := by intro e; cases e; rfl
      }
      calc
        (∑ e : {e : E // F.src e = v}, α e.1) =
            ∑ e : {e : E // e ∈ Finset.univ.filter (fun e : E => F.src e = v)}, α e.1 :=
          Fintype.sum_equiv edgeEquiv _ _ (fun _ => rfl)
        _ = ∑ e ∈ Finset.univ.filter (fun e : E => F.src e = v), α e := by
          simp only [Finset.univ_eq_attach, Finset.sum_attach]

/-- If the multiplicities of the outgoing copies sum to the original
outdegree at every vertex, polarization preserves balance. -/
theorem Balanced.polarize [DecidableEq V]
    (F : FiniteFiberSystem V E) (hF : F.Balanced) (α : E → ℕ)
    (hα : ∀ v, ∑ e ∈ Finset.univ.filter (fun e : E => F.src e = v), α e =
      F.outdegree v) :
    (F.polarize α).Balanced := by
  intro v
  rw [polarize_outdegree, hα, hF]
  rfl

/-- The sum of the new edge variables that replaces the old variable of
edge `e` under the polarization substitution. -/
noncomputable def polarizedVariableSum (α : E → ℕ) (e : E) :
    MvPolynomial (PolarizedEdge α) ℤ :=
  ∑ t : Fin (α e), MvPolynomial.X ⟨e, t⟩

/-- The polynomial substitution that sends each old edge variable to the
sum of the variables on its labelled polarized copies. -/
noncomputable def polarizationHom (α : E → ℕ) :
    MvPolynomial E ℤ →+* MvPolynomial (PolarizedEdge α) ℤ :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ℤ →+* MvPolynomial (PolarizedEdge α) ℤ)
    (polarizedVariableSum α)

@[simp] theorem polarizationHom_X (α : E → ℕ) (e : E) :
    polarizationHom α (MvPolynomial.X e) = polarizedVariableSum α e := by
  simp [polarizationHom]

@[simp] theorem polarizationHom_C (α : E → ℕ) (z : ℤ) :
    polarizationHom α (MvPolynomial.C z) = MvPolynomial.C z := by
  simp [polarizationHom]

/-- Polarization sends a source monomial to the product of the powers
of the corresponding edge-copy sums. -/
theorem polarizationHom_monomial (α : E → ℕ) (d : E →₀ ℕ) (c : ℤ) :
    polarizationHom α (MvPolynomial.monomial d c) =
      MvPolynomial.C c * ∏ e : E, polarizedVariableSum α e ^ d e := by
  classical
  rw [polarizationHom, MvPolynomial.eval₂Hom_monomial]
  rw [d.prod_fintype (fun e n => polarizedVariableSum α e ^ n) (by simp)]
/-- Expanding a polynomial into monomials before polarization gives an
explicit finite sum of products of edge-copy power sums. -/
theorem polarizationHom_as_sum (α : E → ℕ) (P : MvPolynomial E ℤ) :
    polarizationHom α P =
      ∑ d ∈ P.support,
        MvPolynomial.C (P.coeff d) * ∏ e : E, polarizedVariableSum α e ^ d e := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  simp only [map_sum, polarizationHom_monomial]
/-- Coefficient extraction after polarization reduces to a finite sum
over the source support.  The remaining factor coefficient is the
groupwise combinatorial calculation. -/
theorem coeff_polarizationHom (α : E → ℕ) (P : MvPolynomial E ℤ)
    (s : PolarizedEdge α →₀ ℕ) :
    (polarizationHom α P).coeff s =
      ∑ d ∈ P.support,
        P.coeff d * (∏ e : E, polarizedVariableSum α e ^ d e).coeff s := by
  rw [polarizationHom_as_sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul]
/-- Substitution commutes with the determinant of the quotient matrix.  This
is the exact matrix-level polynomial identity underlying polarization; the
remaining coefficient extraction is a separate combinatorial statement. -/
theorem polarizationHom_quotientDeterminant
    (F : FiniteFiberSystem V E) (α : E → ℕ) :
    polarizationHom α (F.quotientDeterminant) =
      ((polarizationHom α).mapMatrix F.quotientLaplacian).det := by
  simpa [FiniteFiberSystem.quotientDeterminant] using
    (RingHom.map_det (polarizationHom α) F.quotientLaplacian)

@[simp] theorem polarize_quotientEdgeCoefficient
    (F : FiniteFiberSystem V E) (α : E → ℕ)
    (a : PolarizedEdge α) (i j : F.Coord) :
    (F.polarize α).quotientEdgeCoefficient a i j =
      F.quotientEdgeCoefficient a.1 i j := by
  rfl

/-- The quotient Laplacian commutes entrywise with the edge-copy
polarization. -/
theorem polarizationHom_quotientLaplacian
    (F : FiniteFiberSystem V E) (α : E → ℕ) (i j : F.Coord) :
    polarizationHom α (F.quotientLaplacian i j) =
      (F.polarize α).quotientLaplacian i j := by
  classical
  simp only [FiniteFiberSystem.quotientLaplacian]
  rw [map_sum]
  simp_rw [map_mul, polarizationHom_X, polarizationHom_C]
  simp_rw [polarize_quotientEdgeCoefficient]
  change (∑ e : E,
      polarizedVariableSum α e * MvPolynomial.C (F.quotientEdgeCoefficient e i j)) =
    ∑ a : Sigma (fun e : E => Fin (α e)),
      (fun e t =>
        MvPolynomial.X (⟨e, t⟩ : PolarizedEdge α) *
          MvPolynomial.C (F.quotientEdgeCoefficient e i j)) a.1 a.2
  rw [Fintype.sum_sigma' (fun e t =>
    MvPolynomial.X (⟨e, t⟩ : PolarizedEdge α) *
      MvPolynomial.C (F.quotientEdgeCoefficient e i j))]
  simp [polarizedVariableSum, Finset.sum_mul]

/-- The determinant after polarization is the determinant of the system with
labelled parallel edge copies. -/
theorem polarizationHom_quotientDeterminant_eq_polarize
    (F : FiniteFiberSystem V E) (α : E → ℕ) :
    polarizationHom α (F.quotientDeterminant) =
      (F.polarize α).quotientDeterminant := by
  rw [polarizationHom_quotientDeterminant]
  have hmatrix :
      (polarizationHom α).mapMatrix F.quotientLaplacian =
        (F.polarize α).quotientLaplacian := by
    funext i j
    exact polarizationHom_quotientLaplacian F α i j
  rw [hmatrix]
  rfl

end FiniteFiberSystem

/-- `sumRingEquiv` sends a monomial to the monomial of its two restricted
exponents. -/
theorem sumRingEquiv_monomial {σ τ R : Type*} [CommSemiring R]
    (d : (σ ⊕ τ) →₀ ℕ) (c : R) :
    MvPolynomial.sumRingEquiv R σ τ (MvPolynomial.monomial d c) =
      MvPolynomial.monomial
        (Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn)
        (MvPolynomial.monomial
          (Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn) c) := by
  classical
  simp [MvPolynomial.sumRingEquiv, MvPolynomial.monomial]

/-- Under the polynomial equivalence for a sum of variable types, the
coefficient at a pair of restricted exponents is the coefficient at their
sum-elimination reconstruction. -/
theorem coeff_sumRingEquiv {σ τ R : Type*} [CommSemiring R]
    (P : MvPolynomial (σ ⊕ τ) R) (d₁ : σ →₀ ℕ) (d₂ : τ →₀ ℕ) :
    ((MvPolynomial.sumRingEquiv R σ τ P).coeff d₁).coeff d₂ =
      P.coeff (d₁.sumElim d₂) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      let l := Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn
      let r := Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn
      have hsplit : (l = d₁ ∧ r = d₂) ↔ d = d₁.sumElim d₂ := by
        constructor
        · rintro ⟨h₁, h₂⟩
          rw [← h₁, ← h₂]
          exact (Finsupp.comapDomain_sumElim_comapDomain d).symm
        · intro h
          constructor
          · have h' := congrArg
              (Finsupp.comapDomain Sum.inl · Sum.inl_injective.injOn) h.symm
            have h'' : d₁ = l := by simpa [l] using h'
            exact h''.symm
          · have h' := congrArg
              (Finsupp.comapDomain Sum.inr · Sum.inr_injective.injOn) h.symm
            have h'' : d₂ = r := by simpa [r] using h'
            exact h''.symm
      rw [sumRingEquiv_monomial]
      by_cases h₁ : l = d₁
      · by_cases h₂ : r = d₂
        · have hd := hsplit.mp ⟨h₁, h₂⟩
          simp [h₁, h₂, hd, MvPolynomial.coeff_monomial]
        · have hn : d ≠ d₁.sumElim d₂ := by
            intro heq
            exact h₂ (hsplit.mpr heq).2
          have h₁' : Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn = d₁ := h₁
          have h₂' : ¬ Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn = d₂ := h₂
          simp [h₁, h₂, h₁', h₂', hn, MvPolynomial.coeff_monomial]
      · have hn : d ≠ d₁.sumElim d₂ := by
          intro heq
          exact h₁ (hsplit.mpr heq).1
        have h₁' : ¬ Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn = d₁ := h₁
        simp [h₁, h₁', hn, MvPolynomial.coeff_monomial]
  | add P Q hP hQ =>
      simp [hP, hQ]

private theorem comapDomain_inr_mapDomain_inl {σ τ : Type*} (d : σ →₀ ℕ) :
    Finsupp.comapDomain (Sum.inr : τ → σ ⊕ τ)
      (Finsupp.mapDomain (Sum.inl : σ → σ ⊕ τ) d) Sum.inr_injective.injOn = 0 := by
  ext x
  simp [Finsupp.comapDomain_apply, Finsupp.mapDomain_apply]

private theorem comapDomain_inl_mapDomain_inr {σ τ : Type*} (d : τ →₀ ℕ) :
    Finsupp.comapDomain (Sum.inl : σ → σ ⊕ τ)
      (Finsupp.mapDomain (Sum.inr : τ → σ ⊕ τ) d) Sum.inl_injective.injOn = 0 := by
  ext x
  simp [Finsupp.comapDomain_apply, Finsupp.mapDomain_apply]

/-- The sum-variable equivalence sends a polynomial in the left group to
the same polynomial with coefficients embedded as constants in the right
group. -/
theorem sumRingEquiv_rename_inl {σ τ R : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) :
    MvPolynomial.sumRingEquiv R σ τ (MvPolynomial.rename Sum.inl P) =
      MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [MvPolynomial.rename_monomial, sumRingEquiv_monomial]
      have hL := Finsupp.comapDomain_mapDomain (Sum.inl : σ → σ ⊕ τ)
        Sum.inl_injective d
      have hR := comapDomain_inr_mapDomain_inl (σ := σ) (τ := τ) d
      rw [hL, hR]
      simp [MvPolynomial.map_monomial]
  | add P Q hP hQ => simp [hP, hQ]

/-- The sum-variable equivalence sends a polynomial in the right group to
a constant polynomial in the left group. -/
theorem sumRingEquiv_rename_inr {σ τ R : Type*} [CommSemiring R]
    (Q : MvPolynomial τ R) :
    MvPolynomial.sumRingEquiv R σ τ (MvPolynomial.rename Sum.inr Q) =
      MvPolynomial.C Q := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [MvPolynomial.rename_monomial, sumRingEquiv_monomial]
      have hL := comapDomain_inl_mapDomain_inr (σ := σ) (τ := τ) d
      have hR := Finsupp.comapDomain_mapDomain (Sum.inr : τ → σ ⊕ τ)
        Sum.inr_injective d
      rw [hL, hR]
      simp [MvPolynomial.C, MvPolynomial.monomial]
  | add P Q hP hQ => simp [hP, hQ]

/-- Coefficients multiply across two disjoint polynomial variable groups.
This is the binary product rule used to combine polarized edge groups. -/
theorem coeff_mul_rename_groups {σ τ R : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (Q : MvPolynomial τ R)
    (d₁ : σ →₀ ℕ) (d₂ : τ →₀ ℕ) :
    (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q).coeff
        (d₁.sumElim d₂) = P.coeff d₁ * Q.coeff d₂ := by
  classical
  rw [← coeff_sumRingEquiv]
  rw [map_mul, sumRingEquiv_rename_inl, sumRingEquiv_rename_inr]
  rw [mul_comm
    (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) P)
    (MvPolynomial.C Q)]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  rw [mul_comm Q (MvPolynomial.C (P.coeff d₁))]
  rw [MvPolynomial.coeff_C_mul]

/-- The canonical embedding of a disjoint sum of two variable groups. -/
def sumEmbeddingOfDisjoint {σ τ ρ : Type*} (f : σ ↪ ρ) (g : τ ↪ ρ)
    (hdisj : Disjoint (Set.range f) (Set.range g)) : (σ ⊕ τ) ↪ ρ where
  toFun := Sum.elim f g
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (f.injective h)
        | inr y =>
            have hx : f x ∈ Set.range f := ⟨x, rfl⟩
            have hy : f x ∈ Set.range g := ⟨y, by simpa using h.symm⟩
            exact False.elim ((Set.disjoint_left.mp hdisj hx) hy)
    | inr x =>
        cases y with
        | inl y =>
            have hy : g x ∈ Set.range g := ⟨x, rfl⟩
            have hx : g x ∈ Set.range f := ⟨y, by simpa using h.symm⟩
            exact False.elim ((Set.disjoint_left.mp hdisj hx) hy)
        | inr y => exact congrArg Sum.inr (g.injective h)

/-- The two-group coefficient formula remains valid after embedding both
variable groups into a larger variable type, provided their images are
disjoint. -/
theorem coeff_mul_rename_disjoint {σ τ ρ R : Type*} [CommSemiring R]
    (f : σ ↪ ρ) (g : τ ↪ ρ)
    (hdisj : Disjoint (Set.range f) (Set.range g))
    (P : MvPolynomial σ R) (Q : MvPolynomial τ R)
    (d₁ : σ →₀ ℕ) (d₂ : τ →₀ ℕ) :
    (MvPolynomial.rename f P * MvPolynomial.rename g Q).coeff
      ((d₁.sumElim d₂).embDomain (sumEmbeddingOfDisjoint f g hdisj)) =
      P.coeff d₁ * Q.coeff d₂ := by
  let e := sumEmbeddingOfDisjoint f g hdisj
  have hpoly :
      MvPolynomial.rename f P * MvPolynomial.rename g Q =
        MvPolynomial.rename e
          (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q) := by
    simp only [map_mul, MvPolynomial.rename_rename]
    congr 1 <;> simp [e]
  rw [hpoly, MvPolynomial.coeff_rename_embDomain]
  exact coeff_mul_rename_groups P Q d₁ d₂

/-- Coefficients also factor across three successively split variable
groups. The statement is arranged recursively so it can be iterated over a
finite family of disjoint groups. -/
theorem coeff_mul_three_rename_groups {σ τ υ R : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (Q : MvPolynomial τ R) (S : MvPolynomial υ R)
    (dσ : σ →₀ ℕ) (dτ : τ →₀ ℕ) (dυ : υ →₀ ℕ) :
    (MvPolynomial.rename Sum.inl P *
      MvPolynomial.rename Sum.inr
        (MvPolynomial.rename Sum.inl Q * MvPolynomial.rename Sum.inr S)).coeff
      (dσ.sumElim (dτ.sumElim dυ)) =
      P.coeff dσ * (Q.coeff dτ * S.coeff dυ) := by
  rw [coeff_mul_rename_groups P
    (MvPolynomial.rename Sum.inl Q * MvPolynomial.rename Sum.inr S)
    dσ (dτ.sumElim dυ)]
  rw [coeff_mul_rename_groups Q S dτ dυ]

end Positivity
