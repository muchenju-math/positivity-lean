import Positivity.FiniteFiber
import Positivity.DeterminantDerivative

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

variable {V E R : Type*} [Fintype V] [Fintype E] [CommRing R]

/-- Removing one point from a finite type subtracts one from its natural
cardinality. -/
theorem natCard_subtype_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype {x : α // x ≠ a} := Fintype.ofFinite _
  letI : Fintype {x : α // x = a} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : α => x = a)]
  simp [Fintype.card_subtype_eq]

/-- Regard a matrix over `R` as a constant polynomial matrix. -/
noncomputable def constantPolynomialMatrix {ι : Type*} (A : Matrix ι ι R) :
    Matrix ι ι (Polynomial R) := fun i j => Polynomial.C (A i j)

/-- A polynomial rank-one update supported in row `i`.  This is the update
`A + X · (eᵢ vᵀ)` written by replacing row `i`. -/
noncomputable def rankOneRowUpdate {ι : Type*} [DecidableEq ι] (A : Matrix ι ι R)
    (i : ι) (v : ι → R) : Matrix ι ι (Polynomial R) :=
  (constantPolynomialMatrix A).updateRow i fun j =>
    Polynomial.C (A i j) + Polynomial.X * Polynomial.C (v j)

/-- The determinant derivative for an arbitrary row-supported rank-one
perturbation.  Equivalently, the determinant polynomial is affine in the
update variable, and its linear coefficient is the determinant with that row
replaced by the perturbing vector. -/
theorem det_rankOneRowUpdate {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A : Matrix ι ι R) (i : ι)
    (v : ι → R) :
    (rankOneRowUpdate A i v).det =
      Polynomial.C A.det + Polynomial.X * Polynomial.C ((A.updateRow i v).det) := by
  classical
  let M := constantPolynomialMatrix A
  have hMdet : M.det = Polynomial.C A.det := by
    change (A.map (Polynomial.C : R →+* Polynomial R)).det = _
    exact (RingHom.map_det (Polynomial.C : R →+* Polynomial R) A).symm
  have hrow : M.updateRow i (M i) = M := Matrix.updateRow_eq_self M i
  have hreplace : M.updateRow i (fun j => Polynomial.C (v j)) =
      constantPolynomialMatrix (A.updateRow i v) := by
    funext k j
    rw [Matrix.updateRow_apply]
    by_cases hk : k = i <;> simp [hk, constantPolynomialMatrix, M]
  have hreplaceDet :
      (M.updateRow i (fun j => Polynomial.C (v j))).det =
        Polynomial.C ((A.updateRow i v).det) := by
    rw [hreplace]
    change ((A.updateRow i v).map (Polynomial.C : R →+* Polynomial R)).det = _
    exact (RingHom.map_det (Polynomial.C : R →+* Polynomial R) (A.updateRow i v)).symm
  have hupdate : rankOneRowUpdate A i v =
      M.updateRow i (M i + (Polynomial.X : Polynomial R) •
        (fun j : ι => (Polynomial.C (v j) : Polynomial R))) := by
    funext k j
    rw [Matrix.updateRow_apply]
    by_cases hk : k = i <;> simp [rankOneRowUpdate, constantPolynomialMatrix, M,
      hk, smul_eq_mul]
  calc
    (rankOneRowUpdate A i v).det =
        (M.updateRow i (M i + Polynomial.X • fun j => Polynomial.C (v j))).det := by
          rw [hupdate]
    _ = (M.updateRow i (M i)).det +
          (M.updateRow i (Polynomial.X • fun j => Polynomial.C (v j))).det :=
        Matrix.det_updateRow_add M i (M i) (Polynomial.X • fun j => Polynomial.C (v j))
    _ = M.det + Polynomial.X *
          (M.updateRow i (fun j => Polynomial.C (v j))).det := by
        rw [hrow, Matrix.det_updateRow_smul]
    _ = Polynomial.C A.det + Polynomial.X *
          Polynomial.C ((A.updateRow i v).det) := by rw [hMdet, hreplaceDet]

/-- Evaluating the formal derivative of the rank-one row update at zero
returns the determinant with the affected row replaced by the update vector. -/
theorem deriv_det_rankOneRowUpdate_at_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι R) (i : ι) (v : ι → R) :
    ((rankOneRowUpdate A i v).det.derivative).eval 0 =
       (A.updateRow i v).det := by
  rw [det_rankOneRowUpdate]
  simp

/-- A polynomial rank-one update supported in column `j`. -/
noncomputable def rankOneColumnUpdate {ι : Type*} [DecidableEq ι] (A : Matrix ι ι R)
    (j : ι) (v : ι → R) : Matrix ι ι (Polynomial R) :=
  (constantPolynomialMatrix A).updateCol j fun i =>
    Polynomial.C (A i j) + Polynomial.X * Polynomial.C (v i)

/-- Column-supported version of the rank-one determinant derivative. -/
theorem det_rankOneColumnUpdate {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A : Matrix ι ι R) (j : ι) (v : ι → R) :
    (rankOneColumnUpdate A j v).det =
      Polynomial.C A.det + Polynomial.X * Polynomial.C ((A.updateCol j v).det) := by
  classical
  let M := constantPolynomialMatrix A
  have hMdet : M.det = Polynomial.C A.det := by
    change (A.map (Polynomial.C : R →+* Polynomial R)).det = _
    exact (RingHom.map_det (Polynomial.C : R →+* Polynomial R) A).symm
  have hcol : M.updateCol j (M.col j) = M := Matrix.updateCol_eq_self M j
  have hreplace : M.updateCol j (fun i => Polynomial.C (v i)) =
      constantPolynomialMatrix (A.updateCol j v) := by
    funext i k
    rw [Matrix.updateCol_apply]
    by_cases hk : k = j <;> simp [hk, constantPolynomialMatrix, M]
  have hreplaceDet :
      (M.updateCol j (fun i => Polynomial.C (v i))).det =
        Polynomial.C ((A.updateCol j v).det) := by
    rw [hreplace]
    change ((A.updateCol j v).map (Polynomial.C : R →+* Polynomial R)).det = _
    exact (RingHom.map_det (Polynomial.C : R →+* Polynomial R) (A.updateCol j v)).symm
  have hupdate : rankOneColumnUpdate A j v =
      M.updateCol j (M.col j + (Polynomial.X : Polynomial R) •
        (fun i : ι => (Polynomial.C (v i) : Polynomial R))) := by
    funext i k
    rw [Matrix.updateCol_apply]
    by_cases hk : k = j <;> simp [rankOneColumnUpdate, constantPolynomialMatrix, M,
      hk, smul_eq_mul]
  calc
    (rankOneColumnUpdate A j v).det =
        (M.updateCol j (M.col j + Polynomial.X • fun i => Polynomial.C (v i))).det := by
          rw [hupdate]
    _ = (M.updateCol j (M.col j)).det +
          (M.updateCol j (Polynomial.X • fun i => Polynomial.C (v i))).det :=
        Matrix.det_updateCol_add M j (M.col j) (Polynomial.X • fun i => Polynomial.C (v i))
    _ = M.det + Polynomial.X *
          (M.updateCol j (fun i => Polynomial.C (v i))).det := by
        rw [hcol, Matrix.det_updateCol_smul]
    _ = Polynomial.C A.det + Polynomial.X *
          Polynomial.C ((A.updateCol j v).det) := by rw [hMdet, hreplaceDet]

/-- Evaluating the column-update determinant derivative at zero gives the
determinant with that column replaced by the update vector. -/
theorem deriv_det_rankOneColumnUpdate_at_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι R) (j : ι) (v : ι → R) :
    ((rankOneColumnUpdate A j v).det.derivative).eval 0 =
       (A.updateCol j v).det := by
  rw [det_rankOneColumnUpdate]
  simp

namespace FiniteFiberSystem

/-- The edge type after removing one labelled edge. This wrapper keeps its
finite-type instance separate from unrelated vertex subtypes. -/
structure EdgesExcept (e : E) where
  val : E
  property : val ≠ e

@[ext] theorem EdgesExcept.ext {e : E} {a b : EdgesExcept e} (h : a.val = b.val) :
    a = b := by
  cases a with
  | mk av ap => cases b with
    | mk bv bp => simp_all

instance (e : E) : CoeOut (EdgesExcept e) E := ⟨EdgesExcept.val⟩

noncomputable instance edgesExceptFintype (e : E) : Fintype (EdgesExcept e) := by
  classical
  letI : Fintype {f : E // f ≠ e} := Fintype.ofFinite _
  let equiv : {f : E // f ≠ e} ≃ EdgesExcept e := {
    toFun := fun f => ⟨f.1, f.2⟩
    invFun := fun f => ⟨f.val, f.property⟩
    left_inv := by intro f; cases f; rfl
    right_inv := by intro f; cases f; rfl
  }
  exact Fintype.ofEquiv {f : E // f ≠ e} equiv

/-- The contracted fiber over `v`.  At the contracted vertex, the element
`p` is removed; fibers over all other vertices are unchanged. -/
noncomputable def contractedFiber (F : FiniteFiberSystem V E) (u : V)
    (p : F.Fiber u) (v : V) : Type _ := by
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
source fiber and their target values are redirected along `p ↦ q`.
The reference point is retained when it survives, and redirected to `q`
when the removed point was the reference. -/
noncomputable def contractMovedEdge (F : FiniteFiberSystem V E) (u : V)
    (p q : F.Fiber u) (hpq : p ≠ q) : FiniteFiberSystem V E := by
  classical
  let CF : V → Type _ := fun v => F.contractedFiber u p v
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
      simpa [CF, contractedFiber] using redirectValue p q hpq (F.reference u)
    · simpa [CF, contractedFiber, h] using F.reference v
  let cmap : ∀ e, CF (F.src e) → CF (F.tgt e) := by
    intro e x
    by_cases hs : F.src e = u
    · by_cases ht : F.tgt e = u
      · have hsrc : CF (F.src e) = {x : F.Fiber u // x ≠ p} := by
          simp [CF, contractedFiber, hs]
        have htgt : CF (F.tgt e) = {x : F.Fiber u // x ≠ p} := by
          simp [CF, contractedFiber, ht]
        rw [hsrc] at x
        rw [htgt]
        exact redirectValue p q hpq (ht ▸ F.fiberMap e (hs.symm ▸ x.1))
      · have hsrc : CF (F.src e) = {x : F.Fiber u // x ≠ p} := by
          simp [CF, contractedFiber, hs]
        have htgt : CF (F.tgt e) = F.Fiber (F.tgt e) := by
          simp [CF, contractedFiber, ht]
        rw [hsrc] at x
        rw [htgt]
        exact F.fiberMap e (hs.symm ▸ x.1)
    · by_cases ht : F.tgt e = u
      · have hsrc : CF (F.src e) = F.Fiber (F.src e) := by
          simp [CF, contractedFiber, hs]
        have htgt : CF (F.tgt e) = {x : F.Fiber u // x ≠ p} := by
          simp [CF, contractedFiber, ht]
        rw [hsrc] at x
        rw [htgt]
        exact redirectValue p q hpq (ht ▸ F.fiberMap e x)
      · have hsrc : CF (F.src e) = F.Fiber (F.src e) := by
          simp [CF, contractedFiber, hs]
        have htgt : CF (F.tgt e) = F.Fiber (F.tgt e) := by
          simp [CF, contractedFiber, ht]
        rw [hsrc] at x
        rw [htgt]
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

/-- Delete one base-edge label while retaining all fibers and the maps on
the remaining edges.  This is kept separate from contraction because a
loop recurrence contracts a lifted edge and then deletes its base loop. -/
noncomputable def deleteEdge (F : FiniteFiberSystem V E) (e : E) :
    FiniteFiberSystem V (EdgesExcept e) := by
  classical
  exact {
    src := fun f => F.src f.val
    tgt := fun f => F.tgt f.val
    Fiber := F.Fiber
    fiberFintype := F.fiberFintype
    reference := F.reference
    fiberMap := fun f => F.fiberMap f.val
  }

@[simp] theorem deleteEdge_src (F : FiniteFiberSystem V E) (e : E)
    (f : EdgesExcept e) : (F.deleteEdge e).src f = F.src f.val := rfl

@[simp] theorem deleteEdge_tgt (F : FiniteFiberSystem V E) (e : E)
    (f : EdgesExcept e) : (F.deleteEdge e).tgt f = F.tgt f.val := rfl

@[simp] theorem deleteEdge_fiberMap (F : FiniteFiberSystem V E) (e : E)
    (f : EdgesExcept e) (x : F.Fiber (F.src f.val)) :
    (F.deleteEdge e).fiberMap f x = F.fiberMap f.val x := rfl

/-- The child system for a loop-contraction step: contract the selected
lift `p → F.fiberMap e p`, then remove the base-loop label `e`. -/
noncomputable def contractLoopEdge (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) :
    FiniteFiberSystem V (EdgesExcept e) := by
  let u := F.src e
  let q : F.Fiber u := F.loopTargetInSource e he p
  let C := F.contractMovedEdge u p q hp
  exact C.deleteEdge e

@[simp] theorem contractLoopEdge_src (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) (f : EdgesExcept e) :
    (F.contractLoopEdge e he p hp).src f = F.src f.val := rfl

@[simp] theorem contractLoopEdge_tgt (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) (f : EdgesExcept e) :
    (F.contractLoopEdge e he p hp).tgt f = F.tgt f.val := rfl

@[simp] theorem contractLoopEdge_fiberMap (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) (f : EdgesExcept e)
    (x : (F.contractMovedEdge (F.src e) p (F.loopTargetInSource e he p) hp).Fiber (F.src f.val)) :
    (F.contractLoopEdge e he p hp).fiberMap f x =
      (F.contractMovedEdge (F.src e) p (F.loopTargetInSource e he p) hp).fiberMap f.val x := rfl

/-- Contracting a moved loop lift removes exactly one point from its base
fiber; deleting the loop label does not affect any fiber. -/
theorem contractLoopEdge_fiberSize_at (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) :
    (F.contractLoopEdge e he p hp).fiberSize (F.src e) =
      F.fiberSize (F.src e) - 1 := by
  classical
  have htype : (F.contractLoopEdge e he p hp).Fiber (F.src e) =
      {x : F.Fiber (F.src e) // x ≠ p} := by
    simp [contractLoopEdge, deleteEdge, contractMovedEdge, contractedFiber]
  letI : Fintype ((F.contractLoopEdge e he p hp).Fiber (F.src e)) :=
    (F.contractLoopEdge e he p hp).fiberFintype (F.src e)
  letI : Fintype (F.Fiber (F.src e)) := F.fiberFintype (F.src e)
  letI : Fintype {x : F.Fiber (F.src e) // x ≠ p} := inferInstance
  calc
    (F.contractLoopEdge e he p hp).fiberSize (F.src e) =
        Fintype.card ((F.contractLoopEdge e he p hp).Fiber (F.src e)) := rfl
    _ = Fintype.card {x : F.Fiber (F.src e) // x ≠ p} :=
      Fintype.card_congr (Equiv.cast htype)
    _ = F.fiberSize (F.src e) - 1 := by
      simp [fiberSize, Fintype.card_subtype_compl]

/-- The quotient dimension drops by one at the contracted vertex. -/
theorem contractLoopEdge_fiberDimension_at (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) :
    (F.contractLoopEdge e he p hp).fiberDimension (F.src e) =
    F.fiberDimension (F.src e) - 1 := by
  simp [fiberDimension, contractLoopEdge_fiberSize_at]

/-- Fibers away from the contracted vertex keep their cardinalities. -/
theorem contractLoopEdge_fiberSize_of_ne (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) (v : V) (hv : v ≠ F.src e) :
    (F.contractLoopEdge e he p hp).fiberSize v = F.fiberSize v := by
  classical
  have htype : (F.contractLoopEdge e he p hp).Fiber v = F.Fiber v := by
    simp [contractLoopEdge, deleteEdge, contractMovedEdge, contractedFiber, hv]
  letI : Fintype ((F.contractLoopEdge e he p hp).Fiber v) :=
    (F.contractLoopEdge e he p hp).fiberFintype v
  letI : Fintype (F.Fiber v) := F.fiberFintype v
  calc
    (F.contractLoopEdge e he p hp).fiberSize v =
        Fintype.card ((F.contractLoopEdge e he p hp).Fiber v) := rfl
    _ = Fintype.card (F.Fiber v) := Fintype.card_congr (Equiv.cast htype)
    _ = F.fiberSize v := rfl

/-- Away from the contracted vertex, the quotient dimensions are unchanged. -/
theorem contractLoopEdge_fiberDimension_of_ne (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) (v : V) (hv : v ≠ F.src e) :
    (F.contractLoopEdge e he p hp).fiberDimension v = F.fiberDimension v := by
  simp [fiberDimension, contractLoopEdge_fiberSize_of_ne, hv]

/-- The total quotient dimension drops by exactly one in a loop child. -/
theorem contractLoopEdge_totalDimension (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) :
    (F.contractLoopEdge e he p hp).totalDimension = F.totalDimension - 1 := by
  classical
  let C := F.contractLoopEdge e he p hp
  rw [C.totalDimension_eq_sum_fiberDimension, F.totalDimension_eq_sum_fiberDimension]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (F.src e)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (F.src e))]
  have hsum : (∑ v ∈ Finset.univ.erase (F.src e), C.fiberDimension v) =
      ∑ v ∈ Finset.univ.erase (F.src e), F.fiberDimension v := by
    apply Finset.sum_congr rfl
    intro v hv
    exact contractLoopEdge_fiberDimension_of_ne F e he p hp v
      (Finset.mem_erase.mp hv).1
  let f : Fin 2 → F.Fiber (F.src e) := fun i =>
    if i.val = 0 then p else F.loopTargetInSource e he p
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hp (by simpa [f] using hij))
    · exact False.elim (hp (by simpa [f] using hij.symm))
    · rfl
  letI : Fintype (F.Fiber (F.src e)) := F.fiberFintype (F.src e)
  have hcard : 2 ≤ F.fiberSize (F.src e) := by
    simpa [fiberSize] using Fintype.card_le_of_injective f hf
  have hdimpos : 1 ≤ F.fiberDimension (F.src e) := by
    simp only [fiberDimension]
    omega
  rw [hsum, contractLoopEdge_fiberDimension_at]
  omega

/-- Deleting a loop edge lowers the outdegree at its source by one. -/
theorem contractLoopEdge_outdegree_at (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) :
    (F.contractLoopEdge e he p hp).outdegree (F.src e) = F.outdegree (F.src e) - 1 := by
  classical
  let U : Type _ := {f : E // F.src f = F.src e}
  let C := F.contractLoopEdge e he p hp
  let ChildU : Type _ := {f : EdgesExcept e // C.src f = F.src e}
  let heU : U := ⟨e, rfl⟩
  let Removed : Type _ := {f : U // f ≠ heU}
  let equiv : ChildU ≃ Removed := {
    toFun := fun (f : ChildU) =>
      (⟨(⟨f.1.val, f.2⟩ : U), by
        intro h
        apply f.1.property
        exact congrArg Subtype.val h⟩ : Removed)
    invFun := fun (f : Removed) =>
      (⟨(⟨f.1.val, by
        intro h
        apply f.2
        apply Subtype.ext
        exact h⟩ : EdgesExcept e), f.1.property⟩ : ChildU)
    left_inv := by intro f; apply Subtype.ext; apply EdgesExcept.ext; rfl
    right_inv := by intro f; apply Subtype.ext; rfl
  }
  letI : Fintype U := Fintype.ofFinite U
  calc
    C.outdegree (F.src e) = Nat.card ChildU := rfl
    _ = Nat.card Removed := Nat.card_congr equiv
    _ = Nat.card U - 1 := by
      change Nat.card {f : U // f ≠ heU} = Nat.card U - 1
      exact natCard_subtype_ne (α := U) heU
    _ = F.outdegree (F.src e) - 1 := rfl

/-- Outdegrees away from the deleted loop source are unchanged. -/
theorem contractLoopEdge_outdegree_of_ne (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) (v : V) (hv : v ≠ F.src e) :
    (F.contractLoopEdge e he p hp).outdegree v = F.outdegree v := by
  classical
  let C := F.contractLoopEdge e he p hp
  let ChildU : Type _ := {f : EdgesExcept e // C.src f = v}
  let BaseU : Type _ := {f : E // F.src f = v}
  let equiv : ChildU ≃ BaseU := {
    toFun := fun (f : ChildU) => by
      refine ⟨f.1.val, ?_⟩
      simpa [C, contractLoopEdge, deleteEdge, contractMovedEdge] using f.2
    invFun := fun (f : BaseU) =>
      ⟨⟨f.1, by
        intro h
        apply hv
        simpa [C, contractLoopEdge, deleteEdge, contractMovedEdge, h] using f.2.symm⟩,
        by simpa [C, contractLoopEdge, deleteEdge, contractMovedEdge] using f.2⟩
    left_inv := by intro f; apply Subtype.ext; apply EdgesExcept.ext; rfl
    right_inv := by intro f; apply Subtype.ext; rfl
  }
  exact Nat.card_congr equiv

/-- Contracting a moved lift of a base loop and deleting that base edge
preserves balance. -/
theorem Balanced.contractLoopEdge (F : FiniteFiberSystem V E) (hF : F.Balanced)
    (e : E) (he : F.src e = F.tgt e) (p : F.Fiber (F.src e))
    (hp : p ≠ F.loopTargetInSource e he p) :
    (F.contractLoopEdge e he p hp).Balanced := by
  intro v
  by_cases hv : v = F.src e
  · subst v
    rw [contractLoopEdge_outdegree_at, contractLoopEdge_fiberDimension_at, hF]
  · rw [contractLoopEdge_outdegree_of_ne F e he p hp v hv,
      contractLoopEdge_fiberDimension_of_ne F e he p hp v hv, hF]

end FiniteFiberSystem

theorem edgesExcept_val_injective (e : E) :
    Function.Injective (EdgesExcept.val : EdgesExcept e → E) :=
  fun _ _ h => EdgesExcept.ext h

/-- Set the deleted edge variable to zero and retain the other labels. -/
noncomputable def deleteEdgeVariables (e : E) :
    MvPolynomial E ℤ →ₐ[ℤ] MvPolynomial (EdgesExcept e) ℤ :=
  MvPolynomial.killCompl (edgesExcept_val_injective e)

@[simp] theorem deleteEdgeVariables_X_self (e : E) :
    deleteEdgeVariables e (MvPolynomial.X e) = 0 := by
  classical
  have h : e ∉ Set.range (EdgesExcept.val : EdgesExcept e → E) := by
    rintro ⟨f, hf⟩
    exact f.property hf
  simp only [deleteEdgeVariables, MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg h]

@[simp] theorem deleteEdgeVariables_X (e : E) (f : EdgesExcept e) :
    deleteEdgeVariables e (MvPolynomial.X f.val) = MvPolynomial.X f := by
  simpa only [deleteEdgeVariables, MvPolynomial.rename_X] using
    MvPolynomial.killCompl_rename_app (edgesExcept_val_injective e) (MvPolynomial.X f : MvPolynomial (EdgesExcept e) ℤ)

@[simp] theorem deleteEdgeVariables_C (e : E) (z : ℤ) :
    deleteEdgeVariables e (MvPolynomial.C z) = MvPolynomial.C z :=
  MvPolynomial.killCompl_C _ z

theorem deleteEdge_quotientEdgeCoefficient (F : FiniteFiberSystem V E) (e : E)
    (f : EdgesExcept e) (i j : F.Coord) :
    (F.deleteEdge e).quotientEdgeCoefficient f i j = F.quotientEdgeCoefficient f.val i j := by
  classical
  rfl

theorem deleteEdgeVariables_quotientLaplacian (F : FiniteFiberSystem V E) (e : E)
    (i j : F.Coord) :
    deleteEdgeVariables e (F.quotientLaplacian i j) =
      (F.deleteEdge e).quotientLaplacian i j := by
  classical
  simp only [FiniteFiberSystem.quotientLaplacian, map_sum, map_mul, deleteEdgeVariables_C,
    deleteEdge_quotientEdgeCoefficient]
  symm
  apply Finset.sum_bij_ne_zero (fun f _ _ => f.val)
  · intro f hf hne
    exact Finset.mem_univ _
  · intro f g hf hg hfn hgn hfg
    exact EdgesExcept.ext hfg
  · intro f hf hfn
    have hfe : f ≠ e := by
      rintro rfl
      simp at hfn
    refine ⟨⟨f, hfe⟩, Finset.mem_univ _, ?_, rfl⟩
    have hx := deleteEdgeVariables_X e (⟨f, hfe⟩ : EdgesExcept e)
    change deleteEdgeVariables e (MvPolynomial.X f) = MvPolynomial.X (⟨f, hfe⟩ : EdgesExcept e) at hx
    rwa [hx] at hfn
  · intro f hf hfn
    simp

theorem deleteEdgeVariables_quotientDeterminant (F : FiniteFiberSystem V E) (e : E) :
    deleteEdgeVariables e F.quotientDeterminant = (F.deleteEdge e).quotientDeterminant := by
  classical
  change deleteEdgeVariables e F.quotientLaplacian.det = (F.deleteEdge e).quotientLaplacian.det
  rw [AlgHom.map_det]
  congr 1
  funext i j
  exact deleteEdgeVariables_quotientLaplacian F e i j

theorem pderiv_quotientLaplacian (F : FiniteFiberSystem V E) (e : E) (i j : F.Coord) :
    MvPolynomial.pderiv e (F.quotientLaplacian i j) =
      MvPolynomial.C (F.quotientEdgeCoefficient e i j) := by
  classical
  simp [FiniteFiberSystem.quotientLaplacian, map_sum, Pi.single_apply]

theorem pderiv_quotientDeterminant_rows (F : FiniteFiberSystem V E) (e : E) :
    MvPolynomial.pderiv e F.quotientDeterminant =
      ∑ i : F.Coord, (F.quotientLaplacian.updateRow i
        (fun j => MvPolynomial.C (F.quotientEdgeCoefficient e i j))).det := by
  classical
  rw [FiniteFiberSystem.quotientDeterminant, derivation_det_rows]
  simp_rw [pderiv_quotientLaplacian]

theorem specialized_pderiv_quotientDeterminant_rows (F : FiniteFiberSystem V E) (e : E) :
    deleteEdgeVariables e (MvPolynomial.pderiv e F.quotientDeterminant) =
      ∑ i : F.Coord, ((F.deleteEdge e).quotientLaplacian.updateRow i
        (fun j => MvPolynomial.C (F.quotientEdgeCoefficient e i j))).det := by
  classical
  rw [pderiv_quotientDeterminant_rows, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [AlgHom.map_det]
  congr 1
  funext j k
  change deleteEdgeVariables e ((F.quotientLaplacian.updateRow i
    (fun l => MvPolynomial.C (F.quotientEdgeCoefficient e i l))) j k) =
    (Matrix.updateRow (m := F.Coord) (n := F.Coord)
      (F.deleteEdge e).quotientLaplacian i
      (fun l => MvPolynomial.C (F.quotientEdgeCoefficient e i l))) j k
  by_cases h : j = i
  · subst j
    simp only [Matrix.updateRow_self, deleteEdgeVariables_C]
    exact (congrFun (Matrix.updateRow_self (M := (F.deleteEdge e).quotientLaplacian)
      (i := i) (b := fun l => MvPolynomial.C (F.quotientEdgeCoefficient e i l))) k).symm
  · simp only [Matrix.updateRow_apply, if_neg h]
    rw [deleteEdgeVariables_quotientLaplacian F e j k]
    exact (congrFun (Matrix.updateRow_ne (M := (F.deleteEdge e).quotientLaplacian)
      (b := fun l => MvPolynomial.C (F.quotientEdgeCoefficient e i l)) h) k).symm


end Positivity
