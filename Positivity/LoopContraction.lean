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

variable {V E R : Type*} [Fintype V] [Fintype E] [CommRing R]

/-- Regard a matrix over `R` as a constant polynomial matrix. -/
def constantPolynomialMatrix {ι : Type*} (A : Matrix ι ι R) :
    Matrix ι ι (Polynomial R) := fun i j => Polynomial.C (A i j)

/-- A polynomial rank-one update supported in row `i`.  This is the update
`A + X · (eᵢ vᵀ)` written by replacing row `i`. -/
def rankOneRowUpdate {ι : Type*} [DecidableEq ι] (A : Matrix ι ι R)
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
    simpa [M, constantPolynomialMatrix] using
      (RingHom.map_det (Polynomial.C : R →+* Polynomial R) A)
  have hrow : M.updateRow i (M i) = M := by
    ext k j
    by_cases hk : k = i <;> simp [Matrix.updateRow, hk]
  have hreplace : M.updateRow i (fun j => Polynomial.C (v j)) =
      constantPolynomialMatrix (A.updateRow i v) := by
    ext k j
    by_cases hk : k = i <;> simp [Matrix.updateRow, constantPolynomialMatrix, M, hk]
  have hreplaceDet :
      (M.updateRow i (fun j => Polynomial.C (v j))).det =
        Polynomial.C ((A.updateRow i v).det) := by
    rw [hreplace]
    simpa [constantPolynomialMatrix] using
      (RingHom.map_det (Polynomial.C : R →+* Polynomial R) (A.updateRow i v))
  have hupdate : rankOneRowUpdate A i v =
      M.updateRow i (M i + Polynomial.X • fun j => Polynomial.C (v j)) := by
    ext k j
    by_cases hk : k = i <;> simp [rankOneRowUpdate, constantPolynomialMatrix, M,
      Matrix.updateRow, hk, mul_comm]
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
      Polynomial.C ((A.updateRow i v).det) := by
  rw [det_rankOneRowUpdate]
  simp

/-- A polynomial rank-one update supported in column `j`. -/
def rankOneColumnUpdate {ι : Type*} [DecidableEq ι] (A : Matrix ι ι R)
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
    simpa [M, constantPolynomialMatrix] using
      (RingHom.map_det (Polynomial.C : R →+* Polynomial R) A)
  have hcol : M.updateCol j (fun i => M i j) = M := by
    ext i k
    by_cases hk : k = j <;> simp [Matrix.updateCol, hk]
  have hreplace : M.updateCol j (fun i => Polynomial.C (v i)) =
      constantPolynomialMatrix (A.updateCol j v) := by
    ext i k
    by_cases hk : k = j <;> simp [Matrix.updateCol, constantPolynomialMatrix, M, hk]
  have hreplaceDet :
      (M.updateCol j (fun i => Polynomial.C (v i))).det =
        Polynomial.C ((A.updateCol j v).det) := by
    rw [hreplace]
    simpa [constantPolynomialMatrix] using
      (RingHom.map_det (Polynomial.C : R →+* Polynomial R) (A.updateCol j v))
  have hupdate : rankOneColumnUpdate A j v =
      M.updateCol j (M.col j + Polynomial.X • fun i => Polynomial.C (v i)) := by
    ext i k
    by_cases hk : k = j <;> simp [rankOneColumnUpdate, constantPolynomialMatrix, M,
      Matrix.updateCol, hk, mul_comm]
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
      Polynomial.C ((A.updateCol j v).det) := by
  rw [det_rankOneColumnUpdate]
  simp

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

