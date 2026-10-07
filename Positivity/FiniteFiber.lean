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
def pullback (e : E) : Matrix (F.CoordAt (F.src e)) (F.CoordAt (F.tgt e)) ℤ :=
  fun p q =>
    (if F.fiberMap e p.1 = q.1 then 1 else 0) -
    (if F.fiberMap e (F.reference (F.src e)) = q.1 then 1 else 0)

/-- The cardinality of the fiber over a base vertex. -/
def fiberSize (v : V) : ℕ := @Fintype.card (F.Fiber v) (F.fiberFintype v)

/-- The number of quotient coordinates contributed by a fiber. -/
def fiberDimension (v : V) : ℕ := F.fiberSize v - 1

/-- Outdegree, counting parallel edges separately and counting a loop once. -/
def outdegree (v : V) : ℕ := (Finset.univ.filter fun e : E => F.src e = v).card

/-- Total dimension of the quotient coordinate space. -/
def totalDimension : ℕ := Fintype.card F.Coord

/-- A system is balanced when the base outdegree equals the quotient
dimension of every fiber. -/
def Balanced : Prop := ∀ v, F.outdegree v = F.fiberDimension v

/-- The block-entry formula for the quotient Laplacian.  The first term is
the source outdegree times the identity block; each edge contributes the
negative of its normalized pullback block. -/
def quotientLaplacian : Matrix F.Coord F.Coord (MvPolynomial E ℤ) := by
  classical
  exact fun i j =>
    (if i = j then
      ∑ e : E, (if F.src e = i.1 then MvPolynomial.X e else 0)
     else 0) -
    ∑ e : E,
      if hsrc : i.1 = F.src e then
        if htgt : j.1 = F.tgt e then
          MvPolynomial.X e *
            (((if F.fiberMap e (hsrc ▸ i.2.1) = htgt ▸ j.2.1 then (1 : ℤ) else 0) -
              (if F.fiberMap e (F.reference (F.src e)) = htgt ▸ j.2.1 then (1 : ℤ) else 0)) : MvPolynomial E ℤ)
        else 0
      else 0

/-- The determinant polynomial of the induced quotient Laplacian. -/
def quotientDeterminant : MvPolynomial E ℤ := Matrix.det F.quotientLaplacian

@[simp] theorem quotientLaplacian_apply (i j : F.Coord) :
    F.quotientLaplacian i j =
      (if i = j then
        ∑ e : E, (if F.src e = i.1 then MvPolynomial.X e else 0)
       else 0) -
      ∑ e : E,
        if hsrc : i.1 = F.src e then
          if htgt : j.1 = F.tgt e then
            MvPolynomial.X e *
              (((if F.fiberMap e (hsrc ▸ i.2.1) = htgt ▸ j.2.1 then (1 : ℤ) else 0) -
                (if F.fiberMap e (F.reference (F.src e)) = htgt ▸ j.2.1 then (1 : ℤ) else 0)) : MvPolynomial E ℤ)
          else 0
        else 0 := rfl

end FiniteFiberSystem

end Positivity
