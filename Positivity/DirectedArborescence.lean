import Positivity.EliminationCoefficientAlgebra

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

/-- One labeled outgoing edge from every vertex other than the root. -/
def RootChoice (src : E → V) (r : V) :=
  {f : {v : V // v ≠ r} → E // ∀ v, src (f v) = v.val}

noncomputable instance rootChoiceFintype (src : E → V) (r : V) : Fintype (RootChoice src r) := by
  classical
  unfold RootChoice
  infer_instance

namespace RootChoice

theorem edge_injective {src : E → V} {r : V} (t : RootChoice src r) :
    Function.Injective t.val := by
  intro v w h
  apply Subtype.ext
  have hs := congrArg src h
  simpa only [t.property] using hs

noncomputable def next {src : E → V} {r : V} (t : RootChoice src r) (tgt : E → V) (v : V) : V :=
  if h : v = r then r else tgt (t.val ⟨v, h⟩)

/-- Every selected path reaches the root. This excludes directed cycles
among nonroot vertices, and includes the empty tree on a single vertex. -/
def ReachesRoot {src : E → V} {r : V} (t : RootChoice src r) (tgt : E → V) : Prop :=
  ∀ v : V, ∃ n : ℕ, (t.next tgt)^[n] v = r

noncomputable def exponent {src : E → V} {r : V} (t : RootChoice src r) : E →₀ ℕ :=
  choiceExponent t.val

theorem exponent_at_edge {src : E → V} {r : V} (t : RootChoice src r)
    (v : {v : V // v ≠ r}) : t.exponent (t.val v) = 1 := by
  classical
  simp [exponent, choiceExponent, Finsupp.finsetSum_apply, Finsupp.single_apply, t.edge_injective.eq_iff]

theorem exponent_injective (src : E → V) (r : V) :
    Function.Injective (exponent (src := src) (r := r)) := by
  classical
  intro t s h
  apply Subtype.ext
  funext v
  have hv : s.exponent (t.val v) = 1 := by rw [← h]; exact t.exponent_at_edge v
  have hex : ∃ w, s.val w = t.val v := by
    by_contra hn
    have hz : s.exponent (t.val v) = 0 := by
      simp only [exponent, choiceExponent, Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro w _
      exact Finsupp.single_eq_of_ne (fun he => hn ⟨w, he.symm⟩)
    omega
  obtain ⟨w, hw⟩ := hex
  have hwv : w = v := by
    apply Subtype.ext
    have hh := congrArg src hw
    simpa only [t.property, s.property] using hh
  subst w
  exact hw.symm

end RootChoice

/-- A directed spanning arborescence oriented toward the designated root. -/
def DirectedArborescence (src tgt : E → V) (r : V) :=
  {t : RootChoice src r // t.ReachesRoot tgt}

noncomputable instance directedArborescenceFintype (src tgt : E → V) (r : V) :
    Fintype (DirectedArborescence src tgt r) := by
  classical
  unfold DirectedArborescence
  infer_instance

/-- Distinct labeled trees contribute distinct monomials, each with
coefficient one. Parallel edges retain their independent labels. -/
noncomputable def arborescencePolynomial (src tgt : E → V) (r : V) : MvPolynomial E ℤ :=
  ∑ t : DirectedArborescence src tgt r, MvPolynomial.monomial t.val.exponent 1

theorem arborescencePolynomial_coeff_tree (src tgt : E → V) (r : V)
    (t : DirectedArborescence src tgt r) :
    (arborescencePolynomial src tgt r).coeff t.val.exponent = 1 := by
  classical
  simp only [arborescencePolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hst
    have hn : s.val.exponent ≠ t.val.exponent := by
      intro he
      exact hst (Subtype.ext (RootChoice.exponent_injective src r he))
    simp [hn]
  · simp

theorem arborescencePolynomial_ne_zero_iff (src tgt : E → V) (r : V) :
    arborescencePolynomial src tgt r ≠ 0 ↔ Nonempty (DirectedArborescence src tgt r) := by
  classical
  constructor
  · intro h
    by_contra hn
    haveI : IsEmpty (DirectedArborescence src tgt r) := not_nonempty_iff.mp hn
    simp [arborescencePolynomial] at h
  · rintro ⟨t⟩ h
    have hc := arborescencePolynomial_coeff_tree src tgt r t
    rw [h] at hc
    simp at hc

theorem arborescencePolynomial_primitive (src tgt : E → V) (r : V)
    (h : arborescencePolynomial src tgt r ≠ 0) (d : ℤ)
    (hd : ∀ α, d ∣ (arborescencePolynomial src tgt r).coeff α) : IsUnit d := by
  obtain ⟨t⟩ := (arborescencePolynomial_ne_zero_iff src tgt r).mp h
  have ht := hd t.val.exponent
  rw [arborescencePolynomial_coeff_tree] at ht
  exact isUnit_of_dvd_one ht

end Positivity
