import Positivity.CoverTreeIdentity
import Positivity.PrimitiveQuotient
import Positivity.CoefficientPositivity
import Mathlib.RingTheory.Localization.FractionRing

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

/-- The covering arborescence ratio as an element of the fraction field of
the integer polynomial ring. Lifted edges inherit their base-edge variables. -/
noncomputable def arborescenceRatio (F : FiniteFiberSystem V E) (r : V) (p : F.Fiber r) :
    FractionRing (MvPolynomial E ℤ) :=
  algebraMap (MvPolynomial E ℤ) _ (F.liftedArborescencePolynomial r p) /
    algebraMap (MvPolynomial E ℤ) _ (arborescencePolynomial F.src F.tgt r)

/-- Manuscript Theorem 1.1, stated as an exact factorization into an integer
polynomial with nonnegative coefficients. The normalization uses the root
fiber size, so the result also applies to disconnected covers of varying degree. -/
theorem covering_arborescence_nonnegative (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (r : V) (p : F.Fiber r)
    (hbase : arborescencePolynomial F.src F.tgt r ≠ 0) :
    ∃ Q : MvPolynomial E ℤ,
      arborescencePolynomial F.src F.tgt r * Q = F.liftedArborescencePolynomial r p ∧
      F.quotientDeterminant = MvPolynomial.C (F.fiberSize r : ℤ) * Q ∧
      ∀ α, 0 ≤ Q.coeff α := by
  apply primitive_positive_quotient _ _ _ (F.fiberSize r)
  · letI := F.fiberFintype r
    exact Fintype.card_pos_iff.mpr ⟨F.reference r⟩
  · exact arborescencePolynomial_primitive F.src F.tgt r hbase
  · exact F.covering_tree_identity hbij r p
  · exact quotientDeterminant_coeff_nonnegative F

/-- The ratio in Theorem 1.1 belongs to the nonnegative integer polynomial ring. -/
theorem arborescenceRatio_nonnegative_integer_polynomial (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (r : V) (p : F.Fiber r)
    (hbase : arborescencePolynomial F.src F.tgt r ≠ 0) :
    ∃ Q : MvPolynomial E ℤ,
      F.arborescenceRatio r p = algebraMap (MvPolynomial E ℤ) _ Q ∧
      (∀ α, 0 ≤ Q.coeff α) ∧
      F.quotientDeterminant = MvPolynomial.C (F.fiberSize r : ℤ) * Q := by
  obtain ⟨Q, hQ, hP, hpos⟩ := F.covering_arborescence_nonnegative hbij r p hbase
  refine ⟨Q, ?_, hpos, hP⟩
  have hne : algebraMap (MvPolynomial E ℤ) (FractionRing (MvPolynomial E ℤ))
      (arborescencePolynomial F.src F.tgt r) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial E ℤ) (FractionRing (MvPolynomial E ℤ))).ne hbase
  rw [arborescenceRatio, ← hQ, map_mul, mul_div_cancel_left₀ _ hne]

/-- The determinant formula in Proposition 2.6, with the positive sheet
count embedded in the fraction field. -/
theorem arborescenceRatio_eq_normalized_determinant (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (r : V) (p : F.Fiber r)
    (hbase : arborescencePolynomial F.src F.tgt r ≠ 0) :
    F.arborescenceRatio r p =
      algebraMap (MvPolynomial E ℤ) (FractionRing (MvPolynomial E ℤ)) F.quotientDeterminant /
        (F.fiberSize r : FractionRing (MvPolynomial E ℤ)) := by
  obtain ⟨Q, hQ, _, hP⟩ := F.arborescenceRatio_nonnegative_integer_polynomial hbij r p hbase
  have hp : 0 < F.fiberSize r := by
    letI := F.fiberFintype r
    exact Fintype.card_pos_iff.mpr ⟨F.reference r⟩
  have hk : (F.fiberSize r : FractionRing (MvPolynomial E ℤ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hp
  rw [hQ, hP, map_mul]
  simp only [map_natCast]
  exact (mul_div_cancel_left₀ _ hk).symm

end Positivity.FiniteFiberSystem
