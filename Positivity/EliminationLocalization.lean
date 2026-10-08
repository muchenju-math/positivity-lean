import Positivity.EliminationDeterminant
import Mathlib.RingTheory.Localization.FractionRing

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E R : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [CommRing R] [IsDomain R]

noncomputable def eliminationSubstitution (F : FiniteFiberSystem V E) (u : V)
    (φ : MvPolynomial E ℤ →+* R) (r : R) :
    MvPolynomial (F.Away u ⊕ (F.Incoming u × F.Outgoing u)) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R)
    (Sum.elim (fun a => φ (MvPolynomial.X a.val))
      (fun ab => φ (MvPolynomial.X ab.1.val) * φ (MvPolynomial.X ab.2.val) * r))

/-- The elimination identity also holds in a polynomial coefficient ring
where the outgoing sum has an explicitly supplied inverse. -/
theorem quotientDeterminant_elimination_substitution (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e) (φ : MvPolynomial E ℤ →+* R)
    (r : R) (hr : φ (F.outgoingWeightSum u) * r = 1) :
    φ F.quotientDeterminant = φ (F.outgoingWeightSum u) ^ F.fiberDimension u *
      F.eliminationSubstitution u φ r (F.eliminateSystemAllCompositions u hloop).quotientDeterminant := by
  classical
  let ι : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hmul : ι (φ (F.outgoingWeightSum u)) * ι r = 1 := by
    rw [← map_mul, hr, map_one]
  have hs : ι (φ (F.outgoingWeightSum u)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  have hinv : ι r = (ι (φ (F.outgoingWeightSum u)))⁻¹ := by
    apply (mul_left_cancel₀ hs)
    rw [hmul, mul_inv_cancel₀ hs]
  have hev : F.eliminationEvaluation u (ι.comp φ) =
      ι.comp (F.eliminationSubstitution u φ r) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [eliminationEvaluation, eliminationSubstitution]
    · intro a
      cases a <;>
        simp [eliminationEvaluation, eliminationSubstitution, MvPolynomial.eval₂Hom_X',
          hinv, div_eq_mul_inv]
  apply IsFractionRing.injective R (FractionRing R)
  have h := F.quotientDeterminant_elimination_evaluation u hloop (ι.comp φ) hs
  rw [hev] at h
  simpa only [RingHom.comp_apply, map_mul, map_pow] using h

end Positivity.FiniteFiberSystem
