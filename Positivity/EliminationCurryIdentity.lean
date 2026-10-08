import Positivity.EliminationCurry
import Positivity.EliminationCoefficientAlgebra

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local instance] Classical.propDecidable
variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Field K]

theorem eliminationCurry_identity (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (ι : MvPolynomial (F.Outgoing u) ℤ →+* K)
    (hs : ι (∑ b : F.Outgoing u, MvPolynomial.X b) ≠ 0) :
    MvPolynomial.map ι (F.eliminationCurryHom u hloop F.quotientDeterminant) =
      (MvPolynomial.C ((ι (∑ b : F.Outgoing u, MvPolynomial.X b)) ^ F.fiberDimension u) :
        MvPolynomial (F.Away u ⊕ F.Incoming u) K) *
      weightedRename (Sum.map (id : F.Away u → F.Away u) (Prod.fst : F.Incoming u × F.Outgoing u → F.Incoming u))
        (Sum.elim (fun _ : F.Away u => 1)
          (fun ab : F.Incoming u × F.Outgoing u => ι (MvPolynomial.X ab.2) /
            ι (∑ b : F.Outgoing u, MvPolynomial.X b)))
        (MvPolynomial.map (Int.castRingHom K) (F.eliminateSystemAllCompositions u hloop).quotientDeterminant) := by
  classical
  let s := ι (∑ b : F.Outgoing u, MvPolynomial.X b)
  let φ : MvPolynomial E ℤ →+* MvPolynomial (F.Away u ⊕ F.Incoming u) K :=
    (MvPolynomial.map ι).comp (F.eliminationCurryHom u hloop)
  have hs' : s ≠ 0 := hs
  have haway (a : F.Away u) : φ (MvPolynomial.X a.val) = MvPolynomial.X (Sum.inl a) := by
    simp [φ, eliminationCurryHom_X_away]
  have hin (a : F.Incoming u) : φ (MvPolynomial.X a.val) = MvPolynomial.X (Sum.inr a) := by
    simp [φ, eliminationCurryHom_X_incoming]
  have hout (b : F.Outgoing u) : φ (MvPolynomial.X b.val) = MvPolynomial.C (ι (MvPolynomial.X b)) := by
    simp [φ, eliminationCurryHom_X_outgoing]
  have hsum : φ (F.outgoingWeightSum u) = MvPolynomial.C s := by
    simp only [φ, RingHom.comp_apply, eliminationCurryHom_outgoingWeightSum, MvPolynomial.map_C]
    rfl
  have hr : φ (F.outgoingWeightSum u) * MvPolynomial.C s⁻¹ = 1 := by
    rw [hsum, ← map_mul, mul_inv_cancel₀ hs', map_one]
  have hev : F.eliminationSubstitution u φ (MvPolynomial.C s⁻¹) =
      (weightedRename (Sum.map id Prod.fst)
        (Sum.elim (fun _ : F.Away u => 1)
          (fun ab : F.Incoming u × F.Outgoing u => ι (MvPolynomial.X ab.2) / s))).comp
        (MvPolynomial.map (Int.castRingHom K)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [eliminationSubstitution, weightedRename]
    · intro a
      cases a with
      | inl a => simp [eliminationSubstitution, weightedRename, MvPolynomial.eval₂Hom_X', haway]
      | inr ab =>
        simp only [eliminationSubstitution, weightedRename, RingHom.comp_apply,
          MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', Sum.elim_inr, Sum.map_inr, hin, hout]
        rw [div_eq_mul_inv, map_mul]
        ring
  have h := F.quotientDeterminant_elimination_substitution u hloop φ (MvPolynomial.C s⁻¹) hr
  rw [hsum, hev, ← map_pow] at h
  exact h

end Positivity.FiniteFiberSystem
