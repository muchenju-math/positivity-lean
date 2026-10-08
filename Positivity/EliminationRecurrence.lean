import Positivity.EliminationCurryIdentity
import Positivity.EliminationCoefficientConnections

namespace Positivity
open FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The vertex-elimination coefficient recurrence of Proposition 4.4. -/
theorem eliminationCoefficientRecurrence (F : FiniteFiberSystem V E) (hF : F.Balanced)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (u : V) (hu : 0 < F.outdegree u) (hle : F.indegree u ≤ F.outdegree u) :
    balancedCoefficient F = (Nat.factorial (F.outdegree u - F.indegree u) : ℤ) *
      ∑ τ : F.Incoming u ↪ F.Outgoing u,
        balancedCoefficient (F.eliminateSystem (u := u) hloop τ) := by
  classical
  let P := F.eliminationCurryHom u hloop F.quotientDeterminant
  let Q := (F.eliminateSystemAllCompositions u hloop).quotientDeterminant
  let K := FractionRing (MvPolynomial (F.Outgoing u) ℤ)
  let ι := algebraMap (MvPolynomial (F.Outgoing u) ℤ) K
  have hcard : Fintype.card (F.Incoming u) ≤ Fintype.card (F.Outgoing u) := by
    simpa only [F.card_incoming, F.card_outgoing] using hle
  have hpos : 0 < Fintype.card (F.Outgoing u) := by rwa [F.card_outgoing]
  obtain ⟨b⟩ := Fintype.card_pos_iff.mp hpos
  have hs : (∑ b : F.Outgoing u, (MvPolynomial.X b : MvPolynomial (F.Outgoing u) ℤ)) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : MvPolynomial (F.Outgoing u) ℤ => p.coeff (Finsupp.single b 1)) h
    simp [MvPolynomial.coeff_X, Finsupp.single_left_inj] at hc
  have hs' : ι (∑ b : F.Outgoing u, MvPolynomial.X b) ≠ 0 := by
    intro h
    apply hs
    exact IsFractionRing.injective _ K (h.trans (map_zero ι).symm)
  have hidentity := F.eliminationCurry_identity u hloop ι hs'
  rw [← hF u, ← F.card_outgoing u] at hidentity
  have h := elimination_coefficient_algebra P Q hcard hs hidentity
  rw [F.coeff_eliminationCurry u hloop, F.card_outgoing, F.card_incoming] at h
  simpa only [Q, F.coeff_auxiliary_selected] using h

end Positivity
