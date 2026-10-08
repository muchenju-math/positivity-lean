import Positivity.SumGroupedSquarefree
import Positivity.EliminationLocalization

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {C A B R : Type*} [Fintype C] [Fintype A] [Fintype B] [CommSemiring R]

theorem monomial_choiceExponent (τ : A → B) :
    (MvPolynomial.monomial (choiceExponent τ) (1 : R)) = ∏ a, MvPolynomial.X (τ a) := by
  classical
  rw [choiceExponent, MvPolynomial.monomial_sum_one]
  rfl

theorem sum_ite_injective (f : (A → B) → R) :
    (∑ τ : A → B, if Function.Injective τ then f τ else 0) =
      ∑ τ : A ↪ B, f τ := by
  classical
  symm
  apply Finset.sum_bij_ne_zero (fun (τ : A ↪ B) _ _ => (τ : A → B))
  · intros; exact Finset.mem_univ _
  · intro τ σ _ _ _ _ h
    exact DFunLike.coe_injective h
  · intro τ _ hτ
    have hinj : Function.Injective τ := by
      by_contra hn
      simp [hn] at hτ
    exact ⟨⟨τ, hinj⟩, Finset.mem_univ _, by simpa [hinj] using hτ, rfl⟩
  · intro τ _ _
    simp [τ.injective]

/-- Algebraic coefficient extraction for the vertex-elimination identity.
The outgoing variables are localized only temporarily; the extracted
incoming coefficient descends back to an ordinary polynomial. -/
theorem elimination_coefficient_algebra
    (P : MvPolynomial (C ⊕ A) (MvPolynomial B ℤ))
    (Q : MvPolynomial (C ⊕ (A × B)) ℤ)
    (hcard : Fintype.card A ≤ Fintype.card B)
    (hs : (∑ b : B, (MvPolynomial.X b : MvPolynomial B ℤ)) ≠ 0)
    (hP :
      P.map (algebraMap (MvPolynomial B ℤ) (FractionRing (MvPolynomial B ℤ))) =
      MvPolynomial.C
        ((algebraMap (MvPolynomial B ℤ) (FractionRing (MvPolynomial B ℤ)))
          (∑ b : B, MvPolynomial.X b) ^ Fintype.card B) *
      weightedRename (Sum.map id Prod.fst)
        (Sum.elim (fun _ : C => 1)
          (fun ab : A × B =>
            (algebraMap (MvPolynomial B ℤ) (FractionRing (MvPolynomial B ℤ)))
              (MvPolynomial.X ab.2) /
            (algebraMap (MvPolynomial B ℤ) (FractionRing (MvPolynomial B ℤ)))
              (∑ b : B, MvPolynomial.X b)))
        (Q.map (Int.castRingHom (FractionRing (MvPolynomial B ℤ))))) :
    (P.coeff squarefreeExponent).coeff squarefreeExponent =
      (Nat.factorial (Fintype.card B - Fintype.card A) : ℤ) *
        ∑ τ : A ↪ B, Q.coeff (selectedExponent τ) := by
  classical
  let ι := algebraMap (MvPolynomial B ℤ) (FractionRing (MvPolynomial B ℤ))
  let s : MvPolynomial B ℤ := ∑ b : B, MvPolynomial.X b
  have hinj := IsFractionRing.injective (MvPolynomial B ℤ) (FractionRing (MvPolynomial B ℤ))
  have hs' : ι s ≠ 0 := by
    intro h
    apply hs
    exact hinj (h.trans (map_zero ι).symm)
  have hc := congrArg (fun p => p.coeff (squarefreeExponent (E := C ⊕ A))) hP
  rw [MvPolynomial.coeff_map] at hc
  erw [coeff_sumGrouped_division (Int.castRingHom (FractionRing (MvPolynomial B ℤ)))
    (fun b => ι (MvPolynomial.X b)) (ι s) hs' (Fintype.card B) hcard Q] at hc
  let T (τ : A → B) : MvPolynomial B ℤ :=
    MvPolynomial.C (Q.coeff (selectedExponent τ)) *
      (MvPolynomial.monomial (choiceExponent τ) 1 * s ^ (Fintype.card B - Fintype.card A))
  have hpoly : P.coeff squarefreeExponent = ∑ τ : A → B, T τ := by
    apply hinj
    rw [map_sum]
    rw [hc]
    apply Finset.sum_congr rfl
    intro τ _
    simp only [T, monomial_choiceExponent, map_mul, map_prod, map_pow]
    have hC (z : ℤ) : ι (MvPolynomial.C z) = (z : FractionRing (MvPolynomial B ℤ)) := by
      simpa using map_intCast (ι.comp MvPolynomial.C) z
    rw [hC]
    change (ι s) ^ _ * (Q.coeff (selectedExponent τ) : FractionRing (MvPolynomial B ℤ)) *
      (∏ a, ι (MvPolynomial.X (τ a))) = _
    ring
  rw [hpoly, MvPolynomial.coeff_sum]
  have hterm (τ : A → B) : (T τ).coeff squarefreeExponent =
      (Nat.factorial (Fintype.card B - Fintype.card A) : ℤ) *
        (if Function.Injective τ then Q.coeff (selectedExponent τ) else 0) := by
    dsimp only [T]
    rw [MvPolynomial.coeff_C_mul, coeff_choice_completion]
    split_ifs <;> ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_ite_injective]

end Positivity
