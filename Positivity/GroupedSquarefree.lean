import Positivity.SquarefreeCompletion

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]

theorem mapDomain_fst_apply (m : A × B →₀ ℕ) (a : A) :
    m.mapDomain Prod.fst a = ∑ b : B, m (a, b) := by
  classical
  rw [Finsupp.mapDomain_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type, Finsupp.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa
    simp [hxa]
  · simp

theorem pair_choiceExponent_apply (τ : A → B) (a : A) (b : B) :
    choiceExponent (fun a => (a, τ a)) (a, b) = if τ a = b then 1 else 0 := by
  classical
  simp only [choiceExponent, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Prod.mk.injEq]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa
    simp [hxa]
  · simp

/-- A monomial with incoming degree one at every label chooses exactly one
outgoing label for each incoming label. -/
theorem exists_choice_of_mapDomain_fst (m : A × B →₀ ℕ)
    (hm : m.mapDomain Prod.fst = squarefreeExponent) :
    ∃ τ : A → B, m = choiceExponent (fun a => (a, τ a)) := by
  classical
  have hrow (a : A) : ∃ b : B,
      (Finsupp.equivFunOnFinite.symm (fun b => m (a, b))) = Finsupp.single b 1 := by
    apply (Finsupp.sum_eq_one_iff _).mp
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ b : B, m (a, b)) = 1
    rw [← mapDomain_fst_apply, hm]
    rfl
  choose τ hτ using hrow
  refine ⟨τ, ?_⟩
  ext ⟨a, b⟩
  have h := congrArg (fun d : B →₀ ℕ => d b) (hτ a)
  simpa [pair_choiceExponent_apply, Finsupp.single_apply] using h

theorem mapDomain_fst_pair_choice (τ : A → B) :
    (choiceExponent (fun a => (a, τ a))).mapDomain Prod.fst = squarefreeExponent := by
  classical
  ext a
  rw [mapDomain_fst_apply]
  simp [pair_choiceExponent_apply, squarefreeExponent]

theorem pair_choiceExponent_injective :
    Function.Injective (fun τ : A → B => choiceExponent (fun a => (a, τ a))) := by
  classical
  intro τ σ h
  funext a
  have he := congrArg (fun d : A × B →₀ ℕ => d (a, τ a)) h
  simp only [pair_choiceExponent_apply, ite_true] at he
  by_contra hn
  simp [Ne.symm hn] at he

noncomputable def groupedEvaluation (w : A × B → R) :
    MvPolynomial (A × B) R →+* MvPolynomial A R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun ab => MvPolynomial.C (w ab) * MvPolynomial.X ab.1)

theorem groupedEvaluation_monomial (w : A × B → R) (d : A × B →₀ ℕ) (c : R) :
    groupedEvaluation w (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (d.mapDomain Prod.fst)
        (c * ∏ ab : A × B, w ab ^ d ab) := by
  classical
  have hX : (∏ ab : A × B, (MvPolynomial.X ab.1 : MvPolynomial A R) ^ d ab) =
      MvPolynomial.monomial (d.mapDomain Prod.fst) 1 := by
    have h := congrArg (MvPolynomial.rename (R := R) Prod.fst)
      (MvPolynomial.monomial_eq (s := d) (a := (1 : R)))
    simp only [map_one, one_mul, MvPolynomial.rename_monomial] at h
    rw [Finsupp.prod_fintype _ _ (by simp)] at h
    simpa only [map_prod, map_pow, MvPolynomial.rename_X] using h.symm
  simp only [groupedEvaluation, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [hX, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]

theorem choice_weight_prod (w : A × B → R) (τ : A → B) :
    (∏ ab : A × B, w ab ^ choiceExponent (fun a => (a, τ a)) ab) =
      ∏ a : A, w (a, τ a) := by
  classical
  simp only [Fintype.prod_prod_type, pair_choiceExponent_apply]
  apply Finset.prod_congr rfl
  intro a _
  rw [Finset.prod_eq_single (τ a)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Squarefree incoming extraction is a sum over all choices of one
outgoing label per incoming label. -/
theorem coeff_groupedEvaluation_squarefree (w : A × B → R)
    (P : MvPolynomial (A × B) R) :
    (groupedEvaluation w P).coeff squarefreeExponent =
      ∑ τ : A → B, P.coeff (choiceExponent (fun a => (a, τ a))) * ∏ a, w (a, τ a) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  simp only [map_sum, groupedEvaluation_monomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  symm
  apply Finset.sum_bij_ne_zero (fun τ _ _ => choiceExponent (fun a => (a, τ a)))
  · intro τ _ hτ
    apply MvPolynomial.mem_support_iff.mpr
    intro hc
    simp [hc] at hτ
  · intro τ σ _ _ _ _ h
    exact pair_choiceExponent_injective h
  · intro d hd hne
    have hm : d.mapDomain Prod.fst = squarefreeExponent := by
      by_contra hn
      simp [hn] at hne
    obtain ⟨τ, rfl⟩ := exists_choice_of_mapDomain_fst d hm
    refine ⟨τ, Finset.mem_univ _, ?_, rfl⟩
    simpa [mapDomain_fst_pair_choice, choice_weight_prod] using hne
  · intro τ _ _
    simp [mapDomain_fst_pair_choice, choice_weight_prod]

end Positivity
