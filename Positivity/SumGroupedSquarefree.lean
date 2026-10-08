import Positivity.GroupedSquarefree

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {S T C A B R : Type*} [Fintype S] [Fintype T]
    [Fintype C] [Fintype A] [Fintype B] [CommSemiring R]

noncomputable def weightedRename (π : S → T) (w : S → R) :
    MvPolynomial S R →+* MvPolynomial T R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun x => MvPolynomial.C (w x) * MvPolynomial.X (π x))

theorem weightedRename_monomial (π : S → T) (w : S → R) (d : S →₀ ℕ) (c : R) :
    weightedRename π w (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (d.mapDomain π) (c * ∏ x, w x ^ d x) := by
  classical
  have hX : (∏ x : S, (MvPolynomial.X (π x) : MvPolynomial T R) ^ d x) =
      MvPolynomial.monomial (d.mapDomain π) 1 := by
    have h := congrArg (MvPolynomial.rename (R := R) π)
      (MvPolynomial.monomial_eq (s := d) (a := (1 : R)))
    simp only [map_one, one_mul, MvPolynomial.rename_monomial] at h
    rw [Finsupp.prod_fintype _ _ (by simp)] at h
    simpa only [map_prod, map_pow, MvPolynomial.rename_X] using h.symm
  simp only [weightedRename, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [hX, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]

noncomputable def selectedExponent (τ : A → B) : C ⊕ (A × B) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (Sum.elim (fun _ => 1) (fun ab => if τ ab.1 = ab.2 then 1 else 0))

theorem selectedExponent_inl (τ : A → B) (c : C) : selectedExponent τ (Sum.inl c) = 1 := rfl
theorem selectedExponent_inr (τ : A → B) (a : A) (b : B) :
    selectedExponent (C := C) τ (Sum.inr (a, b)) = if τ a = b then 1 else 0 := rfl

theorem mapDomain_sum_fst_inl (m : C ⊕ (A × B) →₀ ℕ) (c : C) :
    m.mapDomain (Sum.map id Prod.fst) (Sum.inl c) = m (Sum.inl c) := by
  classical
  rw [Finsupp.mapDomain_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_sum_type, Finsupp.single_apply]

theorem mapDomain_sum_fst_inr (m : C ⊕ (A × B) →₀ ℕ) (a : A) :
    m.mapDomain (Sum.map id Prod.fst) (Sum.inr a) = ∑ b, m (Sum.inr (a, b)) := by
  classical
  rw [Finsupp.mapDomain_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Finsupp.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa
    simp [hxa]
  · simp

theorem mapDomain_selectedExponent (τ : A → B) :
    (selectedExponent (C := C) τ).mapDomain (Sum.map id Prod.fst) = squarefreeExponent := by
  classical
  ext x
  cases x with
  | inl c => rw [mapDomain_sum_fst_inl]; rfl
  | inr a =>
    rw [mapDomain_sum_fst_inr]
    simp [selectedExponent_inr, squarefreeExponent]

theorem exists_selectedExponent (m : C ⊕ (A × B) →₀ ℕ)
    (hm : m.mapDomain (Sum.map id Prod.fst) = squarefreeExponent) :
    ∃ τ : A → B, m = selectedExponent τ := by
  classical
  let d : A × B →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun ab => m (Sum.inr ab))
  have hd : d.mapDomain Prod.fst = squarefreeExponent := by
    ext a
    rw [mapDomain_fst_apply]
    change (∑ b, m (Sum.inr (a, b))) = 1
    rw [← mapDomain_sum_fst_inr, hm]
    rfl
  obtain ⟨τ, hτ⟩ := exists_choice_of_mapDomain_fst d hd
  refine ⟨τ, ?_⟩
  ext x
  cases x with
  | inl c =>
    have h := congrArg (fun z : C ⊕ A →₀ ℕ => z (Sum.inl c)) hm
    simpa [mapDomain_sum_fst_inl, squarefreeExponent, selectedExponent] using h
  | inr ab =>
    rcases ab with ⟨a, b⟩
    have h := congrArg (fun z : A × B →₀ ℕ => z (a, b)) hτ
    change m (Sum.inr (a, b)) = choiceExponent (fun a => (a, τ a)) (a, b) at h
    simpa only [pair_choiceExponent_apply, selectedExponent_inr] using h

theorem selectedExponent_injective :
    Function.Injective (selectedExponent (C := C) (A := A) (B := B)) := by
  classical
  intro τ σ h
  funext a
  have he := congrArg (fun d : C ⊕ (A × B) →₀ ℕ => d (Sum.inr (a, τ a))) h
  simp only [selectedExponent_inr, ite_true] at he
  by_contra hn
  simp [Ne.symm hn] at he

theorem selected_weight_prod (w : A × B → R) (τ : A → B) :
    (∏ x : C ⊕ (A × B), (Sum.elim (fun _ => (1 : R)) w x) ^ selectedExponent τ x) =
      ∏ a, w (a, τ a) := by
  classical
  simp only [Fintype.prod_sum_type, Sum.elim_inl, one_pow, Finset.prod_const_one,
    one_mul, Sum.elim_inr]
  change (∏ ab : A × B, w ab ^ (if τ ab.1 = ab.2 then 1 else 0)) = _
  rw [← choice_weight_prod w τ]
  apply Finset.prod_congr rfl
  rintro ⟨a, b⟩ _
  rw [pair_choiceExponent_apply]

theorem coeff_sumGrouped_squarefree (w : A × B → R)
    (P : MvPolynomial (C ⊕ (A × B)) R) :
    (weightedRename (Sum.map id Prod.fst) (Sum.elim (fun _ : C => 1) w) P).coeff
      squarefreeExponent =
      ∑ τ : A → B, P.coeff (selectedExponent τ) * ∏ a, w (a, τ a) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  simp only [map_sum, weightedRename_monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  symm
  apply Finset.sum_bij_ne_zero (fun τ _ _ => selectedExponent τ)
  · intro τ _ hτ
    apply MvPolynomial.mem_support_iff.mpr
    intro hc
    simp [hc] at hτ
  · intro τ σ _ _ _ _ h
    exact selectedExponent_injective h
  · intro d hd hne
    have hm : d.mapDomain (Sum.map id Prod.fst) = squarefreeExponent := by
      by_contra hn
      simp [hn] at hne
    obtain ⟨τ, rfl⟩ := exists_selectedExponent d hm
    refine ⟨τ, Finset.mem_univ _, ?_, rfl⟩
    simpa only [mapDomain_selectedExponent, ite_true, selected_weight_prod] using hne
  · intro τ _ _
    simp only [mapDomain_selectedExponent, ite_true, selected_weight_prod]

theorem coeff_sumGrouped_division {K : Type*} [Field K] (f : R →+* K) (w : B → K)
    (s : K) (hs : s ≠ 0) (d : ℕ) (hd : Fintype.card A ≤ d)
    (P : MvPolynomial (C ⊕ (A × B)) R) :
    (MvPolynomial.C (s ^ d) * weightedRename (Sum.map id Prod.fst)
      (Sum.elim (fun _ : C => 1) (fun ab : A × B => w ab.2 / s)) (P.map f)).coeff
        squarefreeExponent =
    ∑ τ : A → B, s ^ (d - Fintype.card A) *
      f (P.coeff (selectedExponent τ)) * ∏ a, w (τ a) := by
  classical
  rw [MvPolynomial.coeff_C_mul, coeff_sumGrouped_squarefree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [MvPolynomial.coeff_map, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hp : s ^ d = s ^ (d - Fintype.card A) * s ^ Fintype.card A := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  rw [hp]
  field_simp

end Positivity
