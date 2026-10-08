import Positivity.LoopContraction
import Positivity.VertexElimination

/-!
# Positivity theorem

Formalization of Section 5: induction on the quotient dimension, followed by
polarization and the covering-graph application.
-/

namespace Positivity

open FiniteFiberSystem

universe uV uE uF

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The exponent vector of the squarefree monomial using every base edge
once. -/
noncomputable def squarefreeExponent : E →₀ ℕ:=
  Finsupp.equivFunOnFinite.symm (fun _ : E => 1)

/-- The finitely supported exponent represented by a function on a finite
edge type. -/
noncomputable def exponentOfFunction (α : E →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm α

@[simp] theorem exponentOfFunction_apply (α : E →₀ ℕ) (e : E) :
    exponentOfFunction α e = α e := by
  simp [exponentOfFunction]

/-- The exponent vector using each edge except `e` exactly once. -/
noncomputable def squarefreeExponentExcept (e : E) : E →₀ ℕ:=
  by
    classical
    exact Finsupp.equivFunOnFinite.symm (fun f : E => if f = e then 0 else 1)

theorem squarefreeExponentExcept_add_single (e : E) :
    squarefreeExponentExcept e + Finsupp.single e 1 = squarefreeExponent := by
  classical
  apply Finsupp.equivFunOnFinite.injective
  ext f
  by_cases hf : f = e
  · subst f
    simp [squarefreeExponentExcept, squarefreeExponent]
  · simp [squarefreeExponentExcept, squarefreeExponent, hf]

/-- The coefficient of the squarefree monomial in the top power of the
sum of all variables is the factorial counting their orderings. -/
theorem coeff_sum_X_pow_squarefree {R : Type*} [CommSemiring R] :
    ((∑e : E, (MvPolynomial.X e : MvPolynomial E R)) ^ Fintype.card E).coeff
      (squarefreeExponent (E := E)) = (Nat.factorial (Fintype.card E) : R) := by
  classical
  let d := squarefreeExponent (E := E)
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype]
  have hsum :
      d.sum (fun _ n => n) = Fintype.card E := by
    rw [d.sum_fintype (fun _ n => n) (by simp)]
    simp [d, squarefreeExponent]
  have hprod : d.prod (fun _ n => n.factorial) = 1 := by
    rw [d.prod_fintype (fun _ n => n.factorial) (by simp)]
    simp [d, squarefreeExponent]
  have hfactorial : d.multinomial = Nat.factorial (Fintype.card E) := by
    rw [Finsupp.multinomial]
    change Nat.factorial (d.sum (fun _ n => n)) /
      d.prod (fun _ n => n.factorial) = Nat.factorial (Fintype.card E)
    rw [hsum, hprod]
    simp
  rw [if_pos hsum]
  simpa [d] using congrArg (fun n : ℕ=> (n : R)) hfactorial

/-- A squarefree coefficient in a power of a sum vanishes unless the power
equals the number of variables. -/
theorem coeff_sum_X_pow_squarefree_general (n m : ℕ) :
    ((∑t : Fin n, (MvPolynomial.X t : MvPolynomial (Fin n) ℤ)) ^ m).coeff
      (squarefreeExponent (E := Fin n)) =
        if m = n then (Nat.factorial n : ℤ) else 0 := by
  classical
  by_cases hm : m = n
  · subst m
    simpa [Fintype.card_fin] using
      (coeff_sum_X_pow_squarefree (E := Fin n) (R := ℤ))
  · rw [MvPolynomial.coeff_sum_X_pow_of_fintype]
    have hsum :
        (squarefreeExponent (E := Fin n)).sum (fun _ k => k) = n := by
      rw [Finsupp.sum_fintype (squarefreeExponent (E := Fin n)) (fun _ k => k) (by simp)]
      simp [squarefreeExponent]
    have hne :
        (squarefreeExponent (E := Fin n)).sum (fun _ k => k) ≠ m := by
      omega
    rw [if_neg hne]
    simp [hm]
/-- The labelled copies of a single edge are the variables of a sum whose
top squarefree coefficient is the factorial of the number of copies. -/
theorem coeff_polarizedVariableSum_pow_squarefree
    (α : E →₀ ℕ) (e : E) (ι : Fin (α e) ↪ PolarizedEdge α)
    (hι : ∀ t, ι t = ⟨e, t⟩) :
    (polarizedVariableSum α e ^ α e).coeff
      ((squarefreeExponent (E := Fin (α e))).embDomain ι) = Nat.factorial (α e) := by
  classical
  have hrename :
      MvPolynomial.rename ι (∑t : Fin (α e), MvPolynomial.X t) =
        polarizedVariableSum α e := by
    simp [polarizedVariableSum, hι]
  rw [←hrename, ←map_pow]
  rw [MvPolynomial.coeff_rename_embDomain]
  simpa [Fintype.card_fin] using coeff_sum_X_pow_squarefree (E := Fin (α e)) (R := ℤ)
/-- Exact coefficient extraction for a single polarized edge group: the
squarefree coefficient vanishes unless the input power matches the group size. -/
theorem coeff_polarizedVariableSum_pow
    (α : E →₀ ℕ) (e : E) (ι : Fin (α e) ↪ PolarizedEdge α)
    (hι : ∀ t, ι t = ⟨e, t⟩) (m : ℕ) :
    (polarizedVariableSum α e ^ m).coeff
      ((squarefreeExponent (E := Fin (α e))).embDomain ι) =
      if m = α e then (Nat.factorial (α e) : ℤ) else 0 := by
  classical
  let d := squarefreeExponent (E := Fin (α e))
  have hsum : d.sum (fun _ n => n) = α e := by
    rw [d.sum_fintype (fun _ n => n) (by simp)]
    simp [d, squarefreeExponent]
  have hrename :
      MvPolynomial.rename ι (∑t : Fin (α e), MvPolynomial.X t) =
        polarizedVariableSum α e := by
    simp [polarizedVariableSum, hι]
  have htop := coeff_polarizedVariableSum_pow_squarefree α e ι hι
  have hmulti : (d.multinomial : ℤ) = (Nat.factorial (α e) : ℤ) := by
    rw [←hrename, ←map_pow] at htop
    rw [MvPolynomial.coeff_rename_embDomain,
      MvPolynomial.coeff_sum_X_pow_of_fintype, if_pos hsum] at htop
    simpa [d] using htop
  rw [←hrename, ←map_pow, MvPolynomial.coeff_rename_embDomain,
    MvPolynomial.coeff_sum_X_pow_of_fintype]
  have hsum' : (squarefreeExponent (E := Fin (α e))).sum (fun _ n => n) = α e :=
    by simpa [d] using hsum
  by_cases hm : m = α e
  · subst m
    rw [if_pos hsum']
    simpa [d] using hmulti
  · have hne : (squarefreeExponent (E := Fin (α e))).sum (fun _ n => n) ≠ m := by omega
    rw [if_neg hne]
    simp [hm]
/-- The local edge group extraction formula, stated directly for the
polarization homomorphism on a power of one source variable. -/
theorem coeff_polarizationHom_X_pow
    (α : E →₀ ℕ) (e : E) (ι : Fin (α e) ↪ PolarizedEdge α)
    (hι : ∀ t, ι t = ⟨e, t⟩) (m : ℕ) :
    (polarizationHom α (MvPolynomial.X e ^ m)).coeff
      ((squarefreeExponent (E := Fin (α e))).embDomain ι) =
      if m = α e then (Nat.factorial (α e) : ℤ) else 0 := by
  simpa only [map_pow, polarizationHom_X] using
    coeff_polarizedVariableSum_pow α e ι hι m

/-- The labelled copies belonging to one base edge embed into the full
polarized edge type. -/
def polarizedEdgeEmbedding (α : E →₀ ℕ) (e : E) :
    Fin (α e) ↪ PolarizedEdge α where
  toFun t := ⟨e, t⟩
  inj' := by
    intro i j h
    cases h
    rfl

/-- The two disjoint edge-copy groups embed as a sum of variable types. -/
def polarizedPairEmbedding (α : E →₀ ℕ) (e f : E)
    (hdisj : Disjoint (Set.range (polarizedEdgeEmbedding α e))
      (Set.range (polarizedEdgeEmbedding α f))) :
    Fin (α e) ⊕ Fin (α f) ↪ PolarizedEdge α :=
  sumEmbeddingOfDisjoint (polarizedEdgeEmbedding α e) (polarizedEdgeEmbedding α f) hdisj

/-- The squarefree coefficient factors for two distinct polarized edge
groups. -/
theorem coeff_twoPolarizedEdgeGroups (α : E →₀ ℕ) (e f : E)
    (hdisj : Disjoint (Set.range (polarizedEdgeEmbedding α e))
      (Set.range (polarizedEdgeEmbedding α f))) :
    ((polarizedVariableSum α e ^ α e) *
      (polarizedVariableSum α f ^ α f)).coeff
      (((squarefreeExponent (E := Fin (α e))).sumElim
        (squarefreeExponent (E := Fin (α f)))).embDomain
        (sumEmbeddingOfDisjoint (polarizedEdgeEmbedding α e)
          (polarizedEdgeEmbedding α f) hdisj)) =
      (Nat.factorial (α e) : ℤ) * (Nat.factorial (α f) : ℤ) := by
  classical
  have hren (g : E) :
      MvPolynomial.rename (polarizedEdgeEmbedding α g)
          (∑t : Fin (α g), MvPolynomial.X t) = polarizedVariableSum α g := by
    classical
    rw [map_sum]
    unfold polarizedVariableSum
    apply Finset.sum_congr rfl
    intro t ht
    rw [MvPolynomial.rename_X]
    congr 1
  let baseE : MvPolynomial (Fin (α e)) ℤ:=
    ∑t : Fin (α e), MvPolynomial.X t
  let baseF : MvPolynomial (Fin (α f)) ℤ:=
    ∑t : Fin (α f), MvPolynomial.X t
  have hpowE : polarizedVariableSum α e ^ α e =
      MvPolynomial.rename (polarizedEdgeEmbedding α e)
        (baseE ^ α e) := by
    rw [←hren e, ←map_pow]
  have hpowF : polarizedVariableSum α f ^ α f =
      MvPolynomial.rename (polarizedEdgeEmbedding α f)
        (baseF ^ α f) := by
    rw [←hren f, ←map_pow]
  have hfactor := coeff_mul_rename_disjoint (R := ℤ)
    (polarizedEdgeEmbedding α e) (polarizedEdgeEmbedding α f) hdisj
    (baseE ^ α e)
    (baseF ^ α f)
    (squarefreeExponent (E := Fin (α e)))
    (squarefreeExponent (E := Fin (α f)))
  have htarget :
      (MvPolynomial.rename (polarizedEdgeEmbedding α e)
          (baseE ^ α e) *
        MvPolynomial.rename (polarizedEdgeEmbedding α f)
          (baseF ^ α f)).coeff
        (((squarefreeExponent (E := Fin (α e))).sumElim
          (squarefreeExponent (E := Fin (α f)))).embDomain
          (sumEmbeddingOfDisjoint (polarizedEdgeEmbedding α e)
            (polarizedEdgeEmbedding α f) hdisj)) =
        (baseE ^ α e).coeff
            (squarefreeExponent (E := Fin (α e))) *
          (baseF ^ α f).coeff
            (squarefreeExponent (E := Fin (α f))) := by
    exact hfactor
  have hcoeffE :
      (baseE ^ α e).coeff
        (squarefreeExponent (E := Fin (α e))) = (Nat.factorial (α e) : ℤ) := by
    simpa [Fintype.card_fin] using coeff_sum_X_pow_squarefree (E := Fin (α e)) (R := ℤ)
  have hcoeffF :
      (baseF ^ α f).coeff
        (squarefreeExponent (E := Fin (α f))) = (Nat.factorial (α f) : ℤ) := by
    simpa using coeff_sum_X_pow_squarefree (E := Fin (α f)) (R := ℤ)
  calc
    ((polarizedVariableSum α e ^ α e) *
      (polarizedVariableSum α f ^ α f)).coeff
        (((squarefreeExponent (E := Fin (α e))).sumElim
          (squarefreeExponent (E := Fin (α f)))).embDomain
          (sumEmbeddingOfDisjoint (polarizedEdgeEmbedding α e)
            (polarizedEdgeEmbedding α f) hdisj)) =
        (MvPolynomial.rename (polarizedEdgeEmbedding α e)
            (baseE ^ α e) *
          MvPolynomial.rename (polarizedEdgeEmbedding α f)
            (baseF ^ α f)).coeff
          (((squarefreeExponent (E := Fin (α e))).sumElim
            (squarefreeExponent (E := Fin (α f)))).embDomain
            (sumEmbeddingOfDisjoint (polarizedEdgeEmbedding α e)
              (polarizedEdgeEmbedding α f) hdisj)) := by
      rw [hpowE, hpowF]
    _ = (baseE ^ α e).coeff
          (squarefreeExponent (E := Fin (α e))) *
        (baseF ^ α f).coeff
          (squarefreeExponent (E := Fin (α f))) := htarget
    _ = (Nat.factorial (α e) : ℤ) * (Nat.factorial (α f) : ℤ) := by
      rw [hcoeffE, hcoeffF]

/-- Distinct base-edge labels give disjoint labelled-copy groups. -/
theorem polarizedEdgeGroups_disjoint_of_ne (α : E →₀ ℕ) {e f : E} (hef : e ≠ f) :
    Disjoint (Set.range (polarizedEdgeEmbedding α e))
      (Set.range (polarizedEdgeEmbedding α f)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rcases hz with ⟨i, rfl⟩
  rcases hz' with ⟨j, hj⟩
  have hfe : f = e := congrArg Sigma.fst hj
  exact hef hfe.symm

/-- Two distinct base-edge groups contribute the product of their
factorials to the coefficient using every labelled copy once. -/
theorem coeff_twoPolarizedEdgeGroups_of_ne (α : E →₀ ℕ) {e f : E}
    (hef : e ≠ f) :
    ((polarizedVariableSum α e ^ α e) *
      (polarizedVariableSum α f ^ α f)).coeff
      (((squarefreeExponent (E := Fin (α e))).sumElim
        (squarefreeExponent (E := Fin (α f)))).embDomain
        (polarizedPairEmbedding α e f (polarizedEdgeGroups_disjoint_of_ne α hef))) =
      (Nat.factorial (α e) : ℤ) * (Nat.factorial (α f) : ℤ) :=
  coeff_twoPolarizedEdgeGroups α e f
    (polarizedEdgeGroups_disjoint_of_ne α hef)

/-- The variable type for a list of polarized edge groups, represented as
a nested sum. -/
abbrev PolarizedGroupVariables (α : E →₀ ℕ) : (es : List E) → Type
  | [] => Empty
  | e :: es => Fin (α e) ⊕ PolarizedGroupVariables α es

/-- Map a nested sum of polarized edge groups to the corresponding labelled
edges in the full polarized edge type. -/
def polarizedGroupVariableMap (α : E →₀ ℕ) :
    (es : List E) → PolarizedGroupVariables α es → PolarizedEdge α
  | [], x => nomatch x
  | e :: es, Sum.inl t => ⟨e, t⟩
  | e :: es, Sum.inr x => polarizedGroupVariableMap α es x

/-- Every variable in a nested sum of edge groups remembers an edge label
from the list indexing that sum. -/
theorem polarizedGroupVariableMap_fst_mem (α : E →₀ ℕ) :
    ∀ (es : List E) (x : PolarizedGroupVariables α es),
      (polarizedGroupVariableMap α es x).1 ∈ es := by
  intro es
  induction es with
  | nil => intro x; cases x
  | cons e es ih =>
      intro x
      cases x with
      | inl t => simp [polarizedGroupVariableMap]
      | inr x => exact List.mem_cons_of_mem e (ih x)

/-- Distinct edge labels make the nested group-variable map injective. -/
theorem polarizedGroupVariableMap_injective (α : E →₀ ℕ) :
    ∀ (es : List E), es.Nodup →
      Function.Injective (polarizedGroupVariableMap α es) := by
  intro es
  induction es with
  | nil =>
      intro hnd x
      cases x
  | cons e es ih =>
      intro hnd x y hxy
      have hnot : e ∉es := (List.nodup_cons.mp hnd).1
      have htail : es.Nodup := (List.nodup_cons.mp hnd).2
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              change (⟨e, x⟩ : PolarizedEdge α) = ⟨e, y⟩ at hxy
              cases hxy
              rfl
          | inr y =>
              have hfst := congrArg Sigma.fst hxy
              have hymem := polarizedGroupVariableMap_fst_mem α es y
              change e = (polarizedGroupVariableMap α es y).1 at hfst
              exact False.elim (hnot (hfst.symm ▸ hymem))
      | inr x =>
          cases y with
          | inl y =>
              have hfst := congrArg Sigma.fst hxy
              have hxmem := polarizedGroupVariableMap_fst_mem α es x
              change (polarizedGroupVariableMap α es x).1 = e at hfst
              exact False.elim (hnot (hfst.symm ▸ hxmem))
          | inr y =>
              change polarizedGroupVariableMap α es x =
                polarizedGroupVariableMap α es y at hxy
              exact congrArg Sum.inr (ih htail hxy)

/-- The exponent using every labelled variable exactly once in a nested
sum of polarized edge groups. -/
noncomputable def polarizedGroupExponent (α : E →₀ ℕ) :
    (es : List E) → PolarizedGroupVariables α es →₀ ℕ
  | [] => 0
  | e :: es =>
      (squarefreeExponent (E := Fin (α e))).sumElim
        (polarizedGroupExponent α es)

/-- The product of edge-group power sums in nested-sum variables. -/
noncomputable def polarizedGroupProduct (α : E →₀ ℕ) :
    (es : List E) → MvPolynomial (PolarizedGroupVariables α es) ℤ
  | [] => 1
  | e :: es =>
      MvPolynomial.rename Sum.inl
          ((∑t : Fin (α e), MvPolynomial.X t) ^ α e) *
        MvPolynomial.rename Sum.inr (polarizedGroupProduct α es)

/-- For any finite list of polarized edge groups, the coefficient using
every labelled variable once is the product of their factorials. -/
theorem coeff_polarizedGroupProduct (α : E →₀ ℕ) (es : List E) :
    (polarizedGroupProduct α es).coeff (polarizedGroupExponent α es) =
      (es.map fun e => (Nat.factorial (α e) : ℤ)).prod := by
  induction es with
  | nil => simp [polarizedGroupProduct, polarizedGroupExponent]
  | cons e es ih =>
      change
        (MvPolynomial.rename Sum.inl
            ((∑t : Fin (α e), MvPolynomial.X t) ^ α e) *
          MvPolynomial.rename Sum.inr (polarizedGroupProduct α es)).coeff
          ((squarefreeExponent (E := Fin (α e))).sumElim
            (polarizedGroupExponent α es)) =
          ((Nat.factorial (α e) : ℤ) * (es.map fun e => (Nat.factorial (α e) : ℤ)).prod)
      rw [coeff_mul_rename_groups]
      have hhead :
          ((∑t : Fin (α e), (MvPolynomial.X t : MvPolynomial (Fin (α e)) ℤ)) ^ α e).coeff
            (squarefreeExponent (E := Fin (α e))) = (Nat.factorial (α e) : ℤ) := by
        simpa [Fintype.card_fin] using coeff_sum_X_pow_squarefree (E := Fin (α e)) (R := ℤ)
      rw [hhead, ih]

/-- The nested product of edge-group sums with independently prescribed
power `β e` in each group. -/
noncomputable def polarizedGroupProductPower (α β : E →₀ ℕ) :
    (es : List E) → MvPolynomial (PolarizedGroupVariables α es) ℤ
  | [] => 1
  | e :: es =>
      MvPolynomial.rename Sum.inl
          ((∑t : Fin (α e), MvPolynomial.X t) ^ β e) *
        MvPolynomial.rename Sum.inr (polarizedGroupProductPower α β es)

/-- At the squarefree exponent of the groups, each group power contributes
zero unless its power matches the group size. -/
theorem coeff_polarizedGroupProductPower (α β : E →₀ ℕ) (es : List E) :
    (polarizedGroupProductPower α β es).coeff (polarizedGroupExponent α es) =
      (es.map fun e =>
        if β e = α e then (Nat.factorial (α e) : ℤ) else 0).prod := by
  induction es with
  | nil => simp [polarizedGroupProductPower, polarizedGroupExponent]
  | cons e es ih =>
      change
        (MvPolynomial.rename Sum.inl
            ((∑t : Fin (α e), MvPolynomial.X t) ^ β e) *
          MvPolynomial.rename Sum.inr (polarizedGroupProductPower α β es)).coeff
          ((squarefreeExponent (E := Fin (α e))).sumElim
            (polarizedGroupExponent α es)) = _
      rw [coeff_mul_rename_groups]
      rw [coeff_sum_X_pow_squarefree_general, ih]
      simp

/-- Regard the nested sum variables for a duplicate-free edge list as an
embedding into the actual labelled polarized edge type. -/
def polarizedGroupVariableEmbedding (α : E →₀ ℕ) (es : List E)
    (hnd : es.Nodup) : PolarizedGroupVariables α es ↪ PolarizedEdge α where
  toFun := polarizedGroupVariableMap α es
  inj' := polarizedGroupVariableMap_injective α es hnd

/-- The factorial coefficient formula for nested polarized groups remains
valid after embedding their variables into the full polarized edge type. -/
theorem coeff_rename_polarizedGroupProduct (α : E →₀ ℕ) (es : List E)
    (hnd : es.Nodup) :
    (MvPolynomial.rename (polarizedGroupVariableEmbedding α es hnd)
      (polarizedGroupProduct α es)).coeff
        ((polarizedGroupExponent α es).embDomain
          (polarizedGroupVariableEmbedding α es hnd)) =
      (es.map fun e => (Nat.factorial (α e) : ℤ)).prod := by
  rw [MvPolynomial.coeff_rename_embDomain]
  exact coeff_polarizedGroupProduct α es

/-- The product of polarized edge-group power sums in the full polarized
edge variables, with factors ordered by a list. -/
noncomputable def polarizedEdgeGroupProduct (α : E →₀ ℕ) : List E →
    MvPolynomial (PolarizedEdge α) ℤ
  | [] => 1
  | e :: es =>
      (polarizedVariableSum α e ^ α e) * polarizedEdgeGroupProduct α es

/-- The full-variable edge-group product with an independent power at each
base edge. -/
noncomputable def polarizedEdgeGroupProductPower (α β : E →₀ ℕ) : List E →
    MvPolynomial (PolarizedEdge α) ℤ
  | [] => 1
  | e :: es =>
      (polarizedVariableSum α e ^ β e) * polarizedEdgeGroupProductPower α β es

/-- Renaming the nested group product along its canonical embedding gives
the product of the corresponding power sums in the full polarized edge
variables. -/
theorem rename_polarizedGroupProduct (α : E →₀ ℕ) :
    ∀ (es : List E) (hnd : es.Nodup),
      MvPolynomial.rename (polarizedGroupVariableEmbedding α es hnd)
        (polarizedGroupProduct α es) = polarizedEdgeGroupProduct α es := by
  intro es
  induction es with
  | nil => intro hnd; simp [polarizedGroupProduct, polarizedEdgeGroupProduct]
  | cons e es ih =>
      intro hnd
      have htail : es.Nodup := (List.nodup_cons.mp hnd).2
      let γ := Fin (α e) ⊕ PolarizedGroupVariables α es
      let emb := polarizedGroupVariableEmbedding α (e :: es) hnd
      let head : MvPolynomial γ ℤ:=
        MvPolynomial.rename Sum.inl ((∑t : Fin (α e), MvPolynomial.X t) ^ α e)
      let tail : MvPolynomial γ ℤ:=
        MvPolynomial.rename Sum.inr (polarizedGroupProduct α es)
      change MvPolynomial.rename emb (head * tail) = _
      calc
        MvPolynomial.rename emb (head * tail) =
            MvPolynomial.rename emb head * MvPolynomial.rename emb tail :=
          (MvPolynomial.rename emb).map_mul head tail
        _ = MvPolynomial.rename
              (fun t : Fin (α e) => emb (Sum.inl t))
                ((∑t : Fin (α e), MvPolynomial.X t) ^ α e) *
            MvPolynomial.rename
                (fun t : PolarizedGroupVariables α es => emb (Sum.inr t))
                  (polarizedGroupProduct α es) := by
          rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
          rfl
      have hhead :
          (fun t : Fin (α e) =>
            emb (Sum.inl t)) =
          polarizedEdgeEmbedding α e := by
        funext t
        rfl
      have htailMap :
          (fun t : PolarizedGroupVariables α es =>
            emb (Sum.inr t)) =
          polarizedGroupVariableEmbedding α es htail := by
        funext t
        rfl
      have hsum :
          MvPolynomial.rename (polarizedEdgeEmbedding α e)
            (∑t : Fin (α e), MvPolynomial.X t) = polarizedVariableSum α e := by
        classical
        rw [map_sum]
        unfold polarizedVariableSum
        apply Finset.sum_congr rfl
        intro t ht
        rw [MvPolynomial.rename_X]
        rfl
      rw [hhead, htailMap, map_pow, hsum, ih htail]
      rfl

/-- Rename the generalized nested product to the corresponding product in
the full polarized edge variables. -/
theorem rename_polarizedGroupProductPower (α β : E →₀ ℕ) :
    ∀ (es : List E) (hnd : es.Nodup),
      MvPolynomial.rename (polarizedGroupVariableEmbedding α es hnd)
        (polarizedGroupProductPower α β es) =
          polarizedEdgeGroupProductPower α β es := by
  intro es
  induction es with
  | nil => intro hnd; simp [polarizedGroupProductPower, polarizedEdgeGroupProductPower]
  | cons e es ih =>
      intro hnd
      have htail : es.Nodup := (List.nodup_cons.mp hnd).2
      let γ := Fin (α e) ⊕ PolarizedGroupVariables α es
      let emb := polarizedGroupVariableEmbedding α (e :: es) hnd
      let head : MvPolynomial γ ℤ:=
        MvPolynomial.rename Sum.inl ((∑t : Fin (α e), MvPolynomial.X t) ^ β e)
      let tail : MvPolynomial γ ℤ:=
        MvPolynomial.rename Sum.inr (polarizedGroupProductPower α β es)
      change MvPolynomial.rename emb (head * tail) = _
      calc
        MvPolynomial.rename emb (head * tail) =
            MvPolynomial.rename emb head * MvPolynomial.rename emb tail :=
          (MvPolynomial.rename emb).map_mul head tail
        _ = MvPolynomial.rename
              (fun t : Fin (α e) => emb (Sum.inl t))
                ((∑t : Fin (α e), MvPolynomial.X t) ^ β e) *
            MvPolynomial.rename
              (fun t : PolarizedGroupVariables α es => emb (Sum.inr t))
                (polarizedGroupProductPower α β es) := by
          rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
          rfl
      have hhead :
          (fun t : Fin (α e) => emb (Sum.inl t)) = polarizedEdgeEmbedding α e := by
        funext t
        rfl
      have htailMap :
          (fun t : PolarizedGroupVariables α es => emb (Sum.inr t)) =
            polarizedGroupVariableEmbedding α es htail := by
        funext t
        rfl
      have hsum :
          MvPolynomial.rename (polarizedEdgeEmbedding α e)
            (∑t : Fin (α e), MvPolynomial.X t) = polarizedVariableSum α e := by
        classical
        rw [map_sum]
        unfold polarizedVariableSum
        apply Finset.sum_congr rfl
        intro t ht
        rw [MvPolynomial.rename_X]
        rfl
      rw [hhead, htailMap, map_pow, hsum, ih htail]
      rfl

/-- The generalized factorial filter transports to the full polarized
edge variables for any duplicate-free edge list. -/
theorem coeff_rename_polarizedGroupProductPower (α β : E →₀ ℕ)
    (es : List E) (hnd : es.Nodup) :
    (MvPolynomial.rename (polarizedGroupVariableEmbedding α es hnd)
      (polarizedGroupProductPower α β es)).coeff
        ((polarizedGroupExponent α es).embDomain
          (polarizedGroupVariableEmbedding α es hnd)) =
      (es.map fun e =>
        if β e = α e then (Nat.factorial (α e) : ℤ) else 0).prod := by
  rw [MvPolynomial.coeff_rename_embDomain]
  exact coeff_polarizedGroupProductPower α β es

/-- A labelled edge whose base label occurs in the list is in the image of
the nested group-variable map. -/
theorem polarizedGroupVariableMap_surjective_of_mem (α : E →₀ ℕ) :
    ∀ (es : List E) (e : E) (t : Fin (α e)), e ∈ es →
      ∃ x : PolarizedGroupVariables α es,
        polarizedGroupVariableMap α es x = ⟨e, t⟩ := by
  intro es
  induction es with
  | nil => intro e t h; simp at h
  | cons a es ih =>
      intro e t h
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨Sum.inl t, rfl⟩
      · obtain ⟨x, hx⟩ := ih e t h
        exact ⟨Sum.inr x, hx⟩

/-- Every variable in the nested list of polarized groups has exponent one. -/
theorem polarizedGroupExponent_apply (α : E →₀ ℕ) :
    ∀ (es : List E) (x : PolarizedGroupVariables α es),
      polarizedGroupExponent α es x = 1 := by
  intro es
  induction es with
  | nil => intro x; cases x
  | cons e es ih =>
      intro x
      cases x with
      | inl t => simp [polarizedGroupExponent, squarefreeExponent]
      | inr x => simp [polarizedGroupExponent, ih x]

/-- The factorial coefficient formula for the product over every edge,
with the squarefree exponent in the full polarized edge type. -/
theorem coeff_polarizedEdgeGroupProduct_all (α : E →₀ ℕ) :
    (polarizedEdgeGroupProduct α Finset.univ.toList).coeff
      (squarefreeExponent (E := PolarizedEdge α)) =
      ∏ e : E, (Nat.factorial (α e) : ℤ) := by
  classical
  let es : List E := Finset.univ.toList
  have hnd : es.Nodup := by
    simpa [es] using (Finset.univ : Finset E).nodup_toList
  have hcomplete : ∀ e : E, e ∈ es := by
    intro e
    simp [es]
  let emb := polarizedGroupVariableEmbedding α es hnd
  have hsurj : Function.Surjective emb := by
    intro p
    rcases p with ⟨e, t⟩
    obtain ⟨x, hx⟩ := polarizedGroupVariableMap_surjective_of_mem
      α es e t (hcomplete e)
    exact ⟨x, hx⟩
  have hexp :
      (polarizedGroupExponent α es).embDomain emb =
        squarefreeExponent (E := PolarizedEdge α) := by
    ext p
    obtain ⟨x, hx⟩ := hsurj p
    rw [←hx, Finsupp.embDomain_apply_self]
    exact polarizedGroupExponent_apply α es x
  rw [←rename_polarizedGroupProduct α es hnd, ←hexp,
    coeff_rename_polarizedGroupProduct α es hnd]
  simp [es, Finset.prod_toList]

/-- For arbitrary powers, the full-variable squarefree coefficient keeps
exactly the edge groups whose power matches their number of labels. -/
theorem coeff_polarizedEdgeGroupProductPower_all (α β : E →₀ ℕ) :
    (polarizedEdgeGroupProductPower α β Finset.univ.toList).coeff
      (squarefreeExponent (E := PolarizedEdge α)) =
      ∏ e : E,
        if β e = α e then (Nat.factorial (α e) : ℤ) else 0 := by
  classical
  let es : List E := Finset.univ.toList
  have hnd : es.Nodup := by
    simpa [es] using (Finset.univ : Finset E).nodup_toList
  have hcomplete : ∀ e : E, e ∈ es := by
    intro e
    simp [es]
  let emb := polarizedGroupVariableEmbedding α es hnd
  have hsurj : Function.Surjective emb := by
    intro p
    rcases p with ⟨e, t⟩
    obtain ⟨x, hx⟩ := polarizedGroupVariableMap_surjective_of_mem
      α es e t (hcomplete e)
    exact ⟨x, hx⟩
  have hexp :
      (polarizedGroupExponent α es).embDomain emb =
        squarefreeExponent (E := PolarizedEdge α) := by
    ext p
    obtain ⟨x, hx⟩ := hsurj p
    rw [←hx, Finsupp.embDomain_apply_self]
    exact polarizedGroupExponent_apply α es x
  rw [←rename_polarizedGroupProductPower α β es hnd, ←hexp,
    coeff_rename_polarizedGroupProductPower α β es hnd]
  simp [es]

/-- The recursive full-variable product agrees with the product over the
finite edge type. -/
theorem polarizedEdgeGroupProductPower_eq_prod (α β : E →₀ ℕ) :
    polarizedEdgeGroupProductPower α β Finset.univ.toList =
      ∏ e : E, polarizedVariableSum α e ^ β e := by
  classical
  have hlist (es : List E) :
      polarizedEdgeGroupProductPower α β es =
        (es.map fun e => polarizedVariableSum α e ^ β e).prod := by
    induction es with
    | nil => simp [polarizedEdgeGroupProductPower]
    | cons e es ih => simp [polarizedEdgeGroupProductPower, ih]
  rw [hlist]
  simp

/-- The squarefree coefficient after polarization extracts the coefficient
of the prescribed exponent vector, with the factorial multiplicity from
labelling parallel copies. -/
theorem coeff_polarizationHom_squarefree
    (α : E →₀ ℕ) (P : MvPolynomial E ℤ) :
    (polarizationHom α P).coeff (squarefreeExponent (E := PolarizedEdge α)) =
      P.coeff (exponentOfFunction α) *
        ∏ e : E, (Nat.factorial (α e) : ℤ) := by
  classical
  have hcoeff (d : E →₀ ℕ) :
      (∏ e : E, polarizedVariableSum α e ^ d e).coeff
        (squarefreeExponent (E := PolarizedEdge α)) =
        ∏ e : E, if d e = α e then (Nat.factorial (α e) : ℤ) else 0 := by
    rw [← polarizedEdgeGroupProductPower_eq_prod α d]
    simpa using coeff_polarizedEdgeGroupProductPower_all α d
  rw [coeff_polarizationHom]
  calc
    (∑ d ∈ P.support,
        P.coeff d * (∏ e : E, polarizedVariableSum α e ^ d e).coeff
          (squarefreeExponent (E := PolarizedEdge α))) =
        P.coeff (exponentOfFunction α) *
          (∏ e : E, polarizedVariableSum α e ^ (exponentOfFunction α) e).coeff
            (squarefreeExponent (E := PolarizedEdge α)) := by
      apply Finset.sum_eq_single (exponentOfFunction α)
      · intro d hd hne
        rw [hcoeff d]
        have hdiff : ∃ e : E, d e ≠ α e := by
          by_contra hsame
          push_neg at hsame
          apply hne
          ext e
          rw [exponentOfFunction_apply]
          exact hsame e
        obtain ⟨e, he⟩ := hdiff
        have hzero : (∏ e : E,
            if d e = α e then (Nat.factorial (α e) : ℤ) else 0) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ e)
          simp [he]
        rw [hzero, mul_zero]
      · intro hnot
        have hzero : P.coeff (exponentOfFunction α) = 0 := by
          by_contra hc
          exact hnot (MvPolynomial.mem_support_iff.mpr hc)
        simp [hzero]
    _ = P.coeff (exponentOfFunction α) *
        ∏ e : E, (Nat.factorial (α e) : ℤ) := by
      rw [hcoeff]
      simp [exponentOfFunction]

/-- Sourcewise homogeneity reduces coefficient nonnegativity of a polynomial
to nonnegativity of the squarefree coefficients of its balanced
polarizations. -/
theorem coeff_nonneg_of_balanced_polarizations
    [DecidableEq V]
    (src : E → V) (degree : V → ℕ) (P : MvPolynomial E ℤ)
    (hdegree : ∀ d ∈ P.support, ∀ v,
      (∑ e ∈ Finset.univ.filter (fun e : E => src e = v), d e) = degree v)
    (hpolarized : ∀ α : E →₀ ℕ,
      (∀ v, (∑ e ∈ Finset.univ.filter (fun e : E => src e = v), α e) = degree v) →
      0 ≤ (polarizationHom α P).coeff
        (squarefreeExponent (E := PolarizedEdge α))) :
    ∀ α : E →₀ ℕ, 0 ≤ P.coeff (exponentOfFunction α) := by
  classical
  intro α
  by_cases hzero : P.coeff (exponentOfFunction α) = 0
  · simp [hzero]
  · have hsupport : exponentOfFunction α ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr hzero
    have hdegreeα : ∀ v,
        (∑ e ∈ Finset.univ.filter (fun e : E => src e = v), α e) = degree v := by
      intro v
      simpa only [exponentOfFunction_apply] using hdegree (exponentOfFunction α) hsupport v
    have hnonneg := hpolarized α hdegreeα
    rw [coeff_polarizationHom_squarefree] at hnonneg
    have hfactor : 0 < ∏ e : E, (Nat.factorial (α e) : ℤ) := by
      apply Finset.prod_pos
      intro e he
      exact_mod_cast Nat.factorial_pos (α e)
    nlinarith

/-- Every finitely supported exponent on a sum type is the sum of its
restrictions extended by zero to the two summands. -/
theorem embDomain_comapDomain_sum {σ τ : Type*} (d : σ ⊕ τ →₀ ℕ) :
    Finsupp.embDomain Function.Embedding.inl
        (Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn) +
      Finsupp.embDomain Function.Embedding.inr
        (Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn) = d := by
  rw [Finsupp.embDomain_inl, Finsupp.embDomain_inr, ←Finsupp.sumElim_add]
  simpa using Finsupp.comapDomain_sumElim_comapDomain d
/-- The coefficient used in the induction for a balanced system. -/
noncomputable def balancedCoefficient (F : FiniteFiberSystem V E) : ℤ:=
  F.quotientDeterminant.coeff squarefreeExponent

/-- The squarefree coefficient of a polarized quotient determinant is the
balanced coefficient of the system with labelled parallel copies. -/
theorem polarizationHom_squarefree_eq_balancedCoefficient
    (F : FiniteFiberSystem V E) (α : E →₀ ℕ) :
    (polarizationHom α F.quotientDeterminant).coeff
        (squarefreeExponent (E := PolarizedEdge α)) =
      balancedCoefficient (F.polarize α) := by
  rw [polarizationHom_quotientDeterminant_eq_polarize]
  rfl

/-- Assuming sourcewise homogeneity and positivity for every balanced
polarization, all coefficients of the quotient determinant are nonnegative. -/
theorem quotientDeterminant_coeff_nonneg_of_balanced_polarizations
    [DecidableEq V] (F : FiniteFiberSystem V E)
    (hdegree : ∀ d ∈ F.quotientDeterminant.support, ∀ v,
      (∑ e ∈ Finset.univ.filter (fun e : E => F.src e = v), d e) = F.fiberDimension v)
    (hbalanced : ∀ α : E →₀ ℕ,
      (∀ v, (∑ e ∈ Finset.univ.filter (fun e : E => F.src e = v), α e) = F.fiberDimension v) →
      0 ≤ balancedCoefficient (F.polarize α)) :
    ∀ α : E →₀ ℕ, 0 ≤ F.quotientDeterminant.coeff (exponentOfFunction α) := by
  apply coeff_nonneg_of_balanced_polarizations F.src F.fiberDimension
    F.quotientDeterminant hdegree
  intro α hα
  rw [polarizationHom_squarefree_eq_balancedCoefficient]
  exact hbalanced α hα

/-- If every balanced finite-fiber system has nonnegative balanced
coefficient, then sourcewise homogeneity gives nonnegativity of every
coefficient of the quotient determinant. -/
theorem quotientDeterminant_coeff_nonneg_of_balancedCoefficient_nonneg
    [DecidableEq V] (F : FiniteFiberSystem V E)
    (hdegree : ∀ d ∈ F.quotientDeterminant.support, ∀ v,
      (∑ e ∈ Finset.univ.filter (fun e : E => F.src e = v), d e) = F.fiberDimension v)
    (hbalanced : ∀ α : E →₀ ℕ, (F.polarize α).Balanced →
      0 ≤ balancedCoefficient (F.polarize α)) :
    ∀ α : E →₀ ℕ, 0 ≤ F.quotientDeterminant.coeff (exponentOfFunction α) := by
  apply coeff_nonneg_of_balanced_polarizations F.src F.fiberDimension
    F.quotientDeterminant hdegree
  intro α hα
  have hpolarized : (F.polarize α).Balanced := by
    intro v
    rw [polarize_outdegree]
    exact hα v
  rw [polarizationHom_squarefree_eq_balancedCoefficient]
  exact hbalanced α hpolarized

/-- The determinant's source homogeneity is automatic from its row structure,
so balanced-system positivity alone suffices for all coefficient signs. -/
theorem quotientDeterminant_coeff_nonneg_of_balancedCoefficient_nonneg_auto
    [DecidableEq V] (F : FiniteFiberSystem V E)
    (hbalanced : ∀ α : E →₀ ℕ, (F.polarize α).Balanced →
      0 ≤ balancedCoefficient (F.polarize α)) :
    ∀ α : E →₀ ℕ, 0 ≤ F.quotientDeterminant.coeff (exponentOfFunction α) := by
  apply quotientDeterminant_coeff_nonneg_of_balancedCoefficient_nonneg F
    (fun d hd v => by
      simpa [FiniteFiberSystem.sourceExponentDegree] using
        F.quotientDeterminant_sourceExponentDegree v hd)
    hbalanced

/-- Differentiating with respect to an edge and extracting the squarefree
monomial on the other edges recovers the balanced coefficient. -/
theorem squarefreeDerivativeCoeff_eq_balancedCoefficient
    (F : FiniteFiberSystem V E) (e : E) :
    (MvPolynomial.pderiv e F.quotientDeterminant).coeff
      (squarefreeExponentExcept e) = balancedCoefficient F := by
  classical
  have hex : squarefreeExponentExcept e e = 0 := by
    simp [squarefreeExponentExcept]
  rw [MvPolynomial.coeff_pderiv, squarefreeExponentExcept_add_single]
  simp [balancedCoefficient, hex]


/-- The determinant polynomial of a loop-contraction child, renamed back to
the original edge-variable type. -/
abbrev LoopChildIndex (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) :=
  {p : F.Fiber (F.src e) // p ≠ F.loopTargetInSource e he p}

noncomputable instance (priority := 100) loopChildIndexFintype
    (F : FiniteFiberSystem V E) (e : E) (he : F.src e = F.tgt e) :
    Fintype (LoopChildIndex F e he) := by
  classical
  letI := F.fiberFintype (F.src e)
  infer_instance

/- Fixed sheets contribute zero to the loop edge block, so its rank-one
decomposition can be restricted to the moved sheets indexing contractions. -/
set_option maxHeartbeats 500000 in
theorem quotientEdgeCoefficient_loop_rankOne_sum_moved
    (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e)
    [Fintype (F.Fiber (F.src e))] [DecidableEq (F.Fiber (F.src e))]
    (i j : F.CoordAt (F.src e)) :
    F.quotientEdgeCoefficient e ⟨F.src e, i⟩ ⟨F.src e, j⟩ =
      ∑p ∈ Finset.univ.filter
          (fun p : F.Fiber (F.src e) => p ≠ F.loopTargetInSource e he p),
        ((if p = i.1 then (1 : ℤ) else 0) -
          (if p = F.reference (F.src e) then 1 else 0)) *
        ((if p = j.1 then (1 : ℤ) else 0) -
          (if F.loopTargetInSource e he p = j.1 then 1 else 0)) := by
  classical
  let moved (p : F.Fiber (F.src e)) : Prop :=
    p ≠ F.loopTargetInSource e he p
  let term (p : F.Fiber (F.src e)) : ℤ:=
    ((if p = i.1 then (1 : ℤ) else 0) -
      (if p = F.reference (F.src e) then 1 else 0)) *
    ((if p = j.1 then (1 : ℤ) else 0) -
      (if F.loopTargetInSource e he p = j.1 then 1 else 0))
  have hfixed (p : F.Fiber (F.src e))
      (hp : ¬ p ≠ F.loopTargetInSource e he p) : term p = 0 := by
    have hmap : F.loopTargetInSource e he p = p := by
      by_contra h
      exact hp (fun hp' => h hp'.symm)
    simp [term, hmap]
  have hzero :
      (∑p ∈ Finset.univ.filter (fun p : F.Fiber (F.src e) => ¬ moved p),
        term p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    exact hfixed p (Finset.mem_filter.mp hp |>.2)
  rw [F.quotientEdgeCoefficient_loop_rankOne_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ moved term]
  rw [hzero, add_zero]
  simp [he, moved, term]

noncomputable def loopChildPolynomial
    (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e) (p : LoopChildIndex F e he) :
    MvPolynomial E ℤ:=
  MvPolynomial.rename EdgesExcept.val
    (F.contractLoopEdge e he p.1 p.2).quotientDeterminant

/-- Renaming a polynomial that omits edge `e` preserves its squarefree
coefficient, when viewed in the original edge-variable type. -/
theorem coeff_rename_squarefreeExcept
    {e : E} (P : MvPolynomial (EdgesExcept e) ℤ) :
  (MvPolynomial.rename EdgesExcept.val P).coeff
      (squarefreeExponentExcept e) = P.coeff squarefreeExponent := by
  classical
  let incl : EdgesExcept e ↪ E :=
    ⟨EdgesExcept.val, fun a b h => EdgesExcept.ext h⟩
  have hemb : (squarefreeExponent (E := EdgesExcept e)).embDomain incl =
      squarefreeExponentExcept e := by
    ext f
    by_cases hf : f = e
    · subst f
      have hrange : e ∉ Set.range incl := by
        rintro ⟨x, hx⟩
        exact x.property hx
      rw [Finsupp.embDomain_of_notMem_range incl _ e hrange]
      simp [squarefreeExponentExcept]
    · let x : EdgesExcept e := ⟨f, hf⟩
      have hx : incl x = f := rfl
      have hxe : incl x ≠e := by
        change x.val ≠e
        exact hf
      rw [←hx, Finsupp.embDomain_apply_self]
      simp [squarefreeExponent, squarefreeExponentExcept, hxe]
  rw [←hemb]
  exact MvPolynomial.coeff_rename_embDomain incl P squarefreeExponent

/-- The choices in vertex elimination pair each incoming edge with a
distinct outgoing edge. -/
abbrev EliminationChoice (F : FiniteFiberSystem V E) (u : V) :=
  F.Incoming u ↪ F.Outgoing u

/-- Edges of an elimination child retain distinct parent labels: surviving
edges use their original labels, and virtual edges use their incoming label. -/
def eliminationEdgeEmbedding (F : FiniteFiberSystem V E) (u : V) :
    (F.Away u ⊕F.Incoming u) ↪E where
  toFun
    | Sum.inl e => e.1
    | Sum.inr e => e.1
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            change a.1 = b.1 at hab
            apply congrArg Sum.inl
            apply Subtype.ext
            exact hab
        | inr b =>
            change a.1 = b.1 at hab
            have ht := congrArg F.tgt hab
            exact False.elim (a.2.2 (ht.trans b.2))
    | inr a =>
        cases b with
        | inl b =>
            change a.1 = b.1 at hab
            have ht := congrArg F.tgt hab.symm
            exact False.elim (b.2.2 (ht.trans a.2))
        | inr b =>
            change a.1 = b.1 at hab
            apply congrArg Sum.inr
            apply Subtype.ext
            exact hab

/-- The determinant of an elimination child, expressed in the retained
parent-edge variables. -/
noncomputable def eliminationChildPolynomial (F : FiniteFiberSystem V E)
    [DecidableEq V] [DecidableEq E] (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : EliminationChoice F u) : MvPolynomial E ℤ:=
  MvPolynomial.rename (eliminationEdgeEmbedding F u)
    (F.eliminateSystem (u := u) hloop φ).quotientDeterminant

/-- Renaming an elimination child preserves its squarefree coefficient on
the retained edge labels. -/
theorem coeff_eliminationChildPolynomial [DecidableEq V] [DecidableEq E]
    (F : FiniteFiberSystem V E) (u : V)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (φ : EliminationChoice F u) :
    (eliminationChildPolynomial F u hloop φ).coeff
        ((squarefreeExponent (E := F.Away u ⊕F.Incoming u)).embDomain
          (eliminationEdgeEmbedding F u)) =
      balancedCoefficient (F.eliminateSystem (u := u) hloop φ) := by
  classical
  exact MvPolynomial.coeff_rename_embDomain
    (eliminationEdgeEmbedding F u)
    ((F.eliminateSystem (u := u) hloop φ).quotientDeterminant)
    (squarefreeExponent (E := F.Away u ⊕F.Incoming u))

theorem squarefreeExponent_mapDomain_edgesExcept (e : E) :
    (squarefreeExponent (E := EdgesExcept e)).mapDomain EdgesExcept.val =
      squarefreeExponentExcept e := by
  classical
  let incl : EdgesExcept e ↪ E := ⟨EdgesExcept.val, edgesExcept_val_injective e⟩
  change (squarefreeExponent (E := EdgesExcept e)).mapDomain incl = _
  rw [← Finsupp.embDomain_eq_mapDomain]
  ext f
  by_cases hf : f = e
  · subst f
    have hrange : e ∉ Set.range incl := by
      rintro ⟨x, hx⟩
      exact x.property hx
    rw [Finsupp.embDomain_of_notMem_range incl _ e hrange]
    simp [squarefreeExponentExcept]
  · let x : EdgesExcept e := ⟨f, hf⟩
    have hx : incl x = f := rfl
    rw [← hx, Finsupp.embDomain_apply_self]
    simp [squarefreeExponent, squarefreeExponentExcept, hx, hf]

theorem coeff_deleteEdgeVariables_squarefree (e : E) (P : MvPolynomial E ℤ) :
    (deleteEdgeVariables e P).coeff squarefreeExponent =
      P.coeff (squarefreeExponentExcept e) := by
  rw [deleteEdgeVariables, MvPolynomial.coeff_killCompl,
    squarefreeExponent_mapDomain_edgesExcept]

theorem loopCoefficientRecurrence_of_specialized_derivative
    (F : FiniteFiberSystem V E) (e : E) (he : F.src e = F.tgt e)
    (hderiv : deleteEdgeVariables e (MvPolynomial.pderiv e F.quotientDeterminant) =
      ∑ p : LoopChildIndex F e he,
        (F.contractLoopEdge e he p.1 p.2).quotientDeterminant) :
    balancedCoefficient F = ∑ p : LoopChildIndex F e he,
      balancedCoefficient (F.contractLoopEdge e he p.1 p.2) := by
  classical
  have h := congrArg (fun P : MvPolynomial (EdgesExcept e) ℤ =>
    P.coeff squarefreeExponent) hderiv
  simpa only [coeff_deleteEdgeVariables_squarefree,
    squarefreeDerivativeCoeff_eq_balancedCoefficient, MvPolynomial.coeff_sum,
    balancedCoefficient] using h

/-- The derivative identity uses contractions retaining all base edges.
Setting the loop variable to zero then gives the deleted-edge recurrence. -/
theorem loopCoefficientRecurrence_of_derivative_identity
    (F : FiniteFiberSystem V E) (e : E)
    (he : F.src e = F.tgt e)
    (hderiv : MvPolynomial.pderiv e F.quotientDeterminant =
      ∑ p : LoopChildIndex F e he,
        (F.contractMovedEdge (F.src e) p.1 (F.loopTargetInSource e he p.1) p.2).quotientDeterminant) :
    balancedCoefficient F =
      ∑p : LoopChildIndex F e he,
        balancedCoefficient (F.contractLoopEdge e he p.1 p.2) := by
  classical
  apply loopCoefficientRecurrence_of_specialized_derivative F e he
  have h := congrArg (deleteEdgeVariables e) hderiv
  simpa only [map_sum, deleteEdgeVariables_quotientDeterminant,
    FiniteFiberSystem.contractLoopEdge] using h

/-- The loop-contraction branch of balanced induction: once the loop
coefficient recurrence is available, positivity follows from positivity for
the lower-dimensional balanced contractions. -/
theorem balancedCoefficient_nonnegative_of_loop_recurrence
    (F : FiniteFiberSystem V E) (hF : F.Balanced)
    (e : E) (he : F.src e = F.tgt e)
    (hD : 0 < F.totalDimension)
    (hrec : balancedCoefficient F =
      ∑p : LoopChildIndex F e he,
        balancedCoefficient (F.contractLoopEdge e he p.1 p.2))
    (hind : ∀ (p : LoopChildIndex F e he),
      (F.contractLoopEdge e he p.1 p.2).Balanced →
      (F.contractLoopEdge e he p.1 p.2).totalDimension < F.totalDimension →
      0 ≤ balancedCoefficient (F.contractLoopEdge e he p.1 p.2)) :
    0 ≤ balancedCoefficient F := by
  classical
  rw [hrec]
  apply Finset.sum_nonneg
  intro p hp
  apply hind p
  · exact Balanced.contractLoopEdge (F := F) hF e he p.1 p.2

  · have hdim := F.contractLoopEdge_totalDimension e he p.1 p.2
    omega
/-- The loop-free vertex-elimination branch of balanced induction.  The
recurrence sums over the injective pairings from incoming to outgoing edges;
each child remains balanced and has smaller total dimension. -/
theorem balancedCoefficient_nonnegative_of_elimination_recurrence
    [DecidableEq V] [DecidableEq E]
    (F : FiniteFiberSystem V E) (hF : F.Balanced)
    (hloop : ∀ e : E, F.src e ≠ F.tgt e)
    (u : V) (hu : 0 < F.outdegree u)
    (hD : 0 < F.totalDimension)
    (hrec : balancedCoefficient F =
      (Nat.factorial (F.outdegree u - F.indegree u) : ℤ) *
        ∑ φ : F.Incoming u ↪ F.Outgoing u,
          balancedCoefficient (F.eliminateSystem (u := u) hloop φ))
    (hind : ∀ (φ : F.Incoming u ↪ F.Outgoing u),
      (F.eliminateSystem (u := u) hloop φ).Balanced →
      (F.eliminateSystem (u := u) hloop φ).totalDimension < F.totalDimension →
      0 ≤ balancedCoefficient (F.eliminateSystem (u := u) hloop φ)) :
    0 ≤ balancedCoefficient F := by
  classical
  rw [hrec]
  apply mul_nonneg
  · exact_mod_cast Nat.zero_le (Nat.factorial (F.outdegree u - F.indegree u))
  · apply Finset.sum_nonneg
    intro φ hφ
    apply hind φ
    · exact Balanced.eliminateSystem_balanced (F := F) hF hloop φ
    · rw [Balanced.eliminateSystem_totalDimension (F := F) hF hloop φ]
      have hfiber : 0 < F.fiberDimension u := by
        rw [← hF u]
        exact hu
      omega
/-- The balanced induction starts at the empty system: zero quotient
dimension forces there to be no base edges, and the empty determinant is 1. -/
theorem balancedCoefficient_eq_one_of_totalDimension_eq_zero
    (F : FiniteFiberSystem V E) (hF : F.Balanced)
    (hD : F.totalDimension = 0) : balancedCoefficient F = 1 := by
  classical
  have hEcard : Fintype.card E = 0 := by
    rw [FiniteFiberSystem.Balanced.card_edges_eq_totalDimension (F := F) hF, hD]
  letI : IsEmpty E := Fintype.card_eq_zero_iff.mp hEcard
  have hCcard : Fintype.card F.Coord = 0 := by
    simpa [FiniteFiberSystem.totalDimension] using hD
  letI : IsEmpty F.Coord := Fintype.card_eq_zero_iff.mp hCcard
  have hdet : F.quotientDeterminant = 1 := by
    change Matrix.det F.quotientLaplacian = 1
    exact Matrix.det_isEmpty
  have hα : squarefreeExponent (E := E) = 0 := by
    ext e
    exact isEmptyElim e
  rw [balancedCoefficient, hdet, hα]
  simp

/-- Positivity of the coefficient targeted by the balanced-system
induction. -/
def HasNonnegativeBalancedCoefficient (F : FiniteFiberSystem V E) : Prop :=
  0 ≤ balancedCoefficient F

/-- Base case for the balanced coefficient induction. -/
theorem balancedCoefficient_nonnegative_of_totalDimension_eq_zero
    (F : FiniteFiberSystem V E) (hF : F.Balanced)
    (hD : F.totalDimension = 0) : HasNonnegativeBalancedCoefficient F := by
  change 0 ≤ balancedCoefficient F
  rw [balancedCoefficient_eq_one_of_totalDimension_eq_zero F hF hD]
  norm_num

/-! The following theorem packages the dimension induction used in Section 5.
Its two recurrence hypotheses are the exact statements proved by the loop and
elimination arguments; once those polynomial identities are supplied, the
balanced-system positivity theorem follows without further assumptions. -/

/-- The balanced coefficient is nonnegative for every finite-fiber system,
provided the loop and vertex-elimination coefficient recurrences hold. -/
def BalancedCoefficientNonnegativeAt (D : Nat) : Prop :=
  ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]
    (F : FiniteFiberSystem.{uV, uE, uF} V E), F.Balanced →F.totalDimension = D →
    0 ≤ balancedCoefficient F

set_option maxHeartbeats 1000000 in
theorem balancedCoefficient_nonnegative_of_recurrences
    (loopRec : ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]
      (F : FiniteFiberSystem.{uV, uE, uF} V E) (hF : F.Balanced)
      (e : E) (he : F.src e = F.tgt e),
      balancedCoefficient F =
        ∑p : LoopChildIndex F e he,
          balancedCoefficient
            (@FiniteFiberSystem.contractLoopEdge V E _ _ F e he p.1 p.2))
    (elimRec : ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E]
      (F : FiniteFiberSystem.{uV, uE, uF} V E) (hF : F.Balanced)
      (hloop : ∀ e : E, F.src e ≠ F.tgt e)
      (u : V) (hu : 0 < F.outdegree u) (hle : F.indegree u ≤ F.outdegree u),
      balancedCoefficient F =
        (Nat.factorial (F.outdegree u - F.indegree u) : ℤ) *
          ∑ φ : F.Incoming u ↪ F.Outgoing u,
            balancedCoefficient (F.eliminateSystem (u := u) hloop φ)) :
    ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]
      (F : FiniteFiberSystem.{uV, uE, uF} V E), F.Balanced →
      0 ≤ balancedCoefficient F := by
  intro V E _ _ F hF
  classical
  have hAll : ∀ D, BalancedCoefficientNonnegativeAt D := by
    intro D
    induction D using Nat.strong_induction_on with
    | h D ih =>
      intro V E _ _ F hF hD
      classical
      by_cases hzero : D = 0
      · rw [hzero] at hD
        exact balancedCoefficient_nonnegative_of_totalDimension_eq_zero F hF hD
      have hpos : 0 < F.totalDimension := by omega
      by_cases hex : ∃ e : E, F.src e = F.tgt e
      · obtain ⟨e, he⟩ := hex
        rw [loopRec F hF e he]
        apply Finset.sum_nonneg
        intro p hp
        have hdim := F.contractLoopEdge_totalDimension e he p.1 p.2
        apply ih (F.contractLoopEdge e he p.1 p.2).totalDimension
        ·
          omega
        · exact Balanced.contractLoopEdge (F := F) hF e he p.1 p.2
        · rfl
      · have hloop : ∀ e : E, F.src e ≠ F.tgt e := by
          intro e he
          exact hex ⟨e, he⟩
        have hEpos : 0 < Fintype.card E := by
          rw [Balanced.card_edges_eq_totalDimension hF]
          exact hpos
        have hEnonempty : Nonempty E := Fintype.card_pos_iff.mp hEpos
        obtain ⟨u, hu, hle⟩:= F.exists_elimination_vertex hEnonempty
        have hrec := elimRec (V := V) (E := E) F hF hloop u hu hle
        rw [hrec]
        apply mul_nonneg
        · exact_mod_cast Nat.zero_le (Nat.factorial (F.outdegree u - F.indegree u))
        · apply Finset.sum_nonneg
          intro φ hφ
          have hdim := Balanced.eliminateSystem_totalDimension
            (F := F) hF hloop φ
          apply ih (F.eliminateSystem (u := u) hloop φ).totalDimension
          · rw [Balanced.eliminateSystem_totalDimension (F := F) hF hloop φ]
            rw [←hD]
            have hfiber : 0 < F.fiberDimension u := by
              rw [← hF u]
              exact hu
            omega
          · exact Balanced.eliminateSystem_balanced (F := F) hF hloop φ
          · rfl
  exact hAll F.totalDimension F hF rfl

end Positivity
