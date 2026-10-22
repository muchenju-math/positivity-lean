import Positivity.CoverTreeIdentity
import Positivity.DeterminantDerivative

/-!
# The fiber-constant part of a finite-fiber Laplacian

This decomposition applies to arbitrary fiber maps. The first coordinate
in each fiber is its constant vector; the remaining basis vectors are the
coordinate vectors away from the chosen reference. Unlike the decomposition
for covers, the resulting matrix is only block upper triangular.
-/

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {α β R : Type*} [Fintype α] [Fintype β] [CommRing R]

noncomputable def fiberConstantBasis (a : α) : Matrix α (SplitFiber a) R :=
  fun p c => match c with
    | Sum.inl _ => 1
    | Sum.inr q => if p = q.val then 1 else 0

noncomputable def fiberConstantBasisInv (a : α) : Matrix (SplitFiber a) α R :=
  fun c p => match c with
    | Sum.inl _ => if p = a then 1 else 0
    | Sum.inr q => (if p = q.val then 1 else 0) - (if p = a then 1 else 0)

theorem fiberConstantBasis_left_inverse (a : α) :
    fiberConstantBasisInv (R := R) a * fiberConstantBasis (R := R) a = 1 := by
  classical
  funext i j
  rw [Matrix.mul_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [fiberConstantBasisInv, fiberConstantBasis]
    | inr j => simp [fiberConstantBasisInv, fiberConstantBasis, j.property]
  | inr i =>
    cases j with
    | inl j =>
      simp [fiberConstantBasisInv, fiberConstantBasis, Finset.sum_sub_distrib]
    | inr j =>
      simp [fiberConstantBasisInv, fiberConstantBasis,
        Matrix.one_apply, Ne.symm j.property, Subtype.ext_iff, eq_comm]

theorem fiberConstantBasis_right_inverse (a : α) :
    fiberConstantBasis (R := R) a * fiberConstantBasisInv (R := R) a = 1 := by
  classical
  exact (Matrix.mul_eq_one_comm_of_equiv (splitFiberEquiv a)).mpr
    (fiberConstantBasis_left_inverse a)

noncomputable def constantPullbackRow (a : α) (b : β) (f : α → β) :
    Matrix PUnit.{1} {q : β // q ≠ b} R :=
  fun _ q => if f a = q.val then 1 else 0

theorem pullback_fiberConstantBasis (a : α) (b : β) (f : α → β) :
    (Matrix.of (fun p q => if f p = q then (1 : R) else 0)) * fiberConstantBasis (R := R) b =
      fiberConstantBasis (R := R) a * Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} R)
        (constantPullbackRow a b f) 0 (normalizedPullback a b f) := by
  classical
  funext p c
  cases c with
  | inl c =>
    simp [Matrix.mul_apply, fiberConstantBasis, Fintype.sum_sum_type]
  | inr q =>
    simp only [Matrix.mul_apply, fiberConstantBasis, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, one_mul,
      constantPullbackRow, normalizedPullback, Fintype.sum_unique]
    rw [sum_nonreference_delta a p
      (fun x => (if f x = q.val then (1 : R) else 0) - (if f a = q.val then 1 else 0))
      (by simp)]
    simp

section Blocks
variable {V E : Type*} {n : V → Type*} [Fintype V] [Fintype E]
    [∀ v, Fintype (n v)]

noncomputable def sigmaConstantRow (u v : V) (B : Matrix PUnit.{1} (n v) R) :
    Matrix V (Sigma n) R :=
  fun i j => if i = u then if h : j.1 = v then B PUnit.unit (h ▸ j.2) else 0 else 0

omit [Fintype V] [∀ v, Fintype (n v)] in
theorem sigmaRectBlock_split_upper (u v : V) (c : R)
    (B : Matrix PUnit.{1} (n v) R) (M : Matrix (n u) (n v) R) :
    Matrix.reindex (sigmaSplitEquiv n) (sigmaSplitEquiv n)
      (sigmaRectBlock u v (Matrix.fromBlocks (Matrix.of (fun _ _ : PUnit.{1} => c)) B 0 M)) =
        Matrix.fromBlocks (Matrix.single u v c) (sigmaConstantRow u v B) 0
          (sigmaRectBlock u v M) := by
  classical
  funext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hi : i = u <;> by_cases hj : j = v <;> subst_vars <;>
        simp_all [Matrix.reindex_apply, sigmaSplitEquiv, sigmaRectBlock, Matrix.single, eq_comm]
    | inr j =>
      rcases j with ⟨j, q⟩
      by_cases hi : i = u <;> by_cases hj : j = v <;> subst_vars <;>
        simp_all [Matrix.reindex_apply, sigmaSplitEquiv, sigmaRectBlock, sigmaConstantRow, eq_comm]
  | inr i =>
    rcases i with ⟨i, p⟩
    cases j with
    | inl j =>
      by_cases hi : i = u <;> by_cases hj : j = v <;> subst_vars <;>
        simp_all [Matrix.reindex_apply, sigmaSplitEquiv, sigmaRectBlock, eq_comm]
    | inr j =>
      rcases j with ⟨j, q⟩
      by_cases hi : i = u <;> by_cases hj : j = v <;> subst_vars <;>
        simp_all [Matrix.reindex_apply, sigmaSplitEquiv, sigmaRectBlock, eq_comm]

omit [Fintype V] [∀ v, Fintype (n v)] in
theorem blockLaplacian_split_upper (src tgt : E → V)
    (B : ∀ e, Matrix PUnit.{1} (n (tgt e)) R)
    (P : ∀ e, Matrix (n (src e)) (n (tgt e)) R) (w : E → R) :
    Matrix.reindex (sigmaSplitEquiv n) (sigmaSplitEquiv n)
      (blockLaplacian src tgt
        (fun e => Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} R) (B e) 0 (P e)) w) =
      Matrix.fromBlocks (scalarLaplacian src tgt w)
        (-∑ e, w e • sigmaConstantRow (src e) (tgt e) (B e)) 0
        (blockLaplacian src tgt P w) := by
  classical
  let e := sigmaSplitEquiv n
  have hdiag (v : V) : (1 : Matrix (PUnit.{1} ⊕ n v) (PUnit.{1} ⊕ n v) R) =
      Matrix.fromBlocks (Matrix.of (fun _ _ : PUnit.{1} => (1 : R))) 0 0 1 := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]
  have hone : (1 : Matrix PUnit.{1} PUnit.{1} R) = Matrix.of (fun _ _ => (1 : R)) := by
    ext i j
    simp
  have hedge (a : E) :
      Matrix.reindex e e (sigmaRectBlock (src a) (src a)
        (1 : Matrix (PUnit.{1} ⊕ n (src a)) _ R) -
        sigmaRectBlock (src a) (tgt a) (Matrix.fromBlocks 1 (B a) 0 (P a))) =
      Matrix.fromBlocks (Matrix.single (src a) (src a) 1 - Matrix.single (src a) (tgt a) 1)
        (-sigmaConstantRow (src a) (tgt a) (B a)) 0
        (sigmaRectBlock (src a) (src a) (1 : Matrix (n (src a)) _ R) -
          sigmaRectBlock (src a) (tgt a) (P a)) := by
    change Matrix.reindex e e (sigmaRectBlock (src a) (src a) 1) -
      Matrix.reindex e e (sigmaRectBlock (src a) (tgt a) (Matrix.fromBlocks 1 (B a) 0 (P a))) = _
    rw [hdiag, hone, sigmaRectBlock_split_upper, sigmaRectBlock_split_upper]
    ext i j
    cases i <;> cases j <;> simp [sigmaConstantRow]
  have hsum : Matrix.reindex e e (blockLaplacian src tgt
      (fun a => Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} R) (B a) 0 (P a)) w) =
      ∑ a, w a • Matrix.reindex e e (sigmaRectBlock (src a) (src a)
        (1 : Matrix (PUnit.{1} ⊕ n (src a)) _ R) -
        sigmaRectBlock (src a) (tgt a) (Matrix.fromBlocks 1 (B a) 0 (P a))) := by
    ext i j
    simp [blockLaplacian, Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply]
    simp only [sigmaRectBlock, Matrix.one_apply]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> rfl
  rw [hsum]
  simp_rw [hedge]
  ext i j
  cases i <;> cases j <;>
    simp [scalarLaplacian, blockLaplacian, Matrix.sum_apply, Matrix.smul_apply,
      Finset.sum_neg_distrib]

end Blocks

/-- The manuscript uses the plus sign in `det (z I + M)`. -/
noncomputable def laplacianCharacteristic {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : Polynomial R := (-M).charpoly

theorem laplacianCharacteristic_affine {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) :
    laplacianCharacteristic M = Matrix.det (fun i j => Polynomial.C (M i j) +
      Polynomial.X * Polynomial.C ((1 : Matrix n n R) i j)) := by
  unfold laplacianCharacteristic Matrix.charpoly
  congr 1
  funext i j
  by_cases hij : i = j <;>
    simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal, Matrix.one_apply, hij, add_comm]

theorem laplacianCharacteristic_constant {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : (laplacianCharacteristic M).coeff 0 = M.det := by
  rw [laplacianCharacteristic_affine, Polynomial.coeff_zero_eq_eval_zero]
  change (Polynomial.evalRingHom (0 : R)) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  funext i j
  simp

theorem laplacianCharacteristic_linear {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : (laplacianCharacteristic M).coeff 1 = ∑ i, M.adjugate i i := by
  classical
  rw [laplacianCharacteristic_affine]
  have hd := derivative_det_affineMatrix_at_zero M (1 : Matrix n n R)
  have hc (p : Polynomial R) : p.coeff 1 = p.derivative.eval 0 := by
    simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  rw [hc, hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [adjugate_diagonal_eq_minor]
  convert det_updateRow_delta M i using 1
  congr 2
  funext j
  simp [Matrix.one_apply, eq_comm]

namespace FiniteFiberSystem
variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def constantLocalBasis (F : FiniteFiberSystem V E) (v : V) :
    Matrix (F.Fiber v) (SplitFiber (F.reference v)) (MvPolynomial E ℚ) :=
  fiberConstantBasis (F.reference v)

noncomputable def constantLocalBasisInv (F : FiniteFiberSystem V E) (v : V) :
    Matrix (SplitFiber (F.reference v)) (F.Fiber v) (MvPolynomial E ℚ) :=
  fiberConstantBasisInv (F.reference v)

noncomputable def quotientLocalPullback (F : FiniteFiberSystem V E) (e : E) :
    Matrix (F.CoordAt (F.src e)) (F.CoordAt (F.tgt e)) (MvPolynomial E ℚ) :=
  normalizedPullback (F.reference (F.src e)) (F.reference (F.tgt e)) (F.fiberMap e)

noncomputable def constantLocalRow (F : FiniteFiberSystem V E) (e : E) :
    Matrix PUnit.{1} (F.CoordAt (F.tgt e)) (MvPolynomial E ℚ) :=
  constantPullbackRow (F.reference (F.src e)) (F.reference (F.tgt e)) (F.fiberMap e)

noncomputable def quotientGraphMatrix (F : FiniteFiberSystem V E) :
    Matrix F.Coord F.Coord (MvPolynomial E ℚ) :=
  blockLaplacian F.src F.tgt F.quotientLocalPullback MvPolynomial.X

noncomputable def constantCrossMatrix (F : FiniteFiberSystem V E) :
    Matrix V F.Coord (MvPolynomial E ℚ) :=
  -∑ e, (MvPolynomial.X e : MvPolynomial E ℚ) •
    sigmaConstantRow (F.src e) (F.tgt e) (F.constantLocalRow e)

noncomputable def constantBasis (F : FiniteFiberSystem V E) :
    Matrix F.FullCoord (V ⊕ F.Coord) (MvPolynomial E ℚ) :=
  (Matrix.blockDiagonal' F.constantLocalBasis).submatrix id (sigmaSplitEquiv F.CoordAt).symm

noncomputable def constantBasisInv (F : FiniteFiberSystem V E) :
    Matrix (V ⊕ F.Coord) F.FullCoord (MvPolynomial E ℚ) :=
  (Matrix.blockDiagonal' F.constantLocalBasisInv).submatrix (sigmaSplitEquiv F.CoordAt).symm id

theorem constantBasis_inverse (F : FiniteFiberSystem V E) :
    F.constantBasis * F.constantBasisInv = 1 ∧ F.constantBasisInv * F.constantBasis = 1 := by
  classical
  let : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  have hST : Matrix.blockDiagonal' F.constantLocalBasis *
      Matrix.blockDiagonal' F.constantLocalBasisInv = 1 := by
    rw [← Matrix.blockDiagonal'_mul]
    have h : (fun v => F.constantLocalBasis v * F.constantLocalBasisInv v) =
        (1 : ∀ v, Matrix (F.Fiber v) (F.Fiber v) (MvPolynomial E ℚ)) := by
      funext v
      exact fiberConstantBasis_right_inverse (F.reference v)
    rw [h, Matrix.blockDiagonal'_one]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hTS : Matrix.blockDiagonal' F.constantLocalBasisInv *
      Matrix.blockDiagonal' F.constantLocalBasis = 1 := by
    rw [← Matrix.blockDiagonal'_mul]
    have h : (fun v => F.constantLocalBasisInv v * F.constantLocalBasis v) =
        (1 : ∀ v, Matrix (SplitFiber (F.reference v)) (SplitFiber (F.reference v)) (MvPolynomial E ℚ)) := by
      funext v
      exact fiberConstantBasis_left_inverse (F.reference v)
    rw [h, Matrix.blockDiagonal'_one]
  constructor
  · simp only [constantBasis, constantBasisInv, Matrix.submatrix_mul_equiv, hST, Matrix.submatrix_id_id]
  · change (Matrix.blockDiagonal' F.constantLocalBasisInv).submatrix
      (sigmaSplitEquiv F.CoordAt).symm (Equiv.refl F.FullCoord) *
      (Matrix.blockDiagonal' F.constantLocalBasis).submatrix
      (Equiv.refl F.FullCoord) (sigmaSplitEquiv F.CoordAt).symm = _
    rw [Matrix.submatrix_mul_equiv, hTS, Matrix.submatrix_one_equiv]

theorem fullLocalPullback_constantBasis (F : FiniteFiberSystem V E) (e : E) :
    letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
    F.fullLocalPullback e * F.constantLocalBasis (F.tgt e) =
      F.constantLocalBasis (F.src e) *
        Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} (MvPolynomial E ℚ))
          (F.constantLocalRow e) 0 (F.quotientLocalPullback e) := by
  let : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  have h : F.fullLocalPullback e =
      Matrix.of (fun p q => if F.fiberMap e p = q then (1 : MvPolynomial E ℚ) else 0) := by
    funext p q
    simp [fullLocalPullback, fullPullback]
  rw [h]
  exact pullback_fiberConstantBasis (F.reference (F.src e)) (F.reference (F.tgt e)) (F.fiberMap e)

/-- The fiber-constant submodule is invariant for arbitrary fiber maps. -/
theorem fullGraphMatrix_constant_intertwine (F : FiniteFiberSystem V E) :
    F.fullGraphMatrix * F.constantBasis =
      F.constantBasis * Matrix.fromBlocks F.baseGraphMatrix F.constantCrossMatrix 0
        F.quotientGraphMatrix := by
  classical
  let : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  let Q := fun e => Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} (MvPolynomial E ℚ))
    (F.constantLocalRow e) 0 (F.quotientLocalPullback e)
  let S := Matrix.blockDiagonal' F.constantLocalBasis
  let D := blockLaplacian (n := fun v => SplitFiber (F.reference v)) F.src F.tgt Q MvPolynomial.X
  let e := sigmaSplitEquiv F.CoordAt
  have h := blockLaplacian_intertwine (n := F.Fiber) (m := fun v => SplitFiber (F.reference v))
    F.src F.tgt F.fullLocalPullback Q F.constantLocalBasis MvPolynomial.X
    F.fullLocalPullback_constantBasis
  have hh := congrArg (fun M => M.submatrix id e.symm) h
  change (F.fullGraphMatrix * S).submatrix id e.symm = (S * D).submatrix id e.symm at hh
  rw [← Matrix.submatrix_mul_equiv F.fullGraphMatrix S id (Equiv.refl F.FullCoord) e.symm,
    ← Matrix.submatrix_mul_equiv S D id e.symm e.symm] at hh
  have hd : D.submatrix e.symm e.symm =
      Matrix.fromBlocks F.baseGraphMatrix F.constantCrossMatrix 0 F.quotientGraphMatrix :=
    blockLaplacian_split_upper F.src F.tgt F.constantLocalRow F.quotientLocalPullback MvPolynomial.X
  rw [hd] at hh
  convert! hh using 1

theorem quotientGraphMatrix_eq_map (F : FiniteFiberSystem V E) :
    F.quotientGraphMatrix =
      F.quotientLaplacian.map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  classical
  rw [quotientLaplacian_eq_sum_edge_matrices]
  funext i j
  simp only [quotientGraphMatrix, blockLaplacian, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul, map_sum,
    map_mul, MvPolynomial.map_X]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  rw [F.quotientEdgeCoefficient_blocks e]
  simp only [Matrix.sub_apply, map_sub, MvPolynomial.map_C]
  simp only [sigmaRectBlock, sigmaBlock]
  split_ifs <;> simp only [quotientLocalPullback, normalizedPullback, pullback,
    Matrix.one_apply, map_sub, apply_ite, map_one, map_zero] <;> split_ifs <;> rfl

/-- Equation (2.7), for arbitrary finite-fiber systems, without bijectivity. -/
theorem laplacianCharacteristicFactorization (F : FiniteFiberSystem V E) :
    laplacianCharacteristic F.fullGraphMatrix =
      laplacianCharacteristic F.baseGraphMatrix * laplacianCharacteristic F.quotientGraphMatrix := by
  classical
  let T := Matrix.fromBlocks F.baseGraphMatrix F.constantCrossMatrix 0 F.quotientGraphMatrix
  have hconj : F.constantBasisInv * (-F.fullGraphMatrix) * F.constantBasis = -T := by
    rw [Matrix.mul_assoc, Matrix.neg_mul, F.fullGraphMatrix_constant_intertwine,
      Matrix.mul_neg, ← Matrix.mul_assoc, (F.constantBasis_inverse).2, Matrix.one_mul]
  have hcard : Fintype.card F.FullCoord = Fintype.card (V ⊕ F.Coord) :=
    Fintype.card_congr F.fullSplitEquiv
  have h := Matrix.charpoly_mul_comm_of_le
    (F.constantBasisInv * (-F.fullGraphMatrix)) F.constantBasis (le_of_eq hcard)
  rw [hconj, ← Matrix.mul_assoc, (F.constantBasis_inverse).1, Matrix.one_mul,
    hcard, Nat.sub_self, pow_zero, one_mul] at h
  unfold laplacianCharacteristic
  rw [← h]
  have hneg : -T = Matrix.fromBlocks (-F.baseGraphMatrix) (-F.constantCrossMatrix) 0
      (-F.quotientGraphMatrix) := by
    ext i j
    cases i <;> cases j <;> simp [T]
  rw [hneg, Matrix.charpoly_fromBlocks_zero₂₁]

/-- Lemma 2.4: the sum over all roots, for arbitrary fiber maps. -/
theorem arborescence_sum_identity (F : FiniteFiberSystem V E) :
    ∑ p : F.FullCoord, F.liftedArborescencePolynomial p.1 p.2 =
      F.quotientDeterminant * ∑ r : V, arborescencePolynomial F.src F.tgt r := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hf := congrArg (fun p : Polynomial (MvPolynomial E ℚ) => p.coeff 1)
      F.laplacianCharacteristicFactorization
    rw [Polynomial.mul_coeff_one, laplacianCharacteristic_linear,
      laplacianCharacteristic_linear, laplacianCharacteristic_constant,
      laplacianCharacteristic_constant,
      F.baseGraphMatrix_det_zero (Classical.arbitrary V)] at hf
    simp only [zero_mul, zero_add, laplacianCharacteristic_linear] at hf
    have hdet : F.quotientGraphMatrix.det =
        F.quotientDeterminant.map (Int.castRingHom ℚ) := by
      rw [F.quotientGraphMatrix_eq_map]
      exact ((MvPolynomial.map (Int.castRingHom ℚ)).map_det F.quotientLaplacian).symm
    rw [hdet] at hf
    simp only [F.fullGraphMatrix_cofactor_tree, F.baseGraphMatrix_cofactor] at hf
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simpa only [map_sum, map_mul, mul_comm] using hf

end FiniteFiberSystem
end Positivity
