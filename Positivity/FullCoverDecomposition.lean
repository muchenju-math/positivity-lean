import Positivity.BlockLaplacian
import Positivity.FiberZeroSumBasis
import Positivity.CofactorDecomposition
import Positivity.CoveringMatrix

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

abbrev FullCoord (F : FiniteFiberSystem V E) := Sigma F.Fiber

noncomputable instance fullCoordFintype (F : FiniteFiberSystem V E) : Fintype F.FullCoord := by
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  infer_instance

noncomputable instance fullCoordDecidableEq (F : FiniteFiberSystem V E) : DecidableEq F.FullCoord :=
  Classical.decEq _

noncomputable def fullSplitEquiv (F : FiniteFiberSystem V E) : F.FullCoord ≃ V ⊕ F.Coord :=
  (Equiv.sigmaCongrRight (fun v => splitFiberEquiv (F.reference v))).trans (sigmaSplitEquiv F.CoordAt)

noncomputable def fullLocalBasis (F : FiniteFiberSystem V E) (v : V) :
    Matrix (F.Fiber v) (SplitFiber (F.reference v)) (MvPolynomial E ℚ) :=
  (fiberZeroSumBasis (F.reference v)).map MvPolynomial.C

noncomputable def fullLocalBasisInv (F : FiniteFiberSystem V E) (v : V) :
    Matrix (SplitFiber (F.reference v)) (F.Fiber v) (MvPolynomial E ℚ) := by
  letI := F.fiberFintype v
  exact (fiberZeroSumBasisInv (F.reference v)).map MvPolynomial.C

noncomputable def fullLocalPullback (F : FiniteFiberSystem V E) (e : E) :
    Matrix (F.Fiber (F.src e)) (F.Fiber (F.tgt e)) (MvPolynomial E ℚ) :=
  (fullPullback (F.fiberMap e)).map MvPolynomial.C

noncomputable def zeroLocalPullback (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (e : E) :
    Matrix (F.CoordAt (F.src e)) (F.CoordAt (F.tgt e)) (MvPolynomial E ℚ) := by
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  exact (zeroSumPullback (R := ℚ) (F.reference (F.src e)) (F.reference (F.tgt e))
    (Equiv.ofBijective (F.fiberMap e) (hbij e))).map MvPolynomial.C

noncomputable def fullGraphMatrix (F : FiniteFiberSystem V E) :
    Matrix F.FullCoord F.FullCoord (MvPolynomial E ℚ) := by
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  exact blockLaplacian F.src F.tgt F.fullLocalPullback MvPolynomial.X

noncomputable def zeroGraphMatrix (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) : Matrix F.Coord F.Coord (MvPolynomial E ℚ) :=
  blockLaplacian F.src F.tgt (F.zeroLocalPullback hbij) MvPolynomial.X

noncomputable def baseGraphMatrix (F : FiniteFiberSystem V E) : Matrix V V (MvPolynomial E ℚ) :=
  scalarLaplacian F.src F.tgt MvPolynomial.X

noncomputable def fullBasis (F : FiniteFiberSystem V E) :
    Matrix F.FullCoord (V ⊕ F.Coord) (MvPolynomial E ℚ) :=
  (Matrix.blockDiagonal' F.fullLocalBasis).submatrix id (sigmaSplitEquiv F.CoordAt).symm

noncomputable def fullBasisInv (F : FiniteFiberSystem V E) :
    Matrix (V ⊕ F.Coord) F.FullCoord (MvPolynomial E ℚ) :=
  (Matrix.blockDiagonal' F.fullLocalBasisInv).submatrix (sigmaSplitEquiv F.CoordAt).symm id

theorem fullLocalBasis_inverse (F : FiniteFiberSystem V E) (v : V) :
    letI := F.fiberFintype v
    F.fullLocalBasis v * F.fullLocalBasisInv v = 1 ∧
      F.fullLocalBasisInv v * F.fullLocalBasis v = 1 := by
  letI := F.fiberFintype v
  constructor
  · have h := congrArg (fun M : Matrix (F.Fiber v) (F.Fiber v) ℚ => M.map (MvPolynomial.C (σ := E)))
      (fiberZeroSumBasis_right_inverse (F.reference v))
    simp only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] at h
    convert! h using 1
  · have h := congrArg (fun M : Matrix (SplitFiber (F.reference v)) (SplitFiber (F.reference v)) ℚ =>
      M.map (MvPolynomial.C (σ := E))) (fiberZeroSumBasis_left_inverse (F.reference v))
    simp only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] at h
    convert! h using 1

theorem fullBasis_inverse (F : FiniteFiberSystem V E) :
    F.fullBasis * F.fullBasisInv = 1 ∧ F.fullBasisInv * F.fullBasis = 1 := by
  classical
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  have hST : Matrix.blockDiagonal' F.fullLocalBasis * Matrix.blockDiagonal' F.fullLocalBasisInv = 1 := by
    rw [← Matrix.blockDiagonal'_mul]
    have h : (fun v => F.fullLocalBasis v * F.fullLocalBasisInv v) =
        (1 : ∀ v, Matrix (F.Fiber v) (F.Fiber v) (MvPolynomial E ℚ)) := by
      funext v
      exact (F.fullLocalBasis_inverse v).1
    rw [h, Matrix.blockDiagonal'_one]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hTS : Matrix.blockDiagonal' F.fullLocalBasisInv * Matrix.blockDiagonal' F.fullLocalBasis = 1 := by
    rw [← Matrix.blockDiagonal'_mul]
    have h : (fun v => F.fullLocalBasisInv v * F.fullLocalBasis v) =
        (1 : ∀ v, Matrix (SplitFiber (F.reference v)) (SplitFiber (F.reference v)) (MvPolynomial E ℚ)) := by
      funext v
      exact (F.fullLocalBasis_inverse v).2
    rw [h, Matrix.blockDiagonal'_one]
  constructor
  · simp only [fullBasis, fullBasisInv, Matrix.submatrix_mul_equiv, hST, Matrix.submatrix_id_id]
  · change (Matrix.blockDiagonal' F.fullLocalBasisInv).submatrix (sigmaSplitEquiv F.CoordAt).symm (Equiv.refl F.FullCoord) *
      (Matrix.blockDiagonal' F.fullLocalBasis).submatrix (Equiv.refl F.FullCoord) (sigmaSplitEquiv F.CoordAt).symm = _
    rw [Matrix.submatrix_mul_equiv, hTS, Matrix.submatrix_one_equiv]

theorem fullLocalPullback_intertwine (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (e : E) :
    letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
    F.fullLocalPullback e * F.fullLocalBasis (F.tgt e) =
      F.fullLocalBasis (F.src e) *
        Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} (MvPolynomial E ℚ)) 0 0
          (F.zeroLocalPullback hbij e) := by
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  have h := congrArg
    (fun M : Matrix (F.Fiber (F.src e)) (SplitFiber (F.reference (F.tgt e))) ℚ =>
      M.map (MvPolynomial.C (σ := E)))
    (fullPullback_zeroSumBasis (F.reference (F.src e)) (F.reference (F.tgt e))
      (Equiv.ofBijective (F.fiberMap e) (hbij e)))
  simp only [Matrix.map_mul, Matrix.fromBlocks_map, Matrix.map_one, Matrix.map_zero,
    map_zero, map_one] at h
  convert! h using 1

theorem fullGraphMatrix_intertwine (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) :
    F.fullGraphMatrix * F.fullBasis =
      F.fullBasis * Matrix.fromBlocks F.baseGraphMatrix 0 0 (F.zeroGraphMatrix hbij) := by
  classical
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  let Q := fun e => Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} (MvPolynomial E ℚ)) 0 0
    (F.zeroLocalPullback hbij e)
  let S := Matrix.blockDiagonal' F.fullLocalBasis
  let D := blockLaplacian (n := fun v => SplitFiber (F.reference v)) F.src F.tgt Q MvPolynomial.X
  let e := sigmaSplitEquiv F.CoordAt
  have h := blockLaplacian_intertwine (n := F.Fiber) (m := fun v => SplitFiber (F.reference v)) F.src F.tgt F.fullLocalPullback Q F.fullLocalBasis
    MvPolynomial.X (F.fullLocalPullback_intertwine hbij)
  have hh := congrArg (fun M => M.submatrix id e.symm) h
  change (F.fullGraphMatrix * S).submatrix id e.symm = (S * D).submatrix id e.symm at hh
  rw [← Matrix.submatrix_mul_equiv F.fullGraphMatrix S id (Equiv.refl F.FullCoord) e.symm,
    ← Matrix.submatrix_mul_equiv S D id e.symm e.symm] at hh
  have hd : D.submatrix e.symm e.symm =
      Matrix.fromBlocks F.baseGraphMatrix 0 0 (F.zeroGraphMatrix hbij) :=
    blockLaplacian_split F.src F.tgt (F.zeroLocalPullback hbij) MvPolynomial.X
  rw [hd] at hh
  convert! hh using 1

theorem fullBasis_constant_entry (F : FiniteFiberSystem V E) (r v : V) (p : F.Fiber r) :
    F.fullBasis ⟨r, p⟩ (Sum.inl v) = if r = v then 1 else 0 := by
  classical
  by_cases h : r = v
  · subst v
    simp [fullBasis, sigmaSplitEquiv, fullLocalBasis, fiberZeroSumBasis]
  · simp [fullBasis, sigmaSplitEquiv, Matrix.blockDiagonal'_apply_ne, h]

theorem fullBasisInv_constant_entry (F : FiniteFiberSystem V E) (r v : V) (p : F.Fiber r) :
    F.fullBasisInv (Sum.inl v) ⟨r, p⟩ =
      if v = r then MvPolynomial.C ((F.fiberSize r : ℚ)⁻¹) else 0 := by
  classical
  by_cases h : v = r
  · subst v
    simp [fullBasisInv, sigmaSplitEquiv, fullLocalBasisInv, fiberZeroSumBasisInv, fiberSize]
  · simp [fullBasisInv, sigmaSplitEquiv, Matrix.blockDiagonal'_apply_ne, h]

theorem baseGraphMatrix_det_zero (F : FiniteFiberSystem V E) (r : V) :
    F.baseGraphMatrix.det = 0 := by
  classical
  have hv : Matrix.mulVec F.baseGraphMatrix (fun _ => 1) = 0 := by
    funext v
    simp only [baseGraphMatrix, scalarLaplacian, Matrix.mulVec, dotProduct,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_one]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro e _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    by_cases h : v = F.src e <;> simp [Matrix.single, h, eq_comm]
  by_contra hdet
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  have hr := congrFun hz r
  exact one_ne_zero hr

/-- The covering cofactor identity before identifying cofactors with
arborescence polynomials. The normalization is the size of the root fiber. -/
theorem fullGraphMatrix_cofactor (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (r : V) (p : F.Fiber r) :
    F.fullGraphMatrix.adjugate ⟨r, p⟩ ⟨r, p⟩ =
      MvPolynomial.C ((F.fiberSize r : ℚ)⁻¹) * F.baseGraphMatrix.adjugate r r *
        (F.zeroGraphMatrix hbij).det := by
  classical
  exact cofactor_of_block_decomposition F.fullSplitEquiv F.fullGraphMatrix F.baseGraphMatrix
    (F.zeroGraphMatrix hbij) F.fullBasis F.fullBasisInv F.fullBasis_inverse.1 F.fullBasis_inverse.2
    (F.fullGraphMatrix_intertwine hbij) (F.baseGraphMatrix_det_zero r)
    ⟨r, p⟩ r (MvPolynomial.C ((F.fiberSize r : ℚ)⁻¹))
    (fun v => F.fullBasis_constant_entry r v p) (fun v => F.fullBasisInv_constant_entry r v p)

end Positivity.FiniteFiberSystem
