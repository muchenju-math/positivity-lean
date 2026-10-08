import Positivity.FiniteFiber
import Positivity.CoverCoordinateChange
import Positivity.SigmaBlockMatrix

namespace Positivity.FiniteFiberSystem
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E]

theorem coordAt_cast_val (F : FiniteFiberSystem V E) {v w : V} (h : v = w)
    (p : F.CoordAt v) : (h ▸ p : F.CoordAt w).val = h ▸ p.val := by
  cases h
  rfl

theorem quotientEdgeCoefficient_blocks (F : FiniteFiberSystem V E) (e : E) :
    Matrix.of (F.quotientEdgeCoefficient e) =
      sigmaBlock (F.src e) (F.src e) (1 : Matrix (F.CoordAt (F.src e)) _ ℤ) -
        sigmaBlock (F.src e) (F.tgt e) (F.pullback e) := by
  classical
  funext i j
  rcases i with ⟨v, p⟩
  rcases j with ⟨w, q⟩
  by_cases hv : v = F.src e
  · subst v
    by_cases hw : w = F.src e
    · subst w
      by_cases ht : F.src e = F.tgt e
      · simp [quotientEdgeCoefficient, sigmaBlock, Matrix.one_apply, pullback, ht, coordAt_cast_val]
      · simp [quotientEdgeCoefficient, sigmaBlock, Matrix.one_apply, pullback, ht]
    · have hij : (⟨F.src e, p⟩ : F.Coord) ≠ ⟨w, q⟩ :=
        fun h => hw (congrArg Sigma.fst h).symm
      by_cases ht : w = F.tgt e
      · subst w
        simp [quotientEdgeCoefficient, sigmaBlock, Matrix.one_apply, pullback, hij, hw]
      · simp [quotientEdgeCoefficient, sigmaBlock, Matrix.one_apply, pullback, hij, hw, ht]
  · have hi : F.src e ≠ v := Ne.symm hv
    simp [quotientEdgeCoefficient, sigmaBlock, hv, hi]

noncomputable def coveringPullback (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (e : E) :
    Matrix (F.CoordAt (F.src e)) (F.CoordAt (F.tgt e)) ℤ := by
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  exact zeroSumPullback (F.reference (F.src e)) (F.reference (F.tgt e))
    (Equiv.ofBijective (F.fiberMap e) (hbij e))

noncomputable def fiberReferenceShift (F : FiniteFiberSystem V E) (v : V) :
    Matrix (F.CoordAt v) (F.CoordAt v) ℤ :=
  referenceShiftMatrix (F.reference v)

noncomputable def globalReferenceShift (F : FiniteFiberSystem V E) : Matrix F.Coord F.Coord ℤ :=
  Matrix.blockDiagonal' F.fiberReferenceShift

noncomputable def coveringEdgeCoefficient (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (e : E) : Matrix F.Coord F.Coord ℤ :=
  sigmaBlock (F.src e) (F.src e) (1 : Matrix (F.CoordAt (F.src e)) _ ℤ) -
    sigmaBlock (F.src e) (F.tgt e) (F.coveringPullback hbij e)

theorem pullback_referenceShift (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (e : E) :
    F.pullback e * F.fiberReferenceShift (F.tgt e) =
      F.fiberReferenceShift (F.src e) * F.coveringPullback hbij e := by
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  exact normalizedPullback_referenceShift (R := ℤ)
    (F.reference (F.src e)) (F.reference (F.tgt e))
    (Equiv.ofBijective (F.fiberMap e) (hbij e))

theorem quotientEdgeCoefficient_referenceShift (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) (e : E) :
    Matrix.of (F.quotientEdgeCoefficient e) * F.globalReferenceShift =
      F.globalReferenceShift * F.coveringEdgeCoefficient hbij e := by
  rw [quotientEdgeCoefficient_blocks, coveringEdgeCoefficient, globalReferenceShift,
    Matrix.sub_mul, Matrix.mul_sub, sigmaBlock_mul_diagonal, sigmaBlock_mul_diagonal,
    diagonal_mul_sigmaBlock, diagonal_mul_sigmaBlock, Matrix.one_mul, Matrix.mul_one,
    pullback_referenceShift]

theorem globalReferenceShift_det_ne_zero (F : FiniteFiberSystem V E) :
    F.globalReferenceShift.det ≠ 0 := by
  classical
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  let c := Int.castRingHom ℚ
  have hv (v : V) : ((F.fiberReferenceShift v).map c).det ≠ 0 := by
    erw [← RingHom.map_det c (F.fiberReferenceShift v)]
    change c (referenceShiftMatrix (R := ℤ) (F.reference v)).det ≠ 0
    rw [referenceShiftMatrix_det]
    have hp : 0 < Fintype.card (F.Fiber v) := Fintype.card_pos_iff.mpr ⟨F.reference v⟩
    change (Fintype.card (F.Fiber v) : ℚ) ≠ 0
    exact_mod_cast Nat.ne_of_gt hp
  let J := Matrix.blockDiagonal' (fun v => ((F.fiberReferenceShift v).map c)⁻¹)
  have hprod : F.globalReferenceShift.map c * J = 1 := by
    rw [globalReferenceShift, Matrix.blockDiagonal'_map _ _ (map_zero c)]
    change Matrix.blockDiagonal' (fun v => (F.fiberReferenceShift v).map c) *
      Matrix.blockDiagonal' (fun v => ((F.fiberReferenceShift v).map c)⁻¹) = _
    rw [← Matrix.blockDiagonal'_mul]
    have hblocks : (fun v => (F.fiberReferenceShift v).map c * ((F.fiberReferenceShift v).map c)⁻¹) =
        (1 : ∀ v, Matrix (F.CoordAt v) (F.CoordAt v) ℚ) := by
      funext v
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hv v))
    rw [hblocks, Matrix.blockDiagonal'_one]
  intro hz
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul] at hdet
  erw [← RingHom.map_det c F.globalReferenceShift, hz, map_zero, zero_mul, Matrix.det_one] at hdet
  exact zero_ne_one hdet

/-- The covering matrix, in zero-sum coordinates on each fiber. -/
noncomputable def coveringLaplacian (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) : Matrix F.Coord F.Coord (MvPolynomial E ℤ) :=
  ∑ e, (MvPolynomial.X e : MvPolynomial E ℤ) •
    (F.coveringEdgeCoefficient hbij e).map (MvPolynomial.C (σ := E))

theorem quotientLaplacian_eq_sum_edge_matrices (F : FiniteFiberSystem V E) :
    F.quotientLaplacian = ∑ e, (MvPolynomial.X e : MvPolynomial E ℤ) •
      (Matrix.of (F.quotientEdgeCoefficient e)).map (MvPolynomial.C (σ := E)) := by
  funext i j
  simp [quotientLaplacian, Matrix.sum_apply, Matrix.smul_apply]

theorem quotientLaplacian_referenceShift (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) :
    F.quotientLaplacian * F.globalReferenceShift.map MvPolynomial.C =
      F.globalReferenceShift.map MvPolynomial.C * F.coveringLaplacian hbij := by
  classical
  rw [quotientLaplacian_eq_sum_edge_matrices, coveringLaplacian,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  have h := congrArg (fun M : Matrix F.Coord F.Coord ℤ => M.map (MvPolynomial.C (σ := E)))
    (F.quotientEdgeCoefficient_referenceShift hbij e)
  simpa only [RingHom.mapMatrix_apply, Matrix.map_mul] using h

/-- The covering matrix and the finite-fiber quotient matrix have equal
determinants, including zero-dimensional fibers. -/
theorem coveringLaplacian_det (F : FiniteFiberSystem V E)
    (hbij : ∀ e, Function.Bijective (F.fiberMap e)) :
    (F.coveringLaplacian hbij).det = F.quotientDeterminant := by
  classical
  have h := congrArg Matrix.det (F.quotientLaplacian_referenceShift hbij)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  erw [← RingHom.map_det (MvPolynomial.C (σ := E)) F.globalReferenceShift] at h
  have hne : (MvPolynomial.C F.globalReferenceShift.det : MvPolynomial E ℤ) ≠ 0 := by
    intro hz
    have hc := congrArg (fun p : MvPolynomial E ℤ => p.coeff 0) hz
    simp only [MvPolynomial.coeff_C, ite_true, MvPolynomial.coeff_zero] at hc
    exact F.globalReferenceShift_det_ne_zero hc
  change F.quotientDeterminant * MvPolynomial.C F.globalReferenceShift.det =
    MvPolynomial.C F.globalReferenceShift.det * (F.coveringLaplacian hbij).det at h
  rw [mul_comm] at h
  exact (mul_left_cancel₀ hne h).symm

end Positivity.FiniteFiberSystem
