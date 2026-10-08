import Positivity.AdjugateBlocks
import Positivity.DeterminantCompression

namespace Positivity
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {I J V W R : Type*} [Fintype I] [Fintype J] [Fintype V] [Fintype W]
    [DecidableEq I] [DecidableEq J] [DecidableEq V] [DecidableEq W] [CommRing R]

theorem adjugate_intertwining (e : I ≃ J) (L : Matrix I I R) (D : Matrix J J R)
    (S : Matrix I J R) (T : Matrix J I R)
    (hST : S * T = 1) (hTS : T * S = 1) (hLS : L * S = S * D) :
    L.adjugate = S * D.adjugate * T := by
  let Sq := S.submatrix id e
  let Tq := T.submatrix e id
  let Dq := D.submatrix e e
  have hSTq : Sq * Tq = 1 := by
    simp only [Sq, Tq, Matrix.submatrix_mul_equiv, hST, Matrix.submatrix_id_id]
  have hTSq : Tq * Sq = 1 := by
    change T.submatrix e (Equiv.refl I) * S.submatrix (Equiv.refl I) e = _
    rw [Matrix.submatrix_mul_equiv, hTS, Matrix.submatrix_one_equiv]
  have hLSq : L * Sq = Sq * Dq := by
    have h := congrArg (fun M : Matrix I J R => M.submatrix id e) hLS
    change (L * S).submatrix id e = (S * D).submatrix id e at h
    rw [← Matrix.submatrix_mul_equiv L S id (Equiv.refl I) e,
      ← Matrix.submatrix_mul_equiv S D id e e] at h
    exact h
  have hL : L = Sq * Dq * Tq := by
    calc
      L = L * (Sq * Tq) := by rw [hSTq, Matrix.mul_one]
      _ = Sq * Dq * Tq := by rw [← Matrix.mul_assoc, hLSq]
  rw [hL, adjugate_conjugation Dq Sq Tq hSTq hTSq]
  simp only [Sq, Tq, Dq, Matrix.adjugate_submatrix_equiv_self,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

theorem adjugate_diagonal_eq_minor (M : Matrix I I R) (i : I) :
    M.adjugate i i =
      (M.submatrix (Subtype.val : {j : I // j ≠ i} → I) Subtype.val).det := by
  rw [Matrix.adjugate_apply]
  have h : (Pi.single i (1 : R) : I → R) = fun j => if j = i then 1 else 0 := by
    funext j
    simp [Pi.single_apply]
  rw [h, det_updateRow_delta]

/-- A cofactor in a space split into a constant part and its complement.
The constant-coordinate projection supplies the normalization factor. -/
theorem cofactor_of_block_decomposition (e : I ≃ V ⊕ W)
    (L : Matrix I I R) (A : Matrix V V R) (B : Matrix W W R)
    (S : Matrix I (V ⊕ W) R) (T : Matrix (V ⊕ W) I R)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hLS : L * S = S * Matrix.fromBlocks A 0 0 B) (hA : A.det = 0)
    (i : I) (r : V) (t : R)
    (hS : ∀ v, S i (Sum.inl v) = if r = v then 1 else 0)
    (hT : ∀ v, T (Sum.inl v) i = if v = r then t else 0) :
    L.adjugate i i = t * A.adjugate r r * B.det := by
  have h := adjugate_intertwining e L (Matrix.fromBlocks A 0 0 B) S T hST hTS hLS
  rw [adjugate_block_diagonal, hA, zero_smul] at h
  rw [h]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, hS, hT]
  ring

end Positivity
