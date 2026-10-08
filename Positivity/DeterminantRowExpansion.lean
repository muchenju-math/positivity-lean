import Mathlib

namespace Positivity
variable {I J R : Type*} [Fintype I] [Fintype J] [DecidableEq I] [CommRing R]

theorem determinant_row_sum (M : I → J → I → R) :
    Matrix.det (fun i j => ∑ a : J, M i a j) =
      ∑ f : I → J, Matrix.det (fun i j => M i (f i) j) := by
  have h := (Matrix.detRowAlternating (R := R) (n := I)).toMultilinearMap.map_sum M
  convert h using 1
  congr 1
  funext i j
  simp
  rfl

theorem determinant_row_sum_dependent {J : I → Type*} [∀ i, Fintype (J i)]
    (M : ∀ i, J i → I → R) :
    Matrix.det (fun i j => ∑ a : J i, M i a j) =
      ∑ f : ∀ i, J i, Matrix.det (fun i j => M i (f i) j) := by
  have h := (Matrix.detRowAlternating (R := R) (n := I)).toMultilinearMap.map_sum M
  convert h using 1
  congr 1
  funext i j
  simp
  rfl

end Positivity
