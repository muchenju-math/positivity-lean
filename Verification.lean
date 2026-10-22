import Positivity

/-!
Kernel dependency audit for the principal manuscript results.
Run with `lake env lean Verification.lean` after `lake build`.
Expected axioms: only `propext`, `Classical.choice`, and `Quot.sound`.
-/

#print axioms Positivity.loopDeterminantDerivative
#print axioms Positivity.loopCharacteristicDerivative
#print axioms Positivity.FiniteFiberSystem.fullGraphMatrix_constant_intertwine
#print axioms Positivity.FiniteFiberSystem.laplacianCharacteristicFactorization
#print axioms Positivity.FiniteFiberSystem.arborescence_sum_identity
#print axioms Positivity.loopCoefficientRecurrence
#print axioms Positivity.eliminationCoefficientRecurrence
#print axioms Positivity.balancedCoefficient_nonnegative
#print axioms Positivity.quotientDeterminant_coeff_nonnegative
#print axioms Positivity.directed_matrix_tree
#print axioms Positivity.FiniteFiberSystem.coveringLaplacian_det
#print axioms Positivity.FiniteFiberSystem.covering_tree_identity
#print axioms Positivity.FiniteFiberSystem.covering_arborescence_nonnegative
#print axioms Positivity.FiniteFiberSystem.arborescenceRatio_nonnegative_integer_polynomial
#print axioms Positivity.FiniteFiberSystem.arborescenceRatio_eq_normalized_determinant
