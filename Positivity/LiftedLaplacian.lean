import Positivity.FullCoverDecomposition

namespace Positivity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
variable {V R : Type*} {n : V → Type*} [Fintype V] [∀ v, Fintype (n v)] [CommRing R]

theorem sigmaRectBlock_pullback (u v : V) (f : n u → n v) :
    sigmaRectBlock u v (Matrix.of (fun p q => if f p = q then (1 : R) else 0)) =
      ∑ p : n u, Matrix.single ⟨u, p⟩ ⟨v, f p⟩ 1 := by
  classical
  funext i j
  rcases i with ⟨i, p⟩
  rcases j with ⟨j, q⟩
  by_cases hi : i = u
  · subst i
    by_cases hj : j = v
    · subst j
      simp only [sigmaRectBlock, dite_true, Matrix.of_apply, Matrix.sum_apply]
      rw [Finset.sum_eq_single p]
      · simp [Matrix.single]
      · intro s _ hs
        simp [Matrix.single, hs, Ne.symm hs]
      · simp
    · have hj' (s : n u) : (⟨j, q⟩ : Sigma n) ≠ ⟨v, f s⟩ := fun h => hj (congrArg Sigma.fst h)
      simp [sigmaRectBlock, hj, Ne.symm hj, Matrix.sum_apply, Matrix.single]
  · have hi' (s : n u) : (⟨i, p⟩ : Sigma n) ≠ ⟨u, s⟩ := fun h => hi (congrArg Sigma.fst h)
    simp [sigmaRectBlock, hi, Ne.symm hi, Matrix.sum_apply, Matrix.single]

namespace FiniteFiberSystem
variable {E : Type*} [Fintype E]

abbrev LiftedEdge (F : FiniteFiberSystem V E) := Σ e, F.Fiber (F.src e)

noncomputable instance liftedEdgeFintype (F : FiniteFiberSystem V E) : Fintype F.LiftedEdge := by
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  infer_instance

def liftedSrc (F : FiniteFiberSystem V E) (a : F.LiftedEdge) : F.FullCoord := ⟨F.src a.1, a.2⟩
def liftedTgt (F : FiniteFiberSystem V E) (a : F.LiftedEdge) : F.FullCoord :=
  ⟨F.tgt a.1, F.fiberMap a.1 a.2⟩

theorem fullGraphMatrix_eq_lifted (F : FiniteFiberSystem V E) :
    F.fullGraphMatrix = scalarLaplacian F.liftedSrc F.liftedTgt
      (fun a => (MvPolynomial.X a.1 : MvPolynomial E ℚ)) := by
  classical
  letI : ∀ v, Fintype (F.Fiber v) := F.fiberFintype
  unfold fullGraphMatrix blockLaplacian scalarLaplacian
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  have hid : (1 : Matrix (F.Fiber (F.src e)) _ (MvPolynomial E ℚ)) =
      Matrix.of (fun p q => if p = q then 1 else 0) := by
    funext p q
    simp [Matrix.one_apply]
  have hp : F.fullLocalPullback e =
      Matrix.of (fun p q => if F.fiberMap e p = q then 1 else 0) := by
    funext p q
    simp [fullLocalPullback, fullPullback]
  rw [hid, hp, sigmaRectBlock_pullback, sigmaRectBlock_pullback,
    ← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  funext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, liftedSrc, liftedTgt]
  split_ifs <;> rfl

end FiniteFiberSystem
end Positivity
