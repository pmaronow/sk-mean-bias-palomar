module
public import QuantitativeFollowup.AnisotropicPosterior
public import QuantitativePaper.VectorPosteriorJets

@[expose] public section

/-! Actual global posterior jet bounds for the anisotropic Gaussian model.
The constants are derived from its finite affine-spin recursion. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1500000

theorem boundedPositiveJets_anisotropicFinitePotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) : BoundedPositiveJets (anisotropicFinitePotential D s i) := by
  refine ⟨contDiff_anisotropicFinitePotential D s i,?_⟩
  intro j hj
  obtain ⟨_,K,hK,hb⟩ := anisotropicFinitePotential_smooth_bounded_jets D s j i
  exact ⟨K^j,pow_nonneg (zero_le_one.trans hK) _,fun P => hb j hj le_rfl P⟩

theorem boundedPositiveJets_anisotropicEuclideanHistoryPotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) : BoundedPositiveJets (anisotropicEuclideanHistoryPotential D s i) :=
  (boundedPositiveJets_anisotropicFinitePotential D s (k+2-i)).comp_linear
    (anisotropicEuclideanStateLinear D s i)

theorem boundedPositiveJets_anisotropicPosteriorCorrection (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (σ : Configuration n) :
    BoundedPositiveJets (anisotropicPosteriorCorrection D s a σ) := by
  have he : anisotropicPosteriorCorrection D s a σ = fun z =>
      -anisotropicEuclideanTerminalLinear D s σ z+(s.m 1-a)*anisotropicEuclideanHistoryPotential D s 1 z+
      (∑i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*anisotropicEuclideanHistoryPotential D s (i+2) z)+
      Real.log (anisotropicFiniteOuterPartition D s a) := by
    funext z
    unfold anisotropicPosteriorCorrection anisotropicPosteriorPotential
    ring
  rw [he]
  have h0 := (boundedPositiveJets_linear (anisotropicEuclideanTerminalLinear D s σ)).neg
  have h1 := (boundedPositiveJets_anisotropicEuclideanHistoryPotential D s 1).const_mul (s.m 1-a)
  have hs := boundedPositiveJets_finite_sum (Finset.range k)
    (fun i z => (s.m (i+2)-s.m (i+1))*anisotropicEuclideanHistoryPotential D s (i+2) z)
    (fun i _ => (boundedPositiveJets_anisotropicEuclideanHistoryPotential D s (i+2)).const_mul _)
  exact ((h0.add h1).add hs).add (boundedPositiveJets_const _)

theorem exists_anisotropicPosteriorPotential_jet_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (σ : Configuration n) {j : ℕ} (hj : 3 ≤ j) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ z : AnisotropicGaussianSpace n k,
      ‖iteratedFDeriv ℝ j (anisotropicPosteriorPotential D s a σ) z‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := (boundedPositiveJets_anisotropicPosteriorCorrection D s a σ).2 j (by omega)
  refine ⟨B,hB,fun z => ?_⟩
  have he : anisotropicPosteriorPotential D s a σ =
      fun z => standardGaussianPotential z+anisotropicPosteriorCorrection D s a σ z := by
    funext z
    unfold anisotropicPosteriorCorrection
    ring
  rw [he]
  change ‖iteratedFDeriv ℝ j (standardGaussianPotential+anisotropicPosteriorCorrection D s a σ) z‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_standardGaussianPotential.of_le (by simp)).contDiffAt
    ((boundedPositiveJets_anisotropicPosteriorCorrection D s a σ).1.of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (by
    rw [norm_iteratedFDeriv_standardGaussianPotential_eq_zero hj,zero_add]
    exact hb z)

end QuantitativeFollowup
