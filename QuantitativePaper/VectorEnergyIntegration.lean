module
public import QuantitativePaper.VectorEnergyRegularity
public import QuantitativePaper.VectorWeightedShift
public import QuantitativePaper.VectorInverseEnergyIntegrable

@[expose] public section

/-! The actual finite-profile integrated posterior variance inequality.
Every energy integral is genuine; finite-spin disintegration and the actual
gauge symmetry remove the between-spin term. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

def vectorWeightedHessianEnergy {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (kernel : ℝ → ℝ) (σ : Configuration n) (z : VectorGaussianSpace n k) : ℝ :=
  (∑ i,vectorPosteriorFeatureWeight s a i*(vectorPosteriorFeatureKernel s kernel i)^2*
    vectorSpinHessianEnergy s β t (k+2-vectorPosteriorFeatureTime i) σ
      (vectorEuclideanStateLinear s β t (vectorPosteriorFeatureTime i) z))/(n : ℝ)^2

theorem continuous_vectorWeightedHessianEnergy {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (kernel : ℝ → ℝ) (σ : Configuration n) :
    Continuous (vectorWeightedHessianEnergy (n := n) s β t a kernel σ) := by
  unfold vectorWeightedHessianEnergy
  exact (continuous_finset_sum _ (fun i _ => continuous_const.mul
    ((continuous_vectorSpinHessianEnergy s β t _ σ).comp
      (vectorEuclideanStateLinear s β t _).continuous))).div_const _

theorem exists_vectorWeightedHessianEnergy_bound {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (kernel : ℝ → ℝ) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ (σ : Configuration n) (z : VectorGaussianSpace n k),
      |vectorWeightedHessianEnergy s β t a kernel σ z| ≤ K := by
  classical
  choose B hB hBound using fun i : vectorPosteriorFeatureIndex k =>
    exists_vectorSpinHessianEnergy_bound (n := n) s β t (k+2-vectorPosteriorFeatureTime i)
  let C := ∑ i,|vectorPosteriorFeatureWeight s a i*(vectorPosteriorFeatureKernel s kernel i)^2| * B i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hB i))
  refine ⟨C/(n : ℝ)^2,div_nonneg hC (sq_nonneg _),fun σ z => ?_⟩
  unfold vectorWeightedHessianEnergy
  rw [abs_div,abs_of_nonneg (sq_nonneg (n : ℝ))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hBound i σ (vectorEuclideanStateLinear s β t _ z)) (abs_nonneg _)

theorem integrable_vectorWeightedHessianEnergy {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) (kernel : ℝ → ℝ) (σ : Configuration n) :
    Integrable (vectorWeightedHessianEnergy s β t a kernel σ) (vectorSpinPosteriorLaw s β t a σ) := by
  letI := vectorSpinPosteriorLaw_probability s β t a hq σ
  obtain ⟨K,hK,hBound⟩ := exists_vectorWeightedHessianEnergy_bound (n := n) s β t a kernel
  apply Integrable.mono' (integrable_const K)
    (continuous_vectorWeightedHessianEnergy s β t a kernel σ).aestronglyMeasurable
  exact .of_forall fun z => by simpa only [Real.norm_eq_abs] using hBound σ z

theorem vectorJoint_weightedOverlap_variance_le_posterior_energy {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β t a : ℝ) (hβ : β≠0) (ht : t < 1)
    (hq : s.q 1=0) (ha : a ≤ s.m 1) (kernel : ℝ → ℝ) (σ : Configuration n) :
    variance (fun p : VectorGaussianSpace n k × Configuration n =>
      vectorEuclideanWeightedOverlapScore s β t a kernel p.2 p.1) (vectorEuclideanJointLaw s β t a) ≤
      ∫z,vectorWeightedHessianEnergy s β t a kernel σ z ∂vectorSpinPosteriorLaw s β t a σ := by
  apply (vectorJoint_weightedOverlap_brascamp_lieb s β t a hq ha kernel σ).trans
  apply integral_mono
    (integrable_vectorSpinPosterior_inverse_energy s β t a hq ha σ _
      (boundedJets_vectorEuclideanWeightedOverlapScore s β t a kernel σ))
    (integrable_vectorWeightedHessianEnergy s β t a hq kernel σ)
  intro z
  simpa only [vectorWeightedHessianEnergy,vectorSpinHessianEnergy,vectorEuclideanMagnetization] using
    vectorEuclideanWeightedOverlapScore_inverse_energy_le hn s β t a hβ ht ha kernel σ z

theorem vectorJoint_weightedOverlap_variance_le_hessian_energy {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β t a : ℝ) (hβ : β≠0) (ht : t < 1)
    (hq : s.q 1=0) (ha : a ≤ s.m 1) (kernel : ℝ → ℝ) :
    variance (fun p : VectorGaussianSpace n k × Configuration n =>
      vectorEuclideanWeightedOverlapScore s β t a kernel p.2 p.1) (vectorEuclideanJointLaw s β t a) ≤
      ∫p : VectorGaussianSpace n k × Configuration n,
        vectorWeightedHessianEnergy s β t a kernel p.2 p.1 ∂vectorEuclideanJointLaw s β t a := by
  classical
  let V := variance (fun p : VectorGaussianSpace n k × Configuration n =>
      vectorEuclideanWeightedOverlapScore s β t a kernel p.2 p.1) (vectorEuclideanJointLaw s β t a)
  calc
    _ = ∑σ : Configuration n,vectorSpinPosteriorMass s β t a σ*V := by
      rw [←Finset.sum_mul,vectorSpinPosteriorMass_sum s β t a hq,one_mul]
    _ ≤ ∑σ : Configuration n,vectorSpinPosteriorMass s β t a σ*
        ∫z,vectorWeightedHessianEnergy s β t a kernel σ z ∂vectorSpinPosteriorLaw s β t a σ :=
      Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
        (vectorJoint_weightedOverlap_variance_le_posterior_energy hn s β t a hβ ht hq ha kernel σ)
        (vectorSpinPosteriorMass_pos s β t a hq σ).le
    _ = _ := (integral_vectorEuclideanJointLaw_spin s β t a hq _
      (integrable_vectorWeightedHessianEnergy s β t a hq kernel)).symm

end QuantitativePaper
