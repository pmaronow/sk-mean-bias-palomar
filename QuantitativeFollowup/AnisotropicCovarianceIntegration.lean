module
public import QuantitativeFollowup.AnisotropicCovarianceRegularity
public import QuantitativeFollowup.AnisotropicEnergyIntegration

@[expose] public section

/-! The second genuine selected-coordinate variance inequality. Both
energies are integrated under the actual anisotropic posterior/history law;
all integrability follows from constructed finite-profile bounds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ} [Nonempty (Fin n)]
set_option maxHeartbeats 1800000

def anisotropicWeightedCovarianceEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (z : AnisotropicGaussianSpace n k) : ℝ :=
  (∑i,anisotropicPosteriorFeatureWeight s a i*(anisotropicPosteriorFeatureKernel s kernel i)^2*
    anisotropicSelfOverlapCovarianceEnergy D s J (anisotropicPosteriorFeatureTime i) z)/((J.card : ℝ)/2)^2

theorem continuous_anisotropicWeightedCovarianceEnergy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    Continuous (anisotropicWeightedCovarianceEnergy D s a kernel J) := by
  unfold anisotropicWeightedCovarianceEnergy
  exact (continuous_finset_sum _ (fun i _ => continuous_const.mul
    (continuous_anisotropicSelfOverlapCovarianceEnergy D s J _))).div_const _

theorem exists_anisotropicWeightedCovarianceEnergy_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    ∃K : ℝ,0 ≤ K ∧ ∀z : AnisotropicGaussianSpace n k,|anisotropicWeightedCovarianceEnergy D s a kernel J z| ≤ K := by
  let B := (n : ℝ)*(‖anisotropicSelectedInsertion J‖*Real.sqrt (J.card : ℝ))^2
  let C := ∑i,|anisotropicPosteriorFeatureWeight s a i*(anisotropicPosteriorFeatureKernel s kernel i)^2| * B
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) hB)
  refine ⟨C/((J.card : ℝ)/2)^2,div_nonneg hC (sq_nonneg _),fun z => ?_⟩
  unfold anisotropicWeightedCovarianceEnergy
  rw [abs_div,abs_of_nonneg (sq_nonneg ((J.card : ℝ)/2))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (anisotropicSelfOverlapCovarianceEnergy_bound D s J _ z) (abs_nonneg _)

theorem integrable_anisotropicWeightedCovarianceEnergy_joint (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    Integrable (fun p : AnisotropicGaussianSpace n k×Configuration n =>
      anisotropicWeightedCovarianceEnergy D s a kernel J p.1) (anisotropicEuclideanJointLaw D s a) := by
  obtain ⟨K,hK,hb⟩ := exists_anisotropicWeightedCovarianceEnergy_bound D s a kernel J
  apply Integrable.mono' (integrable_const K)
    ((continuous_anisotropicWeightedCovarianceEnergy D s a kernel J).comp continuous_fst).aestronglyMeasurable
  exact .of_forall fun p => by simpa only [Real.norm_eq_abs,Function.comp_def] using hb p.1

theorem integrable_anisotropicWeightedHessianEnergy_joint (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    Integrable (fun p : AnisotropicGaussianSpace n k×Configuration n =>
      anisotropicWeightedHessianEnergy D s a kernel J p.1) (anisotropicEuclideanJointLaw D s a) := by
  obtain ⟨K,hK,hb⟩ := exists_anisotropicWeightedHessianEnergy_bound D s a kernel J
  apply Integrable.mono' (integrable_const K)
    ((continuous_anisotropicWeightedHessianEnergy D s a kernel J).comp continuous_fst).aestronglyMeasurable
  exact .of_forall fun p => by simpa only [Real.norm_eq_abs,Function.comp_def] using hb p.1

theorem anisotropicWeightedHessianEnergy_le_covariance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (kernel : ℝ→ℝ) (J : Finset (Fin n))
    (z : AnisotropicGaussianSpace n k) :
    anisotropicWeightedHessianEnergy D s a kernel J z ≤ anisotropicWeightedCovarianceEnergy D s a kernel J z := by
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (anisotropicSelfOverlapEnergy_le_covariance D s J _ z)
    (mul_nonneg (anisotropicPosteriorFeatureWeight_nonneg s a ha i) (sq_nonneg _))

theorem anisotropicJoint_weightedSelfOverlap_variance_bounds (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1)
    (kernel : ℝ→ℝ) (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (fun p : AnisotropicGaussianSpace n k×Configuration n =>
      anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J p.1) (anisotropicEuclideanJointLaw D s a) ≤
      ∫p : AnisotropicGaussianSpace n k×Configuration n,anisotropicWeightedHessianEnergy D s a kernel J p.1
        ∂anisotropicEuclideanJointLaw D s a ∧
    (∫p : AnisotropicGaussianSpace n k×Configuration n,anisotropicWeightedHessianEnergy D s a kernel J p.1
        ∂anisotropicEuclideanJointLaw D s a) ≤
      ∫p : AnisotropicGaussianSpace n k×Configuration n,anisotropicWeightedCovarianceEnergy D s a kernel J p.1
        ∂anisotropicEuclideanJointLaw D s a :=
  ⟨anisotropicJoint_weightedSelfOverlap_variance_le_hessian_energy D s a hq ha kernel J hJ,
    integral_mono (integrable_anisotropicWeightedHessianEnergy_joint D s a kernel J)
      (integrable_anisotropicWeightedCovarianceEnergy_joint D s a kernel J)
      (fun p => anisotropicWeightedHessianEnergy_le_covariance D s a ha kernel J p.1)⟩

end QuantitativeFollowup
