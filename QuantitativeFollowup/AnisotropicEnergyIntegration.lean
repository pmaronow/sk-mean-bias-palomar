module
public import QuantitativeFollowup.AnisotropicEnergyRegularity
public import QuantitativeFollowup.AnisotropicWeightedShift
public import QuantitativeFollowup.AnisotropicInverseEnergyIntegrable
public import QuantitativeFollowup.AnisotropicSpinDisintegration

@[expose] public section

/-! The genuine finite-profile selected self-overlap posterior bound.
All model, density, inverse, integrability and equal-spin-mean obligations
are derived for arbitrary coupling scales and positive diagonal covariance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ} [Nonempty (Fin n)]
set_option maxHeartbeats 1800000

def anisotropicWeightedHessianEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (z : AnisotropicGaussianSpace n k) : ℝ :=
  (∑i,anisotropicPosteriorFeatureWeight s a i*(anisotropicPosteriorFeatureKernel s kernel i)^2*
    anisotropicSelfOverlapEnergy D s J (anisotropicPosteriorFeatureTime i) z)/((J.card : ℝ)/2)^2

theorem continuous_anisotropicWeightedHessianEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) : Continuous (anisotropicWeightedHessianEnergy D s a kernel J) := by
  unfold anisotropicWeightedHessianEnergy
  exact (continuous_finset_sum _ (fun i _ => continuous_const.mul
    (continuous_anisotropicSelfOverlapEnergy D s J _))).div_const _

theorem exists_anisotropicWeightedHessianEnergy_bound (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    ∃K : ℝ,0 ≤ K ∧ ∀z : AnisotropicGaussianSpace n k,|anisotropicWeightedHessianEnergy D s a kernel J z|≤K := by
  classical
  choose B hB hb using fun i : anisotropicPosteriorFeatureIndex k =>
    exists_anisotropicSelfOverlapEnergy_bound D s J (anisotropicPosteriorFeatureTime i)
  let C := ∑i,|anisotropicPosteriorFeatureWeight s a i*(anisotropicPosteriorFeatureKernel s kernel i)^2| * B i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hB i))
  refine ⟨C/((J.card : ℝ)/2)^2,div_nonneg hC (sq_nonneg _),fun z => ?_⟩
  unfold anisotropicWeightedHessianEnergy
  rw [abs_div,abs_of_nonneg (sq_nonneg ((J.card : ℝ)/2))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb i z) (abs_nonneg _)

theorem integrable_anisotropicWeightedHessianEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (hq : s.q 1=0) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (σ : Configuration n) :
    Integrable (anisotropicWeightedHessianEnergy D s a kernel J) (anisotropicSpinPosteriorLaw D s a σ) := by
  letI := anisotropicSpinPosteriorLaw_probability D s a hq σ
  obtain ⟨K,hK,hb⟩ := exists_anisotropicWeightedHessianEnergy_bound D s a kernel J
  apply Integrable.mono' (integrable_const K)
    (continuous_anisotropicWeightedHessianEnergy D s a kernel J).aestronglyMeasurable
  exact .of_forall fun z => by simpa only [Real.norm_eq_abs] using hb z

theorem anisotropicJoint_weightedSelfOverlap_variance_eq_slice (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (kernel : ℝ→ℝ) (J : Finset (Fin n))
    (σ : Configuration n) :
    variance (fun p : AnisotropicGaussianSpace n k×Configuration n =>
      anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J p.1) (anisotropicEuclideanJointLaw D s a)=
      variance (anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J) (anisotropicSpinPosteriorLaw D s a σ) := by
  have hf := boundedJets_anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J
  obtain ⟨K,hK,hb⟩ := hf.2 0
  apply variance_anisotropicEuclideanJointLaw_invariant D s a hq
    (fun _ => anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J)
    (fun _ => hf.1.continuous) K
    (fun _ z => by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb z)
    (fun η _ z => anisotropicEuclideanWeightedSelfOverlapScore_gauge D s a kernel J η z) σ

theorem anisotropicJoint_weightedSelfOverlap_variance_le_posterior_energy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1)
    (kernel : ℝ→ℝ) (J : Finset (Fin n)) (hJ : J.Nonempty) (σ : Configuration n) :
    variance (fun p : AnisotropicGaussianSpace n k×Configuration n =>
      anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J p.1) (anisotropicEuclideanJointLaw D s a) ≤
      ∫z,anisotropicWeightedHessianEnergy D s a kernel J z ∂anisotropicSpinPosteriorLaw D s a σ := by
  rw [anisotropicJoint_weightedSelfOverlap_variance_eq_slice D s a hq kernel J σ]
  apply (anisotropicSpinPosterior_weightedSelfOverlap_brascamp_lieb D s a hq ha kernel J σ).trans
  apply integral_mono
    (integrable_anisotropicSpinPosterior_inverse_energy D s a hq ha σ _
      (boundedJets_anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J))
    (integrable_anisotropicWeightedHessianEnergy D s a hq kernel J σ)
  intro z
  exact anisotropicEuclideanWeightedSelfOverlapScore_inverse_energy_le D s a ha kernel J hJ σ z

theorem anisotropicJoint_weightedSelfOverlap_variance_le_hessian_energy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1)
    (kernel : ℝ→ℝ) (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (fun p : AnisotropicGaussianSpace n k×Configuration n =>
      anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J p.1) (anisotropicEuclideanJointLaw D s a) ≤
      ∫p : AnisotropicGaussianSpace n k×Configuration n,
        anisotropicWeightedHessianEnergy D s a kernel J p.1 ∂anisotropicEuclideanJointLaw D s a := by
  classical
  let V := variance (fun p : AnisotropicGaussianSpace n k×Configuration n =>
    anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J p.1) (anisotropicEuclideanJointLaw D s a)
  calc
    _ = ∑σ : Configuration n,anisotropicSpinPosteriorMass D s a σ*V := by
      rw [←Finset.sum_mul,anisotropicSpinPosteriorMass_sum D s a hq,one_mul]
    _ ≤ ∑σ : Configuration n,anisotropicSpinPosteriorMass D s a σ*
        ∫z,anisotropicWeightedHessianEnergy D s a kernel J z ∂anisotropicSpinPosteriorLaw D s a σ :=
      Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
        (anisotropicJoint_weightedSelfOverlap_variance_le_posterior_energy D s a hq ha kernel J hJ σ)
        (anisotropicSpinPosteriorMass_pos D s a hq σ).le
    _ = _ := (integral_anisotropicEuclideanJointLaw_spin D s a hq _
      (fun σ => integrable_anisotropicWeightedHessianEnergy D s a hq kernel J σ)).symm

end QuantitativeFollowup
