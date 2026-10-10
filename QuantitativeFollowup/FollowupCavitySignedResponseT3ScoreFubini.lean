module
public import FourPapersCommon.BoundedKernelExpectationAverage
public import QuantitativeFollowup.FollowupCavitySignedResponseMixedHessianIntegrals
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap

@[expose] public section

/-! Actual strict-future score contribution of T3 and its deterministic
kernel average, including atoms at the reveal time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def cavitySignedResponseT3Score (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (p : Paper.Overlap) : ℝ :=
  ∫l,cavitySignedScalarStrictFutureKernel β0 μ p l*
    (∫z,cavitySignedResponseScore D μ a p z*cavitySignedResponseSelfOverlap D μ l z.1
      ∂anisotropicMeasureSpinPathLaw D μ a) ∂parisiFreeMeasure μ a

theorem cavitySignedResponse_T3_score_eq_kernel_average (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (p : Paper.Overlap) :
    cavitySignedResponseT3Score D μ a β0 p=
      ∫z,cavitySignedResponseScore D μ a p z*
        anisotropicWeightedSelfOverlap D μ a (cavitySignedScalarStrictFutureKernel β0 μ p)
          Finset.univ z.1 ∂anisotropicMeasureSpinPathLaw D μ a := by
  have hmap : Measurable (fun l : Paper.Overlap=>(p,l)) := measurable_const.prodMk measurable_id
  have hK := (measurable_cavitySignedScalarStrictFutureKernel β0 hβ0 μ).comp hmap
  dsimp only [Function.comp_def] at hK
  have hKb (l : Paper.Overlap) : ‖cavitySignedScalarStrictFutureKernel β0 μ p l‖≤1 := by
    have hprod : Gamma β0 μ p*Gamma β0 μ l≤1 :=
      (mul_le_mul (scalarGamma_le_one β0 μ p p.property) (scalarGamma_le_one β0 μ l l.property)
        (scalarGamma_nonneg β0 μ l) zero_le_one).trans_eq (one_mul (1:ℝ))
    have hs := (cavitySignedScalarStrictFutureKernel_square_le β0 μ p l).trans hprod
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (cavitySignedScalarStrictFutureKernel β0 μ p l),
      abs_nonneg (cavitySignedScalarStrictFutureKernel β0 μ p l)]
  have hR := measurable_cavitySignedResponseScore D μ a p
  have hAmap : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      (z.1,z.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have hA := (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hAmap
  dsimp only [Function.comp_def] at hA
  have hh := bounded_kernel_expectation_average (parisiFreeMeasure μ a)
    (anisotropicMeasureSpinPathLaw D μ a) (cavitySignedScalarStrictFutureKernel β0 μ p)
    (cavitySignedResponseScore D μ a p) (fun l z=>cavitySignedResponseSelfOverlap D μ l z.1)
    hK hR hA 1 4 1 hKb (norm_cavitySignedResponseScore_le D μ a ha p)
    (fun l z=>norm_cavitySignedResponseSelfOverlap_le D μ l z.1) (by norm_num) (by norm_num)
  simpa only [cavitySignedResponseT3Score,anisotropicWeightedSelfOverlap,cavitySignedResponseSelfOverlap] using hh

theorem cavitySignedResponse_T3_score_original_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n) :
    |∫p,cavitySignedResponseT3Score D μ a β0 p ∂parisiFreeMeasure μ a|≤
      4*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  simp_rw [cavitySignedResponse_T3_score_eq_kernel_average D μ a β0 hβ0 ha]
  exact cavitySignedResponse_T3_future_score_integral_bound D μ a β0 hβ0 ha hμ hn

end QuantitativeFollowup
