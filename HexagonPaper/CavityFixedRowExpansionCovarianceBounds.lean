module
public import HexagonPaper.CavityFixedRowExpansionPairingContractions
public import QuantitativeFollowup.ScalarResponseNormBounds

@[expose] public section

/-! Bounded true covariance-column kernels used to separate the literal
all-profile marked contractions into their main and signed parts. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {n : ℕ}

theorem norm_cavityRestCovarianceColumn_le_one (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    ‖cavityRestCovarianceColumn D μ a p‖≤1 := by
  unfold cavityRestCovarianceColumn
  have hbound (ω : AnisotropicDisorderBrownianSample n) :
      ‖(cavityRestCenteredOverlapPath D μ a ω p) • cavityRestCenteredOverlapPath D μ a ω‖≤1 := by
    rw [norm_smul]
    exact (mul_le_mul
      (((cavityRestCenteredOverlapPath D μ a ω).norm_coe_le_norm p).trans
        (cavityRestCenteredOverlapPath_norm_le D μ a ω))
      (cavityRestCenteredOverlapPath_norm_le D μ a ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=anisotropicMeasureSampleLaw D μ a) (.of_forall hbound)

theorem norm_cavityRestCovarianceColumn_apply_le_one (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p r : Paper.Overlap) :
    ‖cavityRestCovarianceColumn D μ a p r‖≤1 :=
  ((cavityRestCovarianceColumn D μ a p).norm_coe_le_norm r).trans
    (norm_cavityRestCovarianceColumn_le_one D μ a p)

theorem integrable_cavityRestCovarianceColumn_kernel3 (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a B : ℝ) (hB : B≠0) (p : Paper.Overlap) :
    Integrable (fun r=>cavityRestCovarianceColumn D μ a p (min p r)*scalarResponseKernel3 B μ p r 0)
      (parisiFreeMeasure μ a) := by
  have hK : Continuous (fun r : Paper.Overlap=>scalarResponseKernel3 B μ p r 0) := by
    simpa only [Function.comp_def,id_eq] using (continuous_scalarResponseKernel3 B hB).comp
      (continuous_const.prodMk (continuous_const.prodMk (continuous_id.prodMk continuous_const)))
  have hSigma : Continuous (fun r : Paper.Overlap=>cavityRestCovarianceColumn D μ a p (min p r)) := by
    simpa only [Function.comp_def,id_eq] using
      (cavityRestCovarianceColumn D μ a p).continuous.comp (continuous_const.min continuous_id)
  have hmeas : AEStronglyMeasurable
      (fun r=>cavityRestCovarianceColumn D μ a p (min p r)*scalarResponseKernel3 B μ p r 0) (parisiFreeMeasure μ a) := by
    simpa only [Pi.mul_def] using (hSigma.mul hK).measurable.aestronglyMeasurable
  apply (integrable_const (scalarResponseKernelBound B)).mono' hmeas
  exact .of_forall fun r=>by
    rw [norm_mul]
    exact (mul_le_mul (norm_cavityRestCovarianceColumn_apply_le_one D μ a p (min p r))
      (scalarResponseKernel_bounds B μ p r 0).2.2.2.1 (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end HexagonPaper
