module
public import QuantitativeFollowup.QuantileWindowKernel

@[expose] public section

/-! The quantile-window density is supported in the actual past and above
its cumulative-mass threshold, including partial terminal atoms. -/
noncomputable section
open Set MeasureTheory Filter Paper
open scoped ENNReal NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem parisiFreeQuantile_monotone (μ : ParisiMeasure) (s : ℝ) :
    Monotone (parisiFreeQuantile μ s) := by
  intro v w hvw
  exact parisiQuantile_monotone μ (add_le_add le_rfl hvw)

theorem ae_quantileWindowKernel_property (μ : ParisiMeasure) (s v x : ℝ)
    (p : Overlap→Prop) (hp : MeasurableSet {q | p q})
    (h : ∀w∈Ioc (max 0 (v-x)) v,p (parisiFreeQuantile μ s w)) :
    ∀ᵐq ∂parisiFreeMeasure μ s,quantileWindowKernel μ s v x q≠0→p q := by
  have hw : ∀ᵐq ∂quantileWindowMeasure μ s v x,p q := by
    apply (ae_map_iff (parisiFreeQuantile_measurable μ s).aemeasurable hp).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    exact h w hw
  filter_upwards [Measure.ae_rnDeriv_ne_zero_imp_of_ae (parisiFreeMeasure μ s) hw] with q hq hκ
  apply hq
  intro hz
  apply hκ
  simp only [quantileWindowKernel,hz,ENNReal.toReal_zero,min_eq_right zero_le_one,zero_div]

theorem ae_quantileWindowKernel_cdf_lower (μ : ParisiMeasure) (s v x : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hv : v≤1-s) :
    ∀ᵐq ∂parisiFreeMeasure μ s,quantileWindowKernel μ s v x q≠0→
      s+max 0 (v-x)≤parisiCDF μ q := by
  apply ae_quantileWindowKernel_property μ s v x
  · exact measurableSet_le measurable_const
      ((parisiCDF_measurable μ).comp measurable_subtype_coe)
  · intro w hw
    exact (add_le_add le_rfl hw.1.le).trans
      (parisiCDF_freeQuantile_lower μ s hs
        ⟨(le_max_left 0 (v-x)).trans_lt hw.1,hw.2.trans hv⟩)

theorem ae_quantileWindowKernel_past (μ : ParisiMeasure) (s v x : ℝ) :
    ∀ᵐq ∂parisiFreeMeasure μ s,quantileWindowKernel μ s v x q≠0→
      q≤parisiFreeQuantile μ s v := by
  apply ae_quantileWindowKernel_property μ s v x
  · exact measurableSet_Iic
  · intro w hw
    exact parisiFreeQuantile_monotone μ s hw.2

theorem integrable_quantileWindowKernel (μ : ParisiMeasure) (s v x : ℝ) (hx : 0<x) :
    Integrable (quantileWindowKernel μ s v x) (parisiFreeMeasure μ s) := by
  apply (integrable_const (1/x)).mono' (measurable_quantileWindowKernel μ s v x).aestronglyMeasurable
  exact .of_forall fun q=>by
    rw [Real.norm_of_nonneg (quantileWindowKernel_nonneg_le μ s v x hx q).1]
    exact (quantileWindowKernel_nonneg_le μ s v x hx q).2

theorem integral_quantileWindowKernel_le_one (μ : ParisiMeasure) (s v x : ℝ)
    (hv : v≤1-s) (hx : 0<x) :
    (∫q,quantileWindowKernel μ s v x q ∂parisiFreeMeasure μ s)≤1 := by
  rw [integral_quantileWindowKernel μ s v x hv]
  apply (div_le_one₀ hx).mpr
  apply max_le
  · have h:=le_max_right (0:ℝ) (v-x)
    linarith
  · exact hx.le

end QuantitativeFollowup
