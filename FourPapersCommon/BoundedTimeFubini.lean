module
public import QuantitativePaper.VectorNonnegativeTimeIntegral

@[expose] public section

/-! Exact finite-horizon Fubini for any genuine probability law and a
bounded jointly measurable time/sample source. -/
noncomputable section
open Set MeasureTheory StochasticCalculus
open scoped NNReal
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω]

theorem bounded_nnreal_time_fubini (P : Measure Ω) [IsProbabilityMeasure P]
    (w : ℝ≥0→Ω→ℝ) (hw : Measurable (Function.uncurry w))
    (T K : ℝ≥0) (hb : ∀r≤T,∀ω,‖w r ω‖≤K) :
    Integrable (Function.uncurry w) ((nonnegativeLebesgueMeasure.restrict (Ioc 0 T)).prod P) ∧
    (∫ω,(∫r in Ioc 0 T,w r ω∂nonnegativeLebesgueMeasure)∂P)=
      ∫r in Ioc 0 T,(∫ω,w r ω∂P)∂nonnegativeLebesgueMeasure := by
  let μ:=nonnegativeLebesgueMeasure.restrict (Ioc (0:ℝ≥0) T)
  letI : IsFiniteMeasure μ:=⟨by simpa only [μ,Measure.restrict_apply_univ] using
    (lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T))⟩
  have hbound : ∀ᵐz∂μ.prod P,‖w z.1 z.2‖≤K := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hw.norm measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact .of_forall (hb r hr.2)
  have hi : Integrable (Function.uncurry w) (μ.prod P):=
    (integrable_const (K:ℝ)).mono' hw.aestronglyMeasurable hbound
  exact ⟨hi,(integral_integral_swap hi).symm⟩

end FourPapersCommon
