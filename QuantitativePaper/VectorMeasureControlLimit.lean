module
public import QuantitativePaper.VectorFiniteControlGap
public import QuantitativePaper.VectorFeedbackControl
public import QuantitativePaper.VectorMeasureEndpoints
public import FourPapersCommon.UniformIntegralDifference
public import FRSB.GridMeasureIdentification

@[expose] public section

/-! The actual arbitrary-profile control gap and its uniform dyadic
integral limit. Its integrability follows from genuine finite-cell Itô,
not from assigning Bochner values to an unproved integrable expression. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureControlGap (μ : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorTerminalPotential n β t sample.1
      (vectorControlledState ((1-t)*β^2) μ A 1 sample)-
    vectorMeasurePotential μ β t sample.1 0-
    vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample

theorem measurable_vectorMeasureControlGap (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Measurable (vectorMeasureControlGap μ β t A) := by
  have hT := (contDiff_vectorTerminalPotential_joint n β t 0).continuous.measurable.comp
    (measurable_fst.prodMk ((measurable_vectorControlledState ((1-t)*β^2) μ A hA).of_uncurry_left (x := 1)))
  have hU := (continuous_vectorMeasurePotential_joint (n := n) μ β t ht).measurable.comp
    (show Measurable (fun sample : VectorDisorderBrownianSample n => (sample.1,(0 : Field n))) from by fun_prop)
  have hC := ((measurable_vectorParisiControlCost ((1-t)*β^2) μ A hA).stronglyMeasurable.integral_prod_left'
    (μ := nonnegativeLebesgueMeasure.restrict (Ioc 0 1))).measurable
  exact (hT.sub hU).sub hC

theorem vectorMeasureControlGap_dyadic_abs_sub_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (j : ℕ)
    (sample : VectorDisorderBrownianSample n) :
    |vectorMeasureControlGap μ β t A sample-
      vectorFiniteControlGap (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t μ A sample|≤
        (4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j := by
  have he : vectorMeasureControlGap μ β t A sample-
      vectorFiniteControlGap (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t μ A sample=
      vectorDyadicPotential μ β t j sample.1 0-vectorMeasurePotential μ β t sample.1 0 := by
    unfold vectorMeasureControlGap vectorFiniteControlGap vectorDyadicPotential
    ring
  rw [he]
  exact vectorDyadicPotential_limit_abs_sub_le μ β t ht j sample.1 0

theorem integrable_vectorMeasureControlGap (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hA : IsVectorParisiControl A) :
    Integrable (vectorMeasureControlGap μ β t A) (vectorDisorderBrownianMeasure n) := by
  apply integrable_of_uniform_sub_bound
    (integrable_vectorFiniteControlGap (Paper.parisiGridRSBScheme μ (vectorDyadicIndex 0)) β t hβ ht μ A hA)
    (measurable_vectorMeasureControlGap μ β t ht.le A hA).aestronglyMeasurable
    (4*(n : ℝ)*((1-t)*β^2)*(1/2 : ℝ)^0)
  exact vectorMeasureControlGap_dyadic_abs_sub_le μ β t ht.le A 0

theorem integral_vectorMeasureControlGap_dyadic_abs_sub_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hA : IsVectorParisiControl A) (j : ℕ) :
    |(∫sample,vectorMeasureControlGap μ β t A sample ∂vectorDisorderBrownianMeasure n)-
      (∫sample,vectorFiniteControlGap (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t μ A sample
        ∂vectorDisorderBrownianMeasure n)|≤(4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j :=
  integral_sub_le_uniform_bound (integrable_vectorMeasureControlGap μ β t hβ ht A hA)
    (integrable_vectorFiniteControlGap _ β t hβ ht μ A hA) _
    (vectorMeasureControlGap_dyadic_abs_sub_le μ β t ht.le A j)

theorem tendsto_integral_vectorFiniteControlGap_dyadic (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hA : IsVectorParisiControl A) :
    Tendsto (fun j=>∫sample,vectorFiniteControlGap (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        β t μ A sample ∂vectorDisorderBrownianMeasure n) atTop
      (𝓝 (∫sample,vectorMeasureControlGap μ β t A sample ∂vectorDisorderBrownianMeasure n)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hh : Tendsto (fun j : ℕ=>(4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1)).const_mul
        (4*(n : ℝ)*((1-t)*β^2))
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with j hj
  rw [Real.dist_eq,abs_sub_comm]
  exact (integral_vectorMeasureControlGap_dyadic_abs_sub_le μ β t hβ ht A hA j).trans_lt hj

theorem integral_vectorMeasureControlGap_le_zero (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hA : IsVectorParisiControl A) :
    (∫sample,vectorMeasureControlGap μ β t A sample ∂vectorDisorderBrownianMeasure n)≤0 := by
  have hL := tendsto_integral_vectorFiniteControlGap_dyadic μ β t hβ ht A hA
  have hD := ((Paper.tendsto_parisiCDFDistance_grid μ).comp tendsto_vectorDyadicIndex).const_mul
    (((1-t)*β^2)/2*(n : ℝ))
  simp only [mul_zero] at hD
  apply le_of_tendsto_of_tendsto hL hD
  exact Eventually.of_forall (fun j=>by
    have hh := vectorFiniteControlGap_integral_le (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      β t hβ ht μ A hA
    simpa only [FRSB.parisiSchemeMeasure_grid_eq,Function.comp_def] using hh)

end QuantitativePaper
