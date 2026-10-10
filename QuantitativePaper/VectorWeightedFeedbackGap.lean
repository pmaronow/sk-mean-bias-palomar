module
public import QuantitativePaper.VectorWeightedControlGap

@[expose] public section

/-! Genuine feedback attainment with every bounded initial-filtration
weight. No weighted verification identity is supplied as a premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integral_vectorFiniteControlGap_feedback_weighted_abs_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (j : ℕ)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    |∫sample,Z sample*vectorFiniteControlGap (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t μ
      (vectorMeasureFeedbackControl μ β t ht.le) sample ∂vectorDisorderBrownianMeasure n|≤
      (C : ℝ)*((1-t)*β^2)/2*((vectorDyadicGradientError n β t j)^2+
        (n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiGridMeasure μ (vectorDyadicIndex j))) := by
  let s := Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let A := vectorMeasureFeedbackControl (n := n) μ β t ht.le
  let ε := vectorDyadicGradientError n β t j
  let c := (1-t)*β^2
  let w : ℝ≥0→VectorDisorderBrownianSample n→ℝ := fun r sample=>
    vectorFiniteControlSource s β t μ A r sample-vectorParisiControlCost c μ A r sample
  let g : ℝ≥0→ℝ := fun r=>c/2*(ε^2+(n : ℝ)*|Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r|)
  have hgi : IntegrableOn g (Ioc 0 1) nonnegativeLebesgueMeasure :=
    ((integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1) (C := ε^2)).add
      ((integrableOn_nnreal_CDF_abs_sub μ (Paper.parisiSchemeMeasure s)).const_mul (n : ℝ))).const_mul (c/2)
  have hg : (∫r in Ioc 0 1,g r ∂nonnegativeLebesgueMeasure)=
      c/2*(ε^2+(n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s)) := by
    unfold g
    rw [integral_const_mul,integral_add
      (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1) (C := ε^2))
      ((integrableOn_nnreal_CDF_abs_sub μ (Paper.parisiSchemeMeasure s)).const_mul (n : ℝ)),
      integral_const_mul,integral_nnreal_CDF_abs_sub]
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,nonnegativeLebesgueMeasure_Ioc,
      NNReal.coe_one,NNReal.coe_zero,sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul]
  have hh := vectorBoundedSource_expected_weighted_integral_norm_le w Z C hC g hgi
    (fun r hr sample=>by
      rw [Real.norm_eq_abs]
      exact vectorFiniteControlSource_sub_cost_abs_le s β t ht.le μ A r sample ε
        (vectorDyadicGradientError_nonneg n β t ht.le j)
        (vectorFiniteControlGradient_feedback_sub_le μ β t ht.le j r hr.2 sample))
  rw [hg] at hh
  rw [integral_vectorFiniteControlGap_weighted_eq s β t hβ ht μ A
    (isVectorParisiControl_vectorMeasureFeedbackControl μ β t ht.le) Z hZ C hC]
  rw [←Real.norm_eq_abs]
  convert! hh using 1
  dsimp only [c,ε,s]
  rw [FRSB.parisiSchemeMeasure_grid_eq]
  ring

theorem integral_vectorMeasureControlGap_feedback_weighted_eq_zero (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    (∫sample,Z sample*vectorMeasureControlGap μ β t (vectorMeasureFeedbackControl μ β t ht.le) sample
      ∂vectorDisorderBrownianMeasure n)=0 := by
  have hA := isVectorParisiControl_vectorMeasureFeedbackControl (n := n) μ β t ht.le
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  have hL := (tendsto_integral_vectorFiniteControlGap_dyadic_weighted μ β t hβ ht _ hA Z hZg C hC).abs
  have hD := (Paper.tendsto_parisiCDFDistance_grid μ).comp tendsto_vectorDyadicIndex
  have hE := tendsto_vectorDyadicGradientError n β t
  have hR : Tendsto (fun j=>(C : ℝ)*((1-t)*β^2)/2*((vectorDyadicGradientError n β t j)^2+
      (n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiGridMeasure μ (vectorDyadicIndex j)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,add_zero] using
      ((hE.pow 2).add (hD.const_mul (n : ℝ))).const_mul ((C : ℝ)*((1-t)*β^2)/2)
  have hz := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall (fun j=>
    integral_vectorFiniteControlGap_feedback_weighted_abs_le μ β t hβ ht j Z hZ C hC))
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

end QuantitativePaper
