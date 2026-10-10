module
public import QuantitativePaper.VectorTiltedIntegral
public import FourPapersCommon.ExpWeightedConvergence

@[expose] public section

/-! Genuine convergence of normalized fractional expectations as actual
finite dyadic potentials approach the arbitrary-profile potential. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem tendsto_vectorDyadicOuterPartition (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    Tendsto (fun j=>vectorOuterPartition (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) atTop
      (𝓝 (vectorMeasureOuterPartition (n:=n) μ β t a)) := by
  have hε : Tendsto (fun j : ℕ=>(4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2)
        (by norm_num : (1/2 : ℝ)<1)).const_mul (4*(n : ℝ)*((1-t)*β^2))
  have he := tendsto_integral_exp_mul_of_uniform_error
    (fun p : Couplings n×ℝ=>vectorMeasurePotential μ β t p 0)
    (fun j p=>vectorDyadicPotential μ β t j p 0) (fun _ _=>(1 : ℝ)) (fun _=>(1 : ℝ))
    a 1 zero_le_one _ hε
    (fun j=>by
      simpa only [Function.comp_def,id_eq,vectorDyadicPotential] using
        (measurable_vectorRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
          (vectorDyadicIndex j+3)).comp (measurable_id.prodMk measurable_const))
    (fun _=>measurable_const) (integrable_exp_vectorMeasurePotential μ β t ht a 0)
    (fun j p=>vectorDyadicPotential_limit_abs_sub_le μ β t ht j p 0)
    (fun _ _=>by norm_num) (.of_forall fun _=>tendsto_const_nhds)
  simpa only [mul_one,vectorOuterPartition,vectorMeasureOuterPartition,vectorDyadicPotential] using he

theorem tendsto_integral_vectorDyadicTilt_bounded (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (Fj : ℕ→VectorDisorderBrownianSample n→ℝ)
    (F : VectorDisorderBrownianSample n→ℝ) (C : ℝ) (hC : 0≤C)
    (hFj : ∀ j,Measurable (Fj j)) (hB : ∀ j sample,‖Fj j sample‖≤C)
    (hF : ∀ᵐsample ∂vectorDisorderBrownianMeasure n,
      Tendsto (fun j=>Fj j sample) atTop (𝓝 (F sample))) :
    Tendsto (fun j=>∫sample,Fj j sample ∂vectorFiniteDisorderTilt
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) atTop
      (𝓝 (∫sample,F sample ∂vectorMeasureDisorderTilt μ β t a)) := by
  have hε : Tendsto (fun j : ℕ=>(4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2)
        (by norm_num : (1/2 : ℝ)<1)).const_mul (4*(n : ℝ)*((1-t)*β^2))
  have he := tendsto_integral_exp_mul_of_uniform_error
    (fun sample : VectorDisorderBrownianSample n=>vectorMeasurePotential μ β t sample.1 0)
    (fun j sample=>vectorDyadicPotential μ β t j sample.1 0) Fj F a C hC _ hε
    (fun j=>by
      simpa only [Function.comp_def,vectorDyadicPotential] using
        (measurable_vectorRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
          (vectorDyadicIndex j+3)).comp (measurable_fst.prodMk measurable_const))
    hFj ((integrable_exp_vectorMeasurePotential μ β t ht a 0).comp_fst (vectorBrownianMeasure n))
    (fun j sample=>vectorDyadicPotential_limit_abs_sub_le μ β t ht j sample.1 0) hB hF
  simp only [integral_vectorFiniteDisorderTilt,integral_vectorMeasureDisorderTilt μ β t a ht]
  exact he.div (tendsto_vectorDyadicOuterPartition μ β t a ht)
    (vectorMeasureOuterPartition_pos μ β t a ht).ne'

end QuantitativePaper
