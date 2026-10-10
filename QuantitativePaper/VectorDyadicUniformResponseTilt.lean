module
public import QuantitativePaper.VectorDyadicUniformResponseDensity
public import FourPapersCommon.UniformDensityIntegration

@[expose] public section

/-! Uniform bounded expectations under the actual varying dyadic laws. -/
noncomputable section
open MeasureTheory Set Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ} {Q : Type*}

theorem tendstoUniformly_integral_vectorDyadicGridTilt_bounded
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1)
    (Fj : ℕ → Q → VectorDisorderBrownianSample n → ℝ)
    (F : Q → VectorDisorderBrownianSample n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hFj : ∀ j q, Measurable (Fj j q)) (hF : ∀ q, Measurable (F q))
    (hBj : ∀ j q sample, ‖Fj j q sample‖ ≤ C) (hB : ∀ q sample, ‖F q sample‖ ≤ C)
    (hU : TendstoUniformly (fun j (z : Q × VectorDisorderBrownianSample n) => Fj j z.1 z.2)
      (fun z => F z.1 z.2) atTop) :
    TendstoUniformly (fun j q => ∫ sample, Fj j q sample
      ∂vectorMeasureDisorderTilt (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a)
      (fun q => ∫ sample, F q sample ∂vectorMeasureDisorderTilt μ β t a) atTop := by
  have hmass (j : ℕ) : (∫ sample : VectorDisorderBrownianSample n,
      vectorMeasureOuterWeight (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a sample.1
        ∂vectorDisorderBrownianMeasure n) = 1 := by
    let ν := Paper.parisiGridMeasure μ (vectorDyadicIndex j)
    letI := vectorMeasureDisorderTilt_probability (n := n) ν β t a ht
    have h := integral_vectorMeasureDisorderTilt_eq_weighted (n := n) ν β t a ht (fun _ => 1)
    simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] using h.symm
  have h := tendstoUniformly_integral_density_mul
    (P := vectorDisorderBrownianMeasure n)
    (fun j sample => vectorMeasureOuterWeight (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a sample.1)
    (fun sample => vectorMeasureOuterWeight μ β t a sample.1) Fj F
    (fun j => (integrable_vectorMeasureOuterWeight _ β t a ht).comp_fst (vectorBrownianMeasure n))
    ((integrable_vectorMeasureOuterWeight μ β t a ht).comp_fst (vectorBrownianMeasure n))
    (fun j sample => div_nonneg (Real.exp_pos _).le (vectorMeasureOuterPartition_pos _ β t a ht).le)
    hmass (tendsto_integral_vectorDyadicOuterWeight_abs_sub μ β t a ht)
    C hC hFj hF hBj hB hU
  simpa only [← integral_vectorMeasureDisorderTilt_eq_weighted _ β t a ht] using h

end QuantitativePaper
