module
public import QuantitativePaper.VectorItoGenerator

@[expose] public section

/-! A genuine single-integral form of the vector time Itô expectation,
valid at every prefix of the test horizon. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ} {T : ℝ≥0}

theorem vector_ito_prefix_generator
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (hf : VectorSpatialItoTest (fun q=>test.f q) X)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (b : ℝ≥0) (hb : b ≤ T) :
    Integrable (fun sample=>Z sample*(test.f b sample (X b sample)-test.f 0 sample (X 0 sample)))
      (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(test.f b sample (X b sample)-test.f 0 sample (X 0 sample))
      ∂vectorDisorderBrownianMeasure n)=
      ∫ sample,(∫ s in Ioc 0 b,Z sample*vectorItoGenerator test X d σ s sample
        ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  let P := vectorDisorderBrownianMeasure n
  let A : ℝ≥0 → VectorDisorderBrownianSample n → ℝ := fun s sample=>
    Z sample*fderiv ℝ (test.f s sample) (X s sample) (d s sample)
  let Q : ℝ≥0 → VectorDisorderBrownianSample n → ℝ := fun s sample=>
    Z sample*vectorBilinearTrace (vectorHessian (test.f s sample) (X s sample))
  let V : ℝ≥0 → VectorDisorderBrownianSample n → ℝ := fun s sample=>
    Z sample*test.ft s sample (X s sample)
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  have hAm : Measurable (Function.uncurry A) := (hZg.comp measurable_snd).mul
    ((show Measurable (fun p : (Field n →L[ℝ] ℝ)×Field n=>p.1 p.2) from by fun_prop).comp
      ((measurable_vectorItoGradientPath hf).prodMk hc.measurable_drift))
  have hQm : Measurable (Function.uncurry Q) :=
    (hZg.comp measurable_snd).mul (measurable_vectorItoTracePath hf)
  have hVm : Measurable (Function.uncurry V) :=
    (hZg.comp measurable_snd).mul (measurable_vectorItoTimePath hc test)
  obtain ⟨D,hD⟩ := hc.bounded_drift
  have hAb (s : ℝ≥0) (_ : s∈Icc 0 b) (sample : VectorDisorderBrownianSample n) :
      ‖A s sample‖ ≤ (C*hf.firstBound*D : ℝ≥0) := by
    have hh := ((fderiv ℝ (test.f s sample) (X s sample)).le_opNorm (d s sample)).trans
      (mul_le_mul (hf.first_le s sample _) (hD s sample) (norm_nonneg _) hf.firstBound.coe_nonneg)
    simpa only [A,norm_mul,NNReal.coe_mul,mul_assoc] using
      mul_le_mul (hC sample) hh (norm_nonneg _) C.coe_nonneg
  have hQb (s : ℝ≥0) (_ : s∈Icc 0 b) (sample : VectorDisorderBrownianSample n) :
      ‖Q s sample‖ ≤ (C*(n : ℝ≥0)*hf.secondBound : ℝ≥0) := by
    simpa only [Q,norm_mul,Real.norm_eq_abs,NNReal.coe_mul,NNReal.coe_natCast,mul_assoc] using
      mul_le_mul (hC sample) (hf.trace_bound s sample) (abs_nonneg _) C.coe_nonneg
  have hVb (s : ℝ≥0) (hs : s∈Icc 0 b) (sample : VectorDisorderBrownianSample n) :
      ‖V s sample‖ ≤ (C*test.bound : ℝ≥0) := by
    simpa only [V,norm_mul,NNReal.coe_mul] using mul_le_mul (hC sample)
      (test.ft_bound s ⟨s.coe_nonneg,show (s : ℝ)≤T from hs.2.trans hb⟩ sample (X s sample))
      (norm_nonneg _) C.coe_nonneg
  have hAi := integrable_bounded_time_integral P A hAm (C*hf.firstBound*D) b hAb
  have hQi := integrable_bounded_time_integral P Q hQm (C*(n : ℝ≥0)*hf.secondBound) b hQb
  have hVi := integrable_bounded_time_integral P V hVm (C*test.bound) b hVb
  have he (sample : VectorDisorderBrownianSample n) :
      (∫ s in Ioc 0 b,Z sample*vectorItoGenerator test X d σ s sample ∂nonnegativeLebesgueMeasure)=
      (∫ s in Ioc 0 b,A s sample ∂nonnegativeLebesgueMeasure)+
        σ^2/2*(∫ s in Ioc 0 b,Q s sample ∂nonnegativeLebesgueMeasure)+
        (∫ s in Ioc 0 b,V s sample ∂nonnegativeLebesgueMeasure) := by
    have hA := integrableOn_bounded_time_function A hAm (C*hf.firstBound*D) b hAb sample
    have hQ := integrableOn_bounded_time_function Q hQm (C*(n : ℝ≥0)*hf.secondBound) b hQb sample
    have hV := integrableOn_bounded_time_function V hVm (C*test.bound) b hVb sample
    have hfun : (fun s=>Z sample*vectorItoGenerator test X d σ s sample)=
        (fun s=>A s sample+(σ^2/2)*Q s sample+V s sample) := by
      funext s
      dsimp only [vectorItoGenerator,A,Q,V]
      ring
    have hs := integral_add (hA.add (hQ.const_mul (σ^2/2))) hV
    have hs' := integral_add hA (hQ.const_mul (σ^2/2))
    simp only [Pi.add_apply] at hs hs'
    rw [hfun,hs,hs']
    simp only [integral_const_mul]
  have hito := vector_ito_time_expectation hc (test.restrictHorizon b hb) hf Z hZ C hC
  refine ⟨hito.1,?_⟩
  have hAd : (fun sample=>Z sample*(∫ s in Ioc 0 b,
      fderiv ℝ (test.f s sample) (X s sample) (d s sample) ∂nonnegativeLebesgueMeasure))=
      (fun sample=>∫ s in Ioc 0 b,A s sample ∂nonnegativeLebesgueMeasure) := by
    funext sample
    exact (integral_const_mul _ _).symm
  change _=(∫ sample,(∫ s in Ioc 0 b,Z sample*vectorItoGenerator test X d σ s sample
    ∂nonnegativeLebesgueMeasure) ∂P)
  have hs := integral_add (hAi.add (hQi.const_mul (σ^2/2))) hVi
  have hs' := integral_add hAi (hQi.const_mul (σ^2/2))
  simp only [Pi.add_apply] at hs hs'
  rw [show (fun sample=>∫ s in Ioc 0 b,Z sample*vectorItoGenerator test X d σ s sample
      ∂nonnegativeLebesgueMeasure)=
    (fun sample=>(∫ s in Ioc 0 b,A s sample ∂nonnegativeLebesgueMeasure)+
      σ^2/2*(∫ s in Ioc 0 b,Q s sample ∂nonnegativeLebesgueMeasure)+
      (∫ s in Ioc 0 b,V s sample ∂nonnegativeLebesgueMeasure)) from funext he,
    hs,hs',integral_const_mul]
  have hh := hito.2
  simp only [TimeFTCData.restrictHorizon,timeFTCIntegral] at hh
  rw [hAd] at hh
  exact hh

end QuantitativePaper
