module
public import QuantitativePaper.VectorItoIntervalExpectation

@[expose] public section

/-! Integrable finite-interval generators and genuine linear combinations
of already proved vector Itô identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {T : ℝ≥0}

theorem integrable_vectorItoGenerator_interval
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (hf : VectorSpatialItoTest (fun q=>test.f q) X)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀sample,‖Z sample‖≤C) (a b : ℝ≥0) (hab : a≤b) (hb : b≤T) :
    (∀sample,IntegrableOn (fun r=>Z sample*vectorItoGenerator test X d σ r sample)
      (Ioc a b) nonnegativeLebesgueMeasure) ∧
    Integrable (fun sample=>∫r in Ioc a b,Z sample*vectorItoGenerator test X d σ r sample
      ∂nonnegativeLebesgueMeasure) (vectorDisorderBrownianMeasure n) := by
  let P:=vectorDisorderBrownianMeasure n
  let G:=fun r sample=>Z sample*vectorItoGenerator test X d σ r sample
  have hZg : Measurable Z:=hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  have hGm : Measurable (Function.uncurry G):=
    (hZg.comp measurable_snd).mul (measurable_vectorItoGenerator hc test hf)
  obtain ⟨D,hD⟩:=hc.bounded_drift
  let K : ℝ≥0:=⟨(C : ℝ)*(hf.firstBound*D+σ^2/2*((n : ℝ)*hf.secondBound)+test.bound),by positivity⟩
  have hGb (r : ℝ≥0) (hr : r∈Icc 0 b) (sample : VectorDisorderBrownianSample n) :
      ‖G r sample‖≤K:=by
    change ‖Z sample*vectorItoGenerator test X d σ r sample‖≤_
    rw [norm_mul]
    exact mul_le_mul (hC sample)
      (vectorItoGenerator_bound hc test hf D hD r ⟨hr.1,hr.2.trans hb⟩ sample)
      (norm_nonneg _) C.coe_nonneg
  have hGa (r : ℝ≥0) (hr : r∈Icc 0 a):=hGb r ⟨hr.1,hr.2.trans hab⟩
  have hBi:=integrable_bounded_time_integral P G hGm K b hGb
  have hAi:=integrable_bounded_time_integral P G hGm K a hGa
  refine ⟨?_,?_⟩
  · intro sample
    exact (integrableOn_bounded_time_function G hGm K b hGb sample).mono_set
      (fun r hr=>⟨bot_le.trans_lt hr.1,hr.2⟩)
  · exact (hBi.sub hAi).congr (.of_forall fun sample=>
      bounded_time_integral_sub G hGm K a b hab hGb sample)

theorem vector_ito_interval_linear_combination
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    (A B : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (hA : VectorSpatialItoTest (fun q=>A.f q) X)
    (hB : VectorSpatialItoTest (fun q=>B.f q) X)
    (m : ℝ) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀sample,‖Z sample‖≤C) (a b : ℝ≥0) (hab : a≤b) (hb : b≤T) :
    Integrable (fun sample=>Z sample*((A.f b sample (X b sample)-m*B.f b sample (X b sample))-
      (A.f a sample (X a sample)-m*B.f a sample (X a sample))))
      (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*((A.f b sample (X b sample)-m*B.f b sample (X b sample))-
      (A.f a sample (X a sample)-m*B.f a sample (X a sample)))∂vectorDisorderBrownianMeasure n)=
    ∫sample,(∫r in Ioc a b,Z sample*(vectorItoGenerator A X d σ r sample-
      m*vectorItoGenerator B X d σ r sample)∂nonnegativeLebesgueMeasure)
      ∂vectorDisorderBrownianMeasure n := by
  have hIA:=vector_ito_interval_generator hc A hA Z hZ C hC a b hab hb
  have hIB:=vector_ito_interval_generator hc B hB Z hZ C hC a b hab hb
  have hGA:=integrable_vectorItoGenerator_interval hc A hA Z hZ C hC a b hab hb
  have hGB:=integrable_vectorItoGenerator_interval hc B hB Z hZ C hC a b hab hb
  have he : (fun sample=>Z sample*((A.f b sample (X b sample)-m*B.f b sample (X b sample))-
      (A.f a sample (X a sample)-m*B.f a sample (X a sample))))=
      (fun sample=>Z sample*(A.f b sample (X b sample)-A.f a sample (X a sample))-
        m*(Z sample*(B.f b sample (X b sample)-B.f a sample (X a sample)))):=by
    funext sample
    ring
  refine ⟨(hIA.1.sub (hIB.1.const_mul m)).congr (.of_forall fun sample=>(congrFun he sample).symm),?_⟩
  rw [he,integral_sub hIA.1 (hIB.1.const_mul m),integral_const_mul,hIA.2,hIB.2,
    ←integral_const_mul m,←integral_sub hGA.2 (hGB.2.const_mul m)]
  apply integral_congr_ae
  filter_upwards with sample
  rw [←integral_const_mul m,←integral_sub (hGA.1 sample) ((hGB.1 sample).const_mul m)]
  apply integral_congr_ae
  filter_upwards with r
  ring

end QuantitativePaper
