module
public import QuantitativePaper.VectorItoPrefixGenerator

@[expose] public section

/-! Actual vector time Itô expectation on an arbitrary profile interval,
obtained by subtracting two proved prefix identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ} {T : ℝ≥0}

theorem vector_ito_interval_generator
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (hf : VectorSpatialItoTest (fun q=>test.f q) X)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (a b : ℝ≥0) (hab : a ≤ b) (hb : b ≤ T) :
    Integrable (fun sample=>Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample)))
      (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample))
      ∂vectorDisorderBrownianMeasure n)=
      ∫ sample,(∫ s in Ioc a b,Z sample*vectorItoGenerator test X d σ s sample
        ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  let P := vectorDisorderBrownianMeasure n
  let Y : ℝ≥0 → VectorDisorderBrownianSample n → ℝ := fun r sample=>
    Z sample*(test.f r sample (X r sample)-test.f 0 sample (X 0 sample))
  let G : ℝ≥0 → VectorDisorderBrownianSample n → ℝ := fun s sample=>
    Z sample*vectorItoGenerator test X d σ s sample
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  have hGm : Measurable (Function.uncurry G) :=
    (hZg.comp measurable_snd).mul (measurable_vectorItoGenerator hc test hf)
  obtain ⟨D,hD⟩ := hc.bounded_drift
  let K : ℝ≥0 := ⟨(C : ℝ)*(hf.firstBound*D+σ^2/2*((n : ℝ)*hf.secondBound)+test.bound),by positivity⟩
  have hGb (s : ℝ≥0) (hs : s∈Icc 0 b) (sample : VectorDisorderBrownianSample n) :
      ‖G s sample‖ ≤ K := by
    change ‖Z sample*vectorItoGenerator test X d σ s sample‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hC sample)
      (vectorItoGenerator_bound hc test hf D hD s ⟨hs.1,hs.2.trans hb⟩ sample)
      (norm_nonneg _) C.coe_nonneg
  have hGa (s : ℝ≥0) (hs : s∈Icc 0 a) := hGb s ⟨hs.1,hs.2.trans hab⟩
  have hGbi := integrable_bounded_time_integral P G hGm K b hGb
  have hGai := integrable_bounded_time_integral P G hGm K a hGa
  have hpB := vector_ito_prefix_generator hc test hf Z hZ C hC b hb
  have hpA := vector_ito_prefix_generator hc test hf Z hZ C hC a (hab.trans hb)
  have he : (fun sample=>Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample)))=
      (fun sample=>Y b sample-Y a sample) := by
    funext sample
    dsimp only [Y]
    ring
  refine ⟨(hpB.1.sub hpA.1).congr (Eventually.of_forall fun sample=>(congrFun he sample).symm),?_⟩
  have hEnd := integral_sub hpB.1 hpA.1
  have hInt := integral_sub hGbi hGai
  rw [he,hEnd,hpB.2,hpA.2]
  change (∫ sample,(∫ s in Ioc 0 b,G s sample ∂nonnegativeLebesgueMeasure) ∂P)-
      (∫ sample,(∫ s in Ioc 0 a,G s sample ∂nonnegativeLebesgueMeasure) ∂P)=
    ∫ sample,(∫ s in Ioc a b,G s sample ∂nonnegativeLebesgueMeasure) ∂P
  rw [←hInt]
  apply integral_congr_ae
  exact Eventually.of_forall fun sample=>bounded_time_integral_sub G hGm K a b hab hGb sample

end QuantitativePaper
