module
public import QuantitativePaper.VectorItoPrefixGeneratorAt
public import QuantitativePaper.VectorSpatialTestTimeShift
public import QuantitativePaper.VectorItoGenerator
public import FourPapersCommon.TimeFTCShift

@[expose] public section

/-! Genuine interval Itô expectation with a bounded multiplier known in
the whole past at its left endpoint. The shifted Wiener increments and
time integrals are derived from the actual original characteristics. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {B : ℝ≥0}

theorem vector_ito_interval_generator_past
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) B)
    (hf : VectorSpatialItoTest (fun q=>test.f q) X)
    (a b : ℝ≥0) (hab : a≤b) (hb : b≤B)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample)))
      (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample))
      ∂vectorDisorderBrownianMeasure n)=
      ∫ sample,(∫ r in Ioc a b,Z sample*vectorItoGenerator test X d σ r sample
        ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  let T := b-a
  have heq : a+T=b := add_tsub_cancel_of_le hab
  have hT : a+T≤B := heq.le.trans hb
  let testS := test.shiftStart a T hT
  have hfS : VectorSpatialItoTestAt a (fun q=>testS.f q) (fun q=>X (a+q)) := by
    simpa only [testS,TimeFTCData.shiftStart,NNReal.coe_add] using hf.timeShift a
  have hZS : Measurable[vectorBrownianFiltrationAt n a 0] Z := by
    change Measurable[vectorBrownianFiltration n (a+0)] Z
    rw [add_zero]
    exact hZ
  have hito := vector_ito_prefix_generatorAt (hc.timeShift a) testS hfS Z hZS C hC T le_rfl
  have he : (fun sample=>Z sample*(testS.f T sample (X (a+T) sample)-
      testS.f 0 sample (X (a+0) sample)))=
      (fun sample=>Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample))) := by
    funext sample
    change Z sample*(test.f ((a : ℝ)+T) sample (X (a+T) sample)-
      test.f ((a : ℝ)+0) sample (X (a+0) sample))=_
    rw [←NNReal.coe_add,heq]
    simp only [add_zero]
  have hgen (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
      vectorItoGeneratorAt testS (fun q=>X (a+q)) (fun q=>d (a+q)) σ r sample=
        vectorItoGenerator test X d σ (a+r) sample := by
    simp only [vectorItoGeneratorAt,vectorItoGenerator,testS,TimeFTCData.shiftStart,NNReal.coe_add]
  have hint (sample : VectorDisorderBrownianSample n) :
      (∫ r in Ioc 0 T,Z sample*vectorItoGeneratorAt testS (fun q=>X (a+q))
        (fun q=>d (a+q)) σ r sample ∂nonnegativeLebesgueMeasure)=
        ∫ r in Ioc a b,Z sample*vectorItoGenerator test X d σ r sample ∂nonnegativeLebesgueMeasure := by
    simp only [hgen]
    have hm : Measurable (fun r=>Z sample*vectorItoGenerator test X d σ r sample) :=
      measurable_const.mul (measurable_vectorItoGenerator hc test hf).of_uncurry_right
    rw [integral_nonnegativeTime_add _ hm.aestronglyMeasurable a T,heq]
  refine ⟨hito.1.congr (Eventually.of_forall fun sample=>congrFun he sample),?_⟩
  have hh := hito.2
  rw [he] at hh
  simpa only [hint] using hh

end QuantitativePaper
