module
public import QuantitativePaper.VectorSpatialItoSquare
public import QuantitativePaper.VectorJointResponseSampleTest

@[expose] public section

/-! Genuine squared capped response tests with the actual initial disorder.
All bounds and adapted coefficients follow from constructed response data. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ} {F G : VectorParameter n→ℝ}

theorem norm_vectorJointCappedResponse_le (data : VectorJointResponseTestData F G)
    (m c Q b r : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    ‖vectorCappedResponse (fun y=>F (p,y)) (fun y=>G (p,y)) m c Q b r x‖≤
      (data.observableBounds 0).toNNReal := by
  rw [Real.coe_toNNReal _ (data.observableBounds_nonneg 0),Real.norm_eq_abs]
  apply abs_vectorStepResponse_le _ _ data.fieldLip (data.fieldData p).lipschitz
  intro y
  simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,VectorJointResponseTestData.fieldData] using
    (data.fieldData p).observableJets 0 (by omega) y

theorem lipschitz_vectorJointCappedResponse (data : VectorJointResponseTestData F G)
    (m : ℝ) (h : VectorJointBackwardBounds F G m) (c Q b r : ℝ) (p : Couplings n×ℝ) :
    LipschitzWith h.responsePower
      (vectorCappedResponse (fun y=>F (p,y)) (fun y=>G (p,y)) m c Q b r) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (((h.fieldBounds p).responseRegularity _).differentiable (by norm_num))
  intro x
  rw [←NNReal.coe_le_coe,coe_nnnorm,←norm_iteratedFDeriv_one]
  simpa only [pow_one,VectorJointBackwardBounds.fieldBounds] using
    (h.fieldBounds p).responseJets _ 1 le_rfl (by omega) x

def vectorJointResponseSampleSquareTimeData (data : VectorJointResponseTestData F G)
    (m : ℝ) (h : VectorJointBackwardBounds F G m) (c Q : ℝ) (hc : 0<c)
    (b : ℝ≥0) (hb : (b : ℝ)<Q) :
    TimeFTCData (VectorDisorderBrownianSample n) (Field n) b :=
  (vectorJointResponseSampleTimeData data m h c Q hc b hb).square
    (data.observableBounds 0).toNNReal h.responsePower
    (fun r sample x=>norm_vectorJointCappedResponse_le data m c Q b r sample.1 x)
    (fun r sample=>lipschitz_vectorJointCappedResponse data m h c Q b r sample.1)
    (fun sample=>(data.fieldData sample.1).continuous_cappedResponse m c Q b)

def vectorJointResponseSampleSquareSpatialTest (data : VectorJointResponseTestData F G)
    (m : ℝ) (h : VectorJointBackwardBounds F G m) (c Q b : ℝ)
    (X : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hX : ∀sample,Continuous (fun r=>X r sample))
    (hXa : StronglyAdapted (vectorBrownianFiltration n) X) :
    VectorSpatialItoTest (fun r sample x=>
      (vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b r x)^2) X := by
  apply (vectorJointResponseSampleSpatialTest data m h c Q b X hX hXa).square
    (data.observableBounds 0).toNNReal
    (fun r sample x=>norm_vectorJointCappedResponse_le data m c Q b r sample.1 x)
  · intro q r
    change Measurable[vectorBrownianFiltration n r] (fun sample=>
      vectorJointResponse F G (vectorResponseCapVariance c Q b q) m (sample.1,X r sample))
    exact (h.responseRegularity _).continuous.measurable.comp
      ((stronglyMeasurable_initialVectorDisorder n r).measurable.prodMk (hXa r).measurable)
  · intro sample
    exact ((data.fieldData sample.1).continuous_cappedResponse m c Q b).comp
      ((NNReal.continuous_coe).prodMk (hX sample))

end QuantitativePaper
