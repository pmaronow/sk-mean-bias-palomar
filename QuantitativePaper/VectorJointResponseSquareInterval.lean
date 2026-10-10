module
public import QuantitativePaper.VectorJointResponseSquareTest
public import QuantitativePaper.VectorItoIntervalExpectation

@[expose] public section

/-! Actual weighted square-response evolution on a cropped cell. The drift
may be the arbitrary-profile diffusion; its discrepancy is kept literal. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ} {F G : VectorParameter n→ℝ}

def vectorResponseSquareSource (F G : VectorParameter n→ℝ) (m c Q : ℝ)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ℝ :=
  let f:=vectorStepResponse (c*(Q-r)) m (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x))
  let u:=vectorColeHopfStep (c*(Q-r)) m (fun x=>F (sample.1,x))
  2*f (X r sample)*fderiv ℝ f (X r sample) (d r sample-c • (m • gradient u (X r sample)))+
    c*∑l : Fin n,(fderiv ℝ f (X r sample) (EuclideanSpace.single l 1))^2

theorem vectorJointResponseSquare_generator (data : VectorJointResponseTestData F G)
    (m : ℝ) (h : VectorJointBackwardBounds F G m) (c Q : ℝ) (hc : 0<c)
    (b : ℝ≥0) (hb : (b : ℝ)<Q)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n) (σ : ℝ) (hσ : σ^2=c)
    (r : ℝ≥0) (hr : r≤b) (sample : VectorDisorderBrownianSample n) :
    vectorItoGenerator (vectorJointResponseSampleSquareTimeData data m h c Q hc b hb)
      X d σ r sample=vectorResponseSquareSource F G m c Q X d r sample := by
  let f:=vectorStepResponse (c*(Q-r)) m (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x))
  have hreg : ContDiff ℝ 2 f:=((h.fieldBounds sample.1).responseRegularity _).of_le (by norm_num)
  have he : vectorCappedResponse (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)) m c Q b r=f := by
    funext x
    simp only [vectorCappedResponse,vectorResponseCapVariance_of_le c Q b r
      (show (r : ℝ)≤b from hr),f]
  unfold vectorItoGenerator vectorJointResponseSampleSquareTimeData
  change fderiv ℝ (fun x=>(vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b r x)^2)
      (X r sample) (d r sample)+σ^2/2*vectorBilinearTrace
        (vectorHessian (fun x=>(vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b r x)^2)
          (X r sample))+
    2*vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b r (X r sample)*
      vectorCappedResponseTimeField (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b r (X r sample)=_
  rw [he,fderiv_square f (hreg.differentiable (by norm_num)),vectorBilinearTrace_square f hreg,hσ,
    vectorCappedResponseTimeField_of_le _ _ m c Q b r (show (r : ℝ)≤b from hr)]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,vectorLinearBackwardGenerator,
    vectorResponseSquareSource,map_sub,map_smul]
  dsimp only [f]
  ring

theorem vector_jointResponse_square_interval (data : VectorJointResponseTestData F G)
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ m c Q : ℝ}
    (hc : VectorItoCharacteristics X d σ) (hσ : σ^2=c) (hcpos : 0<c)
    (a b : ℝ≥0) (hab : a≤b) (hb : (b : ℝ)<Q)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*
      ((vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample))^2-
        (vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))^2))
      (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*((vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample))^2-
        (vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))^2)
      ∂vectorDisorderBrownianMeasure n)=
    ∫sample,(∫r in Ioc a b,Z sample*vectorResponseSquareSource F G m c Q X d r sample
      ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  let h:=data.jointBounds m
  let test:=vectorJointResponseSampleSquareTimeData data m h c Q hcpos b hb
  let hf:=vectorJointResponseSampleSquareSpatialTest data m h c Q b X hc.continuous_state hc.adapted_state
  have hito:=vector_ito_interval_generator hc test hf Z hZ C hC a b hab le_rfl
  have he : (fun sample=>Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample)))=
      (fun sample=>Z sample*((vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample))^2-
        (vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))^2)) := by
    funext sample
    change Z sample*((vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y))
      m c Q b b (X b sample))^2-
      (vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b a (X a sample))^2)=_
    simp only [vectorJointResponse,vectorCappedResponse,vectorResponseCapVariance_of_le c Q b b le_rfl,
      vectorResponseCapVariance_of_le c Q b a (show (a : ℝ)≤b from hab)]
  refine ⟨hito.1.congr (Eventually.of_forall fun sample=>congrFun he sample),?_⟩
  rw [he] at hito
  rw [hito.2]
  apply integral_congr_ae
  filter_upwards with sample
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [vectorJointResponseSquare_generator data m h c Q hcpos b hb X d σ hσ r hr.2 sample]

end QuantitativePaper
