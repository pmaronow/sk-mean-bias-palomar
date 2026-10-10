module
public import QuantitativePaper.VectorJointResponseSampleTest
public import QuantitativePaper.VectorItoIntervalExpectation

@[expose] public section

/-! Genuine backward-response Itô evolution under an arbitrary constructed
bounded-drift state. The actual discrepancy from the Cole–Hopf drift remains
in the source; the stochastic cancellation is proved by the interval theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ} {F G : VectorParameter n→ℝ}

def vectorResponseLinearSource (F G : VectorParameter n→ℝ) (m c Q : ℝ)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ℝ :=
  let f:=vectorStepResponse (c*(Q-r)) m (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x))
  let u:=vectorColeHopfStep (c*(Q-r)) m (fun x=>F (sample.1,x))
  fderiv ℝ f (X r sample) (d r sample-c • (m • gradient u (X r sample)))

theorem vectorJointResponseLinear_generator (data : VectorJointResponseTestData F G)
    (m : ℝ) (h : VectorJointBackwardBounds F G m) (c Q : ℝ) (hc : 0<c)
    (b : ℝ≥0) (hb : (b : ℝ)<Q)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n) (σ : ℝ) (hσ : σ^2=c)
    (r : ℝ≥0) (hr : r≤b) (sample : VectorDisorderBrownianSample n) :
    vectorItoGenerator (vectorJointResponseSampleTimeData data m h c Q hc b hb)
      X d σ r sample=vectorResponseLinearSource F G m c Q X d r sample := by
  let f:=vectorStepResponse (c*(Q-r)) m (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x))
  have he : vectorCappedResponse (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)) m c Q b r=f := by
    funext x
    simp only [vectorCappedResponse,vectorResponseCapVariance_of_le c Q b r
      (show (r : ℝ)≤b from hr),f]
  unfold vectorItoGenerator vectorJointResponseSampleTimeData
  change fderiv ℝ (vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b r)
      (X r sample) (d r sample)+σ^2/2*vectorBilinearTrace
        (vectorHessian (vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b r)
          (X r sample))+
    vectorCappedResponseTimeField (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b r (X r sample)=_
  rw [he,hσ,vectorCappedResponseTimeField_of_le _ _ m c Q b r (show (r : ℝ)≤b from hr)]
  simp only [vectorLinearBackwardGenerator,vectorResponseLinearSource,map_sub,map_smul]
  dsimp only [f]
  ring

theorem vector_jointResponse_linear_interval (data : VectorJointResponseTestData F G)
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ m c Q : ℝ}
    (hc : VectorItoCharacteristics X d σ) (hσ : σ^2=c) (hcpos : 0<c)
    (a b : ℝ≥0) (hab : a≤b) (hb : (b : ℝ)<Q)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*
      (vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample)-
        vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample)))
      (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*(vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample)-
        vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))
      ∂vectorDisorderBrownianMeasure n)=
    ∫sample,(∫r in Ioc a b,Z sample*vectorResponseLinearSource F G m c Q X d r sample
      ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  let h:=data.jointBounds m
  let test:=vectorJointResponseSampleTimeData data m h c Q hcpos b hb
  let hf:=vectorJointResponseSampleSpatialTest data m h c Q b X hc.continuous_state hc.adapted_state
  have hito:=vector_ito_interval_generator hc test hf Z hZ C hC a b hab le_rfl
  have he : (fun sample=>Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample)))=
      (fun sample=>Z sample*(vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample)-
        vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))) := by
    funext sample
    change Z sample*(vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y))
      m c Q b b (X b sample)-
      vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b a (X a sample))=_
    simp only [vectorJointResponse,vectorCappedResponse,vectorResponseCapVariance_of_le c Q b b le_rfl,
      vectorResponseCapVariance_of_le c Q b a (show (a : ℝ)≤b from hab)]
  refine ⟨hito.1.congr (Eventually.of_forall fun sample=>congrFun he sample),?_⟩
  rw [he] at hito
  rw [hito.2]
  apply integral_congr_ae
  filter_upwards with sample
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [vectorJointResponseLinear_generator data m h c Q hcpos b hb X d σ hσ r hr.2 sample]

end QuantitativePaper
