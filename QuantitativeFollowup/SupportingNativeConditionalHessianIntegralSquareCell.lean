module
public import QuantitativePaper.VectorJointResponseSquareInterval
public import QuantitativePaper.VectorItoIntervalPast

@[expose] public section

/-! Genuine square-response evolution against every bounded multiplier
known in the full Wiener past at the left endpoint. This is the local
stochastic step for native conditional covariance integral identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ} {F G : VectorParameter n→ℝ}

theorem native_jointResponse_square_interval_past (data : VectorJointResponseTestData F G)
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ m c Q : ℝ}
    (hc : VectorItoCharacteristics X d σ) (hσ : σ^2=c) (hcpos : 0<c)
    (a b : ℝ≥0) (hab : a≤b) (hb : (b : ℝ)<Q)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*
      ((vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample))^2-
        (vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))^2))
      (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*((vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample))^2-
        (vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))^2)
      ∂vectorDisorderBrownianMeasure n)=
    ∫sample,(∫r in Ioc a b,Z sample*vectorResponseSquareSource F G m c Q X d r sample
      ∂nonnegativeLebesgueMeasure)∂vectorDisorderBrownianMeasure n := by
  let h:=data.jointBounds m
  let test:=vectorJointResponseSampleSquareTimeData data m h c Q hcpos b hb
  let hf:=vectorJointResponseSampleSquareSpatialTest data m h c Q b X hc.continuous_state hc.adapted_state
  have hito:=vector_ito_interval_generator_past hc test hf a b hab le_rfl Z hZ C hC
  have he : (fun sample=>Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample)))=
      (fun sample=>Z sample*((vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample))^2-
        (vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))^2)):=by
    funext sample
    change Z sample*((vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y))
      m c Q b b (X b sample))^2-
      (vectorCappedResponse (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y)) m c Q b a (X a sample))^2)=_
    simp only [vectorJointResponse,vectorCappedResponse,vectorResponseCapVariance_of_le c Q b b le_rfl,
      vectorResponseCapVariance_of_le c Q b a (show (a:ℝ)≤b from hab)]
  refine ⟨hito.1.congr (.of_forall fun sample=>congrFun he sample),?_⟩
  rw [he] at hito
  rw [hito.2]
  apply integral_congr_ae
  filter_upwards with sample
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [vectorJointResponseSquare_generator data m h c Q hcpos b hb X d σ hσ r hr.2 sample]

theorem native_jointResponse_square_source_drift_cancellation
    (F G : VectorParameter n→ℝ) (m c Q : ℝ)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n)
    (hd : d r sample=c • (m • gradient (vectorColeHopfStep (c*(Q-r)) m
      (fun x=>F (sample.1,x))) (X r sample))) :
    vectorResponseSquareSource F G m c Q X d r sample=
      c*∑l : Fin n,(fderiv ℝ
        (vectorStepResponse (c*(Q-r)) m (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)))
        (X r sample) (EuclideanSpace.single l 1))^2 := by
  simp only [vectorResponseSquareSource,hd,sub_self,map_zero,mul_zero,zero_add]

end QuantitativeFollowup
