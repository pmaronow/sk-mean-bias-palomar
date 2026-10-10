module
public import QuantitativePaper.VectorItoIntervalPast
public import QuantitativePaper.VectorJointResponseSampleTest

@[expose] public section

/-! Actual bounded F0-weighted backward response identity with random
initial disorder. The cell drift and Wiener characteristics are literal. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem vector_jointResponse_interval_martingale_past
    {F G : VectorParameter n→ℝ} (data : VectorJointResponseTestData F G)
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ m c Q : ℝ}
    (hc : VectorItoCharacteristics X d σ) (hσ : σ^2=c) (hcpos : 0<c)
    (a b : ℝ≥0) (hab : a≤b) (hbQ : (b : ℝ)<Q)
    (hd : ∀ r∈Ioc a b,∀ sample,d r sample=
      c • (m • gradient (vectorColeHopfStep (c*(Q-r)) m (fun x=>F (sample.1,x))) (X r sample)))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample)-
      vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample)-
      vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample)) ∂vectorDisorderBrownianMeasure n)=0 := by
  let h := data.jointBounds m
  let test := vectorJointResponseSampleTimeData data m h c Q hcpos b hbQ
  let hf := vectorJointResponseSampleSpatialTest data m h c Q b X hc.continuous_state hc.adapted_state
  have hito := vector_ito_interval_generator_past hc test hf a b hab le_rfl Z hZ C hC
  have he : (fun sample=>Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample)))=
      (fun sample=>Z sample*(vectorJointResponse F G (c*(Q-b)) m (sample.1,X b sample)-
        vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))) := by
    funext sample
    change Z sample*(vectorCappedResponse (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)) m c Q b b (X b sample)-
      vectorCappedResponse (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)) m c Q b a (X a sample))=_
    simp only [vectorJointResponse,vectorCappedResponse,vectorResponseCapVariance_of_le c Q b b le_rfl,
      vectorResponseCapVariance_of_le c Q b a (show (a : ℝ)≤b from hab)]
  have hgen (r : ℝ≥0) (hr : r∈Ioc a b) (sample : VectorDisorderBrownianSample n) :
      vectorItoGenerator test X d σ r sample=0 := by
    have hrb : (r : ℝ)≤b := hr.2
    change fderiv ℝ (vectorCappedResponse (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)) m c Q b r)
      (X r sample) (d r sample)+σ^2/2*vectorBilinearTrace (vectorHessian
        (vectorCappedResponse (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)) m c Q b r) (X r sample))+
      vectorCappedResponseTimeField (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)) m c Q b r (X r sample)=0
    have hR : vectorCappedResponse (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)) m c Q b r=
        vectorStepResponse (c*(Q-r)) m (fun x=>F (sample.1,x)) (fun x=>G (sample.1,x)) := by
      funext x
      simp only [vectorCappedResponse,vectorResponseCapVariance_of_le c Q b r hrb]
    rw [hR]
    simp only [vectorCappedResponseTimeField_of_le _ _ m c Q b r hrb,hσ,hd r hr sample,
      map_smul,smul_eq_mul,vectorLinearBackwardGenerator]
    ring
  have hz (sample : VectorDisorderBrownianSample n) :
      (∫ s in Ioc a b,Z sample*vectorItoGenerator test X d σ s sample ∂nonnegativeLebesgueMeasure)=0 := by
    calc
      _ = ∫ s in Ioc a b,(0 : ℝ) ∂nonnegativeLebesgueMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        rw [hgen s hs,mul_zero]
      _ = 0 := by simp
  refine ⟨hito.1.congr (Eventually.of_forall fun sample=>congrFun he sample),?_⟩
  have hh := hito.2
  rw [he] at hh
  simpa only [hz,integral_zero] using hh

end QuantitativePaper
