module
public import QuantitativePaper.VectorResponseSpatialTest

@[expose] public section

/-! A genuine weighted backward-response identity on an interior
constant-mass cell of an actual bounded-drift Wiener state. The diffusion
characteristics and literal cell drift are the inputs; no stochastic or
transition-law identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem vector_response_interval_martingale
    {f g : Field n → ℝ} (data : VectorResponseTestData f g)
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ m c Q : ℝ}
    (hc : VectorItoCharacteristics X d σ) (hσ : σ^2=c) (hcpos : 0<c)
    (a b : ℝ≥0) (hab : a≤b) (hbQ : (b : ℝ)<Q)
    (hd : ∀ r∈Ioc a b,∀ sample,d r sample=
      c • (m • gradient (vectorColeHopfStep (c*(Q-r)) m f) (X r sample)))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(vectorStepResponse (c*(Q-b)) m f g (X b sample)-
      vectorStepResponse (c*(Q-a)) m f g (X a sample))) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(vectorStepResponse (c*(Q-b)) m f g (X b sample)-
      vectorStepResponse (c*(Q-a)) m f g (X a sample)) ∂vectorDisorderBrownianMeasure n)=0 := by
  let test := vectorResponseTimeData data m c Q hcpos b hbQ
  let hf := vectorResponseSpatialTest data m c Q b X hc.continuous_state hc.adapted_state
  have hito := vector_ito_interval_generator hc test hf Z hZ C hC a b hab le_rfl
  have he : (fun sample=>Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample)))=
      (fun sample=>Z sample*(vectorStepResponse (c*(Q-b)) m f g (X b sample)-
        vectorStepResponse (c*(Q-a)) m f g (X a sample))) := by
    funext sample
    change Z sample*(vectorCappedResponse f g m c Q b b (X b sample)-
      vectorCappedResponse f g m c Q b a (X a sample))=_
    simp only [vectorCappedResponse,vectorResponseCapVariance_of_le c Q b b le_rfl,
      vectorResponseCapVariance_of_le c Q b a (show (a : ℝ)≤b from hab)]
  have hgen (r : ℝ≥0) (hr : r∈Ioc a b) (sample : VectorDisorderBrownianSample n) :
      vectorItoGenerator test X d σ r sample=0 := by
    have hrb : (r : ℝ)≤b := hr.2
    change fderiv ℝ (vectorCappedResponse f g m c Q b r) (X r sample) (d r sample)+
      σ^2/2*vectorBilinearTrace (vectorHessian (vectorCappedResponse f g m c Q b r) (X r sample))+
      vectorCappedResponseTimeField f g m c Q b r (X r sample)=0
    have hR : vectorCappedResponse f g m c Q b r=vectorStepResponse (c*(Q-r)) m f g := by
      funext x
      simp only [vectorCappedResponse,vectorResponseCapVariance_of_le c Q b r hrb]
    rw [hR]
    simp only [vectorCappedResponseTimeField_of_le f g m c Q b r hrb,hσ,hd r hr sample,
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
