module
public import QuantitativePaper.VectorResponseTimeData

@[expose] public section

/-! Actual adapted spatial Itô tests for capped weighted responses along
any genuine continuous adapted vector state. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable {n : ℕ}

def vectorResponseSpatialTest {f g : Field n → ℝ} (d : VectorResponseTestData f g)
    (m c Q b : ℝ)
    (X : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hX : ∀ sample,Continuous (fun r=>X r sample))
    (hXa : StronglyAdapted (vectorBrownianFiltration n) X) :
    VectorSpatialItoTest (fun r _ x=>vectorCappedResponse f g m c Q b r x) X := by
  let h := d.bounds m
  have hC (r : ℝ) : ContDiff ℝ 3 (vectorCappedResponse f g m c Q b r) :=
    h.responseRegularity (vectorResponseCapVariance c Q b r)
  have hp (sample : VectorDisorderBrownianSample n) :
      Continuous (fun r : ℝ≥0=>(vectorResponseCapVariance c Q b r,X r sample)) := by
    unfold vectorResponseCapVariance
    fun_prop
  refine {
    firstBound := h.responsePower
    secondBound := h.responsePower^2
    thirdBound := h.responsePower^3
    measurable := ?_
    regularity := fun r _=>hC r
    first_le := ?_
    second_le := ?_
    third_le := ?_
    adapted_first := ?_
    adapted_second := ?_
    continuous_first_path := ?_
    continuous_trace_path := ?_ }
  · intro r
    exact (hC r).continuous.measurable.comp measurable_snd
  · intro r _ x
    rw [←norm_iteratedFDeriv_one]
    simpa only [vectorCappedResponse,pow_one] using h.responseJets
      (vectorResponseCapVariance c Q b r) 1 le_rfl (by omega) x
  · intro r _ x
    exact h.responseJets (vectorResponseCapVariance c Q b r) 2 (by omega) (by omega) x
  · intro r _ x
    exact h.responseJets (vectorResponseCapVariance c Q b r) 3 (by omega) le_rfl x
  · intro r q
    exact ((hC r).fderiv_right (m := 2) (by norm_num)).continuous.measurable.comp (hXa q).measurable
  · intro r q
    exact (((hC r).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuous.measurable.comp (hXa q).measurable
  · intro sample
    change Continuous (fun r : ℝ≥0=>fderiv ℝ
      (vectorStepResponse (vectorResponseCapVariance c Q b r) m f g) (X r sample))
    simpa only [Function.comp_def] using (d.continuous_response_first m).comp (hp sample)
  · intro sample
    change Continuous (fun r : ℝ≥0=>vectorBilinearTrace (vectorHessian
      (vectorStepResponse (vectorResponseCapVariance c Q b r) m f g) (X r sample)))
    simpa only [Function.comp_def] using (d.continuous_response_trace m).comp (hp sample)

end QuantitativePaper
