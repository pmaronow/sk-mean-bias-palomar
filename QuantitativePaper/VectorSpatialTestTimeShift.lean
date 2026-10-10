module
public import QuantitativePaper.VectorSpatialItoTestAt
public import QuantitativePaper.VectorSpatialItoTest

@[expose] public section

/-! The actual original adapted spatial tests retain the whole earlier
past when restricted to a deterministic later starting time. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def VectorSpatialItoTest.timeShift
    {f : ℝ≥0→VectorDisorderBrownianSample n→Field n→ℝ}
    {X : ℝ≥0→VectorDisorderBrownianSample n→Field n}
    (hf : VectorSpatialItoTest f X) (a : ℝ≥0) :
    VectorSpatialItoTestAt a (fun q=>f (a+q)) (fun q=>X (a+q)) where
  firstBound := hf.firstBound
  secondBound := hf.secondBound
  thirdBound := hf.thirdBound
  measurable := fun q=>hf.measurable (a+q)
  regularity := fun q=>hf.regularity (a+q)
  first_le := fun q=>hf.first_le (a+q)
  second_le := fun q=>hf.second_le (a+q)
  third_le := fun q=>hf.third_le (a+q)
  adapted_first := fun q r=>hf.adapted_first (a+q) (a+r)
  adapted_second := fun q r=>hf.adapted_second (a+q) (a+r)
  continuous_first_path := fun sample=>(hf.continuous_first_path sample).comp
    (continuous_const.add continuous_id)
  continuous_trace_path := fun sample=>(hf.continuous_trace_path sample).comp
    (continuous_const.add continuous_id)

end QuantitativePaper
