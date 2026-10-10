module
public import QuantitativePaper.VectorResponseIntervalMartingale

@[expose] public section

/-! The literal variance-zero boundary and actual bounded response limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem vectorStepResponse_zero (f g : Field n→ℝ) (m : ℝ) (x : Field n) :
    vectorStepResponse 0 m f g x=g x := by
  simp [vectorStepResponse,vectorStepWeight,vectorStepPartition,fieldShift,Real.exp_ne_zero]

theorem VectorResponseTestData.response_bound {f g : Field n→ℝ}
    (d : VectorResponseTestData f g) (m v : ℝ) (x : Field n) :
    |vectorStepResponse v m f g x|≤d.observableBounds 0 := by
  apply abs_vectorStepResponse_le f g d.fieldLip d.lipschitz
  intro y
  simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using d.observableJets 0 (by omega) y

theorem VectorResponseTestData.tendsto_response_zero {f g : Field n→ℝ}
    (d : VectorResponseTestData f g) (m : ℝ) {α : Type*} {l : Filter α}
    {v : α→ℝ} {x : α→Field n} {x0 : Field n}
    (hv : Tendsto v l (𝓝 0)) (hx : Tendsto x l (𝓝 x0)) :
    Tendsto (fun i=>vectorStepResponse (v i) m f g (x i)) l (𝓝 (g x0)) := by
  have hg (y : Field n) : |g y|≤d.observableBounds 0 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using d.observableJets 0 (by omega) y
  have hh := (continuous_vectorStepResponse_variance_field f g d.fieldLip d.lipschitz
    d.observableRegularity.continuous (d.observableBounds 0) hg m).continuousAt.tendsto.comp
      (hv.prodMk_nhds hx)
  simpa only [Function.comp_def,vectorStepResponse_zero] using hh

end QuantitativePaper
