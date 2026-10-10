module
public import QuantitativePaper.VectorLinearBackwardBounds
public import QuantitativePaper.VectorColeHopfUniformJets
public import QuantitativePaper.VectorNormalizedHeatContinuity

@[expose] public section

/-! Analytic test data with uniform bounds derived from actual potential
and observable jets. No diffusion law or backward equation is an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

structure VectorResponseTestData (f g : Field n → ℝ) where
  potentialRegularity : ContDiff ℝ 3 f
  observableRegularity : ContDiff ℝ 3 g
  fieldLip : ℝ≥0
  lipschitz : LipschitzWith fieldLip f
  potentialPower : ℝ≥0
  potentialPower_ge_one : 1 ≤ potentialPower
  potentialJets : ∀ j,1 ≤ j → j ≤ 3 → ∀ x,
    ‖iteratedFDeriv ℝ j f x‖ ≤ (potentialPower : ℝ)^j
  observableBounds : ℕ → ℝ
  observableBounds_nonneg : ∀ j,0 ≤ observableBounds j
  observableJets : ∀ j,j ≤ 3 → ∀ x,‖iteratedFDeriv ℝ j g x‖ ≤ observableBounds j

structure VectorBackwardUniformBounds (f g : Field n → ℝ) (m : ℝ) where
  responsePower : ℝ≥0
  responsePower_ge_one : 1 ≤ responsePower
  potentialPower : ℝ≥0
  potentialPower_ge_one : 1 ≤ potentialPower
  responseRegularity : ∀ v,ContDiff ℝ 3 (vectorStepResponse v m f g)
  potentialRegularity : ∀ v,ContDiff ℝ 3 (vectorColeHopfStep v m f)
  responseJets : ∀ v j,1 ≤ j → j ≤ 3 → ∀ x,
    ‖iteratedFDeriv ℝ j (vectorStepResponse v m f g) x‖ ≤ (responsePower : ℝ)^j
  potentialJets : ∀ v j,1 ≤ j → j ≤ 3 → ∀ x,
    ‖iteratedFDeriv ℝ j (vectorColeHopfStep v m f) x‖ ≤ (potentialPower : ℝ)^j

theorem VectorResponseTestData.exists_bounds {f g : Field n → ℝ}
    (d : VectorResponseTestData f g) (m : ℝ) : Nonempty (VectorBackwardUniformBounds f g m) := by
  obtain ⟨B,hB,hR⟩ := vectorStepResponse_uniform_jets 3 f g d.potentialRegularity d.observableRegularity
    d.fieldLip d.lipschitz m d.potentialPower d.potentialPower.coe_nonneg
    d.observableBounds d.observableBounds_nonneg d.potentialJets d.observableJets
  obtain ⟨hU,D,hD,hUB⟩ := vectorColeHopfStep_smooth_uniform_jets 3 f d.potentialRegularity
    d.fieldLip d.lipschitz d.potentialPower (show 1 ≤ (d.potentialPower : ℝ) from d.potentialPower_ge_one)
    d.potentialJets m
  let A := finiteJetPowerBound B 3
  have hA := finiteJetPowerBound_ge_one B 3
  refine ⟨{
    responsePower := ⟨A,zero_le_one.trans hA⟩
    responsePower_ge_one := hA
    potentialPower := ⟨D,zero_le_one.trans hD⟩
    potentialPower_ge_one := hD
    responseRegularity := fun v=>(hR v).1
    potentialRegularity := hU
    responseJets := fun v j hj hjN x=>((hR v).2 j hjN x).trans
      (finite_jet_bound_le_power B 3 j hj hjN)
    potentialJets := hUB }⟩

def VectorResponseTestData.bounds {f g : Field n → ℝ} (d : VectorResponseTestData f g) (m : ℝ) :
    VectorBackwardUniformBounds f g m := Classical.choice (d.exists_bounds m)

def VectorResponseTestData.expDatum {f g : Field n → ℝ} (d : VectorResponseTestData f g) (m : ℝ) :
    VectorHeatDatum (fun x=>Real.exp (m*f x)) :=
  Classical.choice (vectorHeatDatum_exp f (d.potentialRegularity.of_le (by norm_num))
    d.fieldLip d.lipschitz m d.potentialPower d.potentialPower.coe_nonneg
    (fun j hj hjN=>d.potentialJets j hj (hjN.trans (by omega))))

def VectorResponseTestData.weightedDatum {f g : Field n → ℝ} (d : VectorResponseTestData f g) (m : ℝ) :
    VectorHeatDatum (fun x=>Real.exp (m*f x)*g x) :=
  Classical.choice (vectorHeatDatum_exp_observable f g
    (d.potentialRegularity.of_le (by norm_num)) (d.observableRegularity.of_le (by norm_num))
    d.fieldLip d.lipschitz m d.potentialPower d.potentialPower.coe_nonneg
    d.observableBounds d.observableBounds_nonneg
    (fun j hj hjN=>d.potentialJets j hj (hjN.trans (by omega)))
    (fun j hjN=>d.observableJets j (hjN.trans (by omega))))

theorem VectorResponseTestData.continuous_response_first {f g : Field n → ℝ}
    (d : VectorResponseTestData f g) (m : ℝ) :
    Continuous (fun p : ℝ×Field n=>fderiv ℝ (vectorStepResponse p.1 m f g) p.2) := by
  have hh := continuous_fderiv_vectorNormalizedHeat (d.weightedDatum m) (d.expDatum m)
    (fun _=>Real.exp_pos _)
  simpa only [vectorNormalizedHeat_exp_eq_stepResponse f g] using hh

theorem VectorResponseTestData.continuous_response_trace {f g : Field n → ℝ}
    (d : VectorResponseTestData f g) (m : ℝ) :
    Continuous (fun p : ℝ×Field n=>vectorBilinearTrace (vectorHessian (vectorStepResponse p.1 m f g) p.2)) := by
  have hh := continuous_vectorNormalizedHeat_trace (d.weightedDatum m) (d.expDatum m)
    (fun _=>Real.exp_pos _)
  simpa only [vectorNormalizedHeat_exp_eq_stepResponse f g] using hh

theorem VectorResponseTestData.continuous_generator {f g : Field n → ℝ}
    (d : VectorResponseTestData f g) (m : ℝ) :
    Continuous (fun p : ℝ×Field n=>vectorLinearBackwardGenerator
      (vectorStepResponse p.1 m f g) (vectorColeHopfStep p.1 m f) m p.2) := by
  have hd := continuous_vectorHeatLogGradient (d.expDatum m) (fun _=>Real.exp_pos _)
  have hp := (d.continuous_response_first m).clm_apply hd
  simp only [vectorHeatLogGradient_exp f m (d.expDatum m)] at hp
  exact ((d.continuous_response_trace m).div_const 2).add hp

end QuantitativePaper
