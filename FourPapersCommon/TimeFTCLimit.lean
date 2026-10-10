module
public import FourPapersCommon.TimeFTCPartitionExpectation
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! The literal time-FTC partition converges in expectation, including zero
horizon. Its quantitative finite-mesh estimate is proved in the preceding
module, and the only stochastic input is the genuine L1 increment estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal Topology
namespace FourPapersCommon
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {T : ℝ≥0} (P : Measure Ω) [IsProbabilityMeasure P]

theorem tendsto_integral_timeRightPartitionSum (d : TimeFTCData Ω E T)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (Z : Ω → ℝ) (hZ : Measurable Z) (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖ ≤ C)
    (A D : ℝ≥0)
    (hi : ∀ r t : ℝ≥0,r ≤ t → t ≤ T →
      Integrable (fun sample => ‖X t sample-X r sample‖) P)
    (hinc : ∀ r t : ℝ≥0,r ≤ t → t ≤ T →
      (∫ sample,‖X t sample-X r sample‖ ∂P) ≤ A*Real.sqrt ((t : ℝ)-r)+D*((t : ℝ)-r)) :
    Tendsto (fun N => ∫ sample,timeRightPartitionSum d X Z (N+1) sample ∂P) atTop
      (𝓝 (∫ sample,timeFTCIntegral d X Z sample ∂P)) := by
  have hmesh : Tendsto (fun N : ℕ => (T : ℝ)/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).comp (tendsto_add_atTop_nat 1)
  have hroot : Tendsto (fun N : ℕ => Real.sqrt ((T : ℝ)/((N : ℝ)+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hmesh
  have hb : Tendsto (fun N : ℕ => (C : ℝ)*d.spatialLip*T*
      (A*Real.sqrt ((T : ℝ)/((N : ℝ)+1))+D*((T : ℝ)/((N : ℝ)+1)))) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (((hroot.const_mul (A : ℝ)).add (hmesh.const_mul (D : ℝ))).const_mul
        ((C : ℝ)*d.spatialLip*T))
  have hdiff : Tendsto (fun N : ℕ => (∫ sample,timeRightPartitionSum d X Z (N+1) sample ∂P)-
      ∫ sample,timeFTCIntegral d X Z sample ∂P) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => ?_) hb
    simpa only [Real.norm_eq_abs,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using
      (timeRightPartitionSum_expectation_error_bound P d X hX Z hZ C hC A D hi hinc (Nat.succ_pos N)).2
  simpa only [sub_add_cancel,zero_add] using
    hdiff.add_const (∫ sample,timeFTCIntegral d X Z sample ∂P)

end FourPapersCommon
