module
public import QuantitativePaper.VectorProfilePosteriorExponentialMoment
public import QuantitativePaper.VectorExponentialLocalization

@[expose] public section

/-! Actual uniform exponential envelopes for a fixed-disorder, fixed-field
restart. The original disorder remains an independent reference coordinate
for the localization tests. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 4000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorRestartExponentialEnvelope (β t K : ℝ) (x : Field n)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  Real.exp (|K| *(‖sample.1‖+‖x‖+vectorRestartFieldPathEnvelope β t sample))

theorem integrable_vectorRestartExponentialEnvelope (β t K : ℝ) (x : Field n) :
    Integrable (vectorRestartExponentialEnvelope β t K x) (vectorDisorderBrownianMeasure n) := by
  let c:=(1-t)*β^2
  have hi:=((integrable_exp_completion_norm n |K|).mul_prod
    (integrable_exp_vectorBrownianPathEnvelope (n:=n) (|K| *Real.sqrt c))).const_mul
      (Real.exp (|K| *(‖x‖+c*Real.sqrt (n:ℝ))))
  have he : vectorRestartExponentialEnvelope β t K x=
      (fun sample : VectorDisorderBrownianSample n=>Real.exp (|K| *(‖x‖+c*Real.sqrt (n:ℝ)))*
        (Real.exp (|K| *‖sample.1‖)*Real.exp ((|K| *Real.sqrt c)*vectorBrownianPathEnvelope sample.2))) := by
    funext sample
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    unfold vectorRestartExponentialEnvelope vectorRestartFieldPathEnvelope c
    ring
  rw [he]
  exact hi

theorem exp_vectorRestartState_and_disorder_le_envelope (μ : Paper.ParisiMeasure)
    (β t K : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    Real.exp (K*(‖sample.1‖+‖vectorRestartState μ β t ht q p x r sample‖))≤
      vectorRestartExponentialEnvelope β t K x sample := by
  apply Real.exp_le_exp.mpr
  have hX : ‖vectorRestartState μ β t ht q p x r sample‖≤
      ‖x‖+vectorRestartFieldPathEnvelope β t sample := by
    have hh:=norm_vectorRestartState_sub_initial_le_pathEnvelope μ β t ht q p x r hr sample
    have hn:=norm_add_le (vectorRestartState μ β t ht q p x r sample-x) x
    rw [sub_add_cancel] at hn
    linarith
  have hsum : ‖sample.1‖+‖vectorRestartState μ β t ht q p x r sample‖≤
      ‖sample.1‖+‖x‖+vectorRestartFieldPathEnvelope β t sample := by linarith
  exact (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
    (mul_le_mul_of_nonneg_left hsum (abs_nonneg K))

end QuantitativePaper
