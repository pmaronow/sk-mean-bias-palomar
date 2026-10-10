module
public import QuantitativePaper.VectorRestartState
public import QuantitativePaper.VectorBrownianPathEnvelope

@[expose] public section

/-! A single actual Wiener path envelope bounds every field displacement
of a genuine restarted arbitrary-measure diffusion. It is independent of
the profile and the initial disorder/field. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorRestartFieldPathEnvelope (β t : ℝ) (sample : VectorDisorderBrownianSample n) : ℝ :=
  ((1-t)*β^2)*Real.sqrt (n:ℝ)+Real.sqrt ((1-t)*β^2)*vectorBrownianPathEnvelope sample.2

theorem vectorRestartFieldPathEnvelope_nonneg (β t : ℝ) (ht : t≤1)
    (sample : VectorDisorderBrownianSample n) : 0≤vectorRestartFieldPathEnvelope β t sample := by
  unfold vectorRestartFieldPathEnvelope
  exact add_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _)
    (vectorBrownianPathEnvelope_nonneg _))

theorem measurable_vectorRestartFieldPathEnvelope (β t : ℝ) :
    Measurable (vectorRestartFieldPathEnvelope (n:=n) β t) :=
  measurable_const.add (measurable_const.mul
    ((measurable_vectorBrownianPathEnvelope n).comp measurable_snd))

theorem integrable_vectorBrownianPathEnvelope (n : ℕ) :
    Integrable (vectorBrownianPathEnvelope (n:=n)) (vectorBrownianMeasure n) := by
  apply (integrable_exp_vectorBrownianPathEnvelope (n:=n) 1).mono'
    (measurable_vectorBrownianPathEnvelope n).aestronglyMeasurable
  exact .of_forall fun sample=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (vectorBrownianPathEnvelope_nonneg sample)]
    simpa only [one_mul] using (show vectorBrownianPathEnvelope sample≤
      Real.exp (vectorBrownianPathEnvelope sample) by
        linarith [Real.add_one_le_exp (vectorBrownianPathEnvelope sample)])

theorem integrable_vectorRestartFieldPathEnvelope (β t : ℝ) :
    Integrable (vectorRestartFieldPathEnvelope (n:=n) β t) (vectorDisorderBrownianMeasure n) :=
  (integrable_const _).add (((integrable_vectorBrownianPathEnvelope n).comp_snd
    (completionLaw n)).const_mul _)

theorem norm_vectorRestartState_sub_initial_le_pathEnvelope (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    ‖vectorRestartState μ β t ht q p x r sample-x‖≤vectorRestartFieldPathEnvelope β t sample := by
  have hh:=norm_vectorAdditiveState_increment_le (vectorRestartDriftData μ β t ht q p)
    (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q) 0 r bot_le sample
  change ‖vectorRestartState μ β t ht q p x r sample-
      vectorRestartState μ β t ht q p x 0 sample‖≤_ at hh
  rw [vectorRestartState_zero,NNReal.coe_zero,sub_zero,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hh
  have he : disorderVectorBrownianIncrement (n:=n) 0 r sample=disorderVectorBrownian r sample := by
    simp [disorderVectorBrownianIncrement,disorderVectorBrownian,vectorBrownian_zero]
  rw [he] at hh
  change ‖vectorRestartState μ β t ht q p x r sample-x‖≤
    ((1-t)*β^2)*Real.sqrt (n:ℝ)*(r:ℝ)+Real.sqrt ((1-t)*β^2)*‖disorderVectorBrownian r sample‖ at hh
  apply hh.trans
  unfold vectorRestartFieldPathEnvelope
  exact add_le_add (mul_le_of_le_one_right (by positivity) (show (r:ℝ)≤1 from hr))
    (mul_le_mul_of_nonneg_left (norm_vectorBrownian_le_pathEnvelope r hr sample.2) (Real.sqrt_nonneg _))

end QuantitativePaper
