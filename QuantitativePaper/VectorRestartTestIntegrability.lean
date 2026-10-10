module
public import QuantitativePaper.VectorRestartExpectedContinuity

@[expose] public section

/-! Exponential-growth observables of the actual restarted state are
integrable at every physical endpoint, using the genuine path envelope. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integrable_vectorRestart_exp_test (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (r : ℝ≥0) (hr : r≤1) (F : Field n→ℝ) (hF : Continuous F)
    (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hbound : ∀y,|F y|≤C*Real.exp (R*‖y‖)) :
    Integrable (fun sample=>F (vectorRestartState μ β t ht q p x r sample))
      (vectorDisorderBrownianMeasure n) := by
  apply ((integrable_vectorRestartExponentialEnvelope β t R x).const_mul C).mono'
  · exact (hF.measurable.comp
      ((measurable_uncurry_vectorRestartState μ β t ht q p x).of_uncurry_left)).aestronglyMeasurable
  · exact .of_forall fun sample=>by
      rw [Real.norm_eq_abs]
      apply (hbound _).trans (mul_le_mul_of_nonneg_left _ hC)
      apply le_trans _ (exp_vectorRestartState_and_disorder_le_envelope μ β t R ht q p x r hr sample)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by linarith [norm_nonneg sample.1]) hR)

end QuantitativePaper
