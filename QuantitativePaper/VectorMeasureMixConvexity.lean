module
public import QuantitativePaper.VectorControlMix

@[expose] public section

/-! Actual measure convexity obtained from the proved vector control
verification and the independently constructed attaining feedback. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorWeightedParisiControlObjective_mix_le (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n → ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖ ≤ C) (hZn : ∀sample,0 ≤ Z sample) :
    vectorWeightedParisiControlObjective (Paper.parisiMix μ ν lam) β t A Z ≤
      (1-lam)*vectorWeightedParisiControlObjective μ β t A Z +
        lam*vectorWeightedParisiControlObjective ν β t A Z := by
  have hμ := integrable_vectorWeightedParisiControlPayoff μ β t ht A hA Z hZ C hC
  have hν := integrable_vectorWeightedParisiControlPayoff ν β t ht A hA Z hZ C hC
  have hm := integrable_vectorWeightedParisiControlPayoff (Paper.parisiMix μ ν lam) β t ht A hA Z hZ C hC
  have hh := integral_mono hm ((hμ.const_mul (1-lam)).add (hν.const_mul lam))
    (fun sample => by
      have hp := mul_le_mul_of_nonneg_left
        (vectorParisiControlPayoff_mix_le μ ν β t lam hlam A hA sample) (hZn sample)
      dsimp only [Pi.add_apply]
      nlinarith [hp])
  simp only [Pi.add_apply] at hh
  rw [integral_add (hμ.const_mul (1-lam)) (hν.const_mul lam),
    integral_const_mul,integral_const_mul] at hh
  exact hh

theorem integral_vectorMeasurePotential_mix_le_weighted (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖ ≤ C) (hZn : ∀sample,0 ≤ Z sample) :
    (∫sample,Z sample*vectorMeasurePotential (Paper.parisiMix μ ν lam) β t sample.1 0
      ∂vectorDisorderBrownianMeasure n) ≤
      (1-lam)*(∫sample,Z sample*vectorMeasurePotential μ β t sample.1 0
        ∂vectorDisorderBrownianMeasure n) +
      lam*(∫sample,Z sample*vectorMeasurePotential ν β t sample.1 0
        ∂vectorDisorderBrownianMeasure n) := by
  let A := vectorMeasureFeedbackControl (n := n) (Paper.parisiMix μ ν lam) β t ht
  have hA : IsVectorParisiControl A := isVectorParisiControl_vectorMeasureFeedbackControl _ β t ht
  rw [← vectorWeightedParisiControlObjective_feedback_eq_value _ β t ht Z hZ C hC]
  apply (vectorWeightedParisiControlObjective_mix_le μ ν β t ht lam hlam A hA Z
    (hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl) C hC hZn).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (vectorWeightedParisiControlObjective_le_value μ β t ht A hA Z hZ C hC hZn)
      (sub_nonneg.mpr hlam.2))
    (mul_le_mul_of_nonneg_left (vectorWeightedParisiControlObjective_le_value ν β t ht A hA Z hZ C hC hZn)
      hlam.1)

end QuantitativePaper
