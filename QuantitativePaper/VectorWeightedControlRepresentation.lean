module
public import QuantitativePaper.VectorWeightedFeedbackGap

@[expose] public section

/-! Genuine arbitrary-profile vector control representation with bounded
initial-filtration weights, including the literal zero-diffusion endpoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorWeightedParisiControlObjective (μ : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (Z : VectorDisorderBrownianSample n→ℝ) : ℝ :=
  ∫sample,Z sample*(vectorTerminalPotential n β t sample.1
    (vectorControlledState ((1-t)*β^2) μ A 1 sample)-
      vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample) ∂vectorDisorderBrownianMeasure n

theorem integrable_vectorWeightedParisiControlPayoff (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(vectorTerminalPotential n β t sample.1
      (vectorControlledState ((1-t)*β^2) μ A 1 sample)-
        vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample)) (vectorDisorderBrownianMeasure n) :=
  (integrable_vectorParisiControlPayoff μ β t ht A hA).bdd_mul
    hZ.aestronglyMeasurable (Eventually.of_forall hC)

theorem vectorWeightedParisiControlObjective_eq_gap_add_value (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    vectorWeightedParisiControlObjective μ β t A Z=
      (∫sample,Z sample*vectorMeasureControlGap μ β t A sample ∂vectorDisorderBrownianMeasure n)+
      (∫sample,Z sample*vectorMeasurePotential μ β t sample.1 0 ∂vectorDisorderBrownianMeasure n) := by
  have hu := ((integrable_vectorMeasurePotential μ β t ht (0 : Field n)).comp_fst (vectorBrownianMeasure n)).bdd_mul
    hZ.aestronglyMeasurable (Eventually.of_forall hC)
  have hg := (integrable_vectorMeasureControlGap_all μ β t ht A hA).bdd_mul
    hZ.aestronglyMeasurable (Eventually.of_forall hC)
  have he : (fun sample=>Z sample*(vectorTerminalPotential n β t sample.1
      (vectorControlledState ((1-t)*β^2) μ A 1 sample)-
        vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample))=
      (fun sample=>Z sample*vectorMeasureControlGap μ β t A sample+Z sample*vectorMeasurePotential μ β t sample.1 0) := by
    funext sample
    unfold vectorMeasureControlGap
    ring
  unfold vectorWeightedParisiControlObjective
  rw [he,integral_add hg hu]

theorem vectorWeightedParisiControlObjective_le_value (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) (hZn : ∀sample,0≤Z sample) :
    vectorWeightedParisiControlObjective μ β t A Z≤
      ∫sample,Z sample*vectorMeasurePotential μ β t sample.1 0 ∂vectorDisorderBrownianMeasure n := by
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  rw [vectorWeightedParisiControlObjective_eq_gap_add_value μ β t ht A hA Z hZg C hC]
  suffices (∫sample,Z sample*vectorMeasureControlGap μ β t A sample ∂vectorDisorderBrownianMeasure n)≤0 by linarith
  by_cases hβ : β=0
  · simp_rw [vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [hβ]) A]
    simp
  by_cases he : t=1
  · simp_rw [vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [he]) A]
    simp
  exact integral_vectorMeasureControlGap_weighted_le_zero μ β t hβ (lt_of_le_of_ne ht he) A hA Z hZ C hC hZn

theorem vectorWeightedParisiControlObjective_feedback_eq_value (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    vectorWeightedParisiControlObjective μ β t (vectorMeasureFeedbackControl (n := n) μ β t ht) Z=
      ∫sample,Z sample*vectorMeasurePotential μ β t sample.1 0 ∂vectorDisorderBrownianMeasure n := by
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  rw [vectorWeightedParisiControlObjective_eq_gap_add_value μ β t ht _
    (isVectorParisiControl_vectorMeasureFeedbackControl μ β t ht) Z hZg C hC]
  suffices (∫sample,Z sample*vectorMeasureControlGap μ β t (vectorMeasureFeedbackControl μ β t ht) sample
      ∂vectorDisorderBrownianMeasure n)=0 by rw [this,zero_add]
  by_cases hβ : β=0
  · simp_rw [vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [hβ])]
    simp
  by_cases he : t=1
  · simp_rw [vectorMeasureControlGap_zero_diffusion μ β t ht (by simp [he])]
    simp
  exact integral_vectorMeasureControlGap_feedback_weighted_eq_zero μ β t hβ (lt_of_le_of_ne ht he) Z hZ C hC

end QuantitativePaper
