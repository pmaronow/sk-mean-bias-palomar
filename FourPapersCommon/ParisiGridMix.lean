module
public import Paper.ParisiCDFGrid
public import Paper.JTVariational

@[expose] public section

/-! The actual upward-grid pushforward commutes with admissible profile mixtures. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 900000

theorem parisiGridMeasure_mix (μ ν : Paper.ParisiMeasure) (N : ℕ) (θ : ℝ)
    (hθ : θ ∈ Icc (0 : ℝ) 1) :
    Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) N =
      Paper.parisiMix (Paper.parisiGridMeasure μ N) (Paper.parisiGridMeasure ν N) θ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Paper.parisiGridMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Paper.parisiMix_measure μ ν θ hθ,
    Measure.map_add _ _ (Paper.measurable_parisiGridRound N),
    Measure.map_smul _ (Paper.measurable_parisiGridRound N).aemeasurable,
    Measure.map_smul _ (Paper.measurable_parisiGridRound N).aemeasurable,
    Paper.parisiMix_measure _ _ θ hθ]
  rfl

end FourPapersCommon
