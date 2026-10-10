module
public import QuantitativePaper.VectorUniformVarianceJets

@[expose] public section

/-! Actual field Cole--Hopf regularity with spatial bounds uniform in all
variances. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem gaussianShiftColeHopf_eq_vectorStep (f : Field n → ℝ) (v m : ℝ) :
    gaussianShiftColeHopf (Real.sqrt v • ContinuousLinearMap.id ℝ (Field n)) m f=
      vectorColeHopfStep v m f := by
  funext x
  simp only [gaussianShiftColeHopf,gaussianShiftAverage,gaussianShiftPartition,
    vectorColeHopfStep,vectorStepPartition,fieldShift,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]

theorem vectorColeHopfStep_smooth_uniform_jets (N : ℕ) (f : Field n → ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 1 ≤ K)
    (hjets : ∀ j,1 ≤ j → j ≤ N → ∀ x,‖iteratedFDeriv ℝ j f x‖ ≤ K^j)
    (m : ℝ) :
    (∀ v,ContDiff ℝ N (vectorColeHopfStep v m f)) ∧
    ∃ D : ℝ,1 ≤ D ∧ ∀ v j,1 ≤ j → j ≤ N → ∀ x,
      ‖iteratedFDeriv ℝ j (vectorColeHopfStep v m f) x‖ ≤ D^j := by
  obtain ⟨D,hD,hB⟩ := gaussianShiftColeHopf_uniform_shift_jets N f hf L hlip K hK hjets m
  refine ⟨fun v=>?_,D,hD,fun v j hj hjN x=>?_⟩
  · have hh := (gaussianShiftColeHopf_smooth_bounded_jets N f hf L hlip K hK hjets
      (Real.sqrt v • ContinuousLinearMap.id ℝ (Field n)) m).1
    rw [gaussianShiftColeHopf_eq_vectorStep] at hh
    exact hh
  · have hh := hB (Real.sqrt v • ContinuousLinearMap.id ℝ (Field n)) j hj hjN x
    rw [gaussianShiftColeHopf_eq_vectorStep] at hh
    exact hh

end QuantitativePaper
