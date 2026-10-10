module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexSourceDerivatives
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternNormalizerTerminalRepresentation

@[expose] public section

/-! The normalizer term is a product of two genuinely independent
terminal expectations. Its parameter derivative retains both source
responses and holds at the two physical parameter endpoints. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem normalizerSource_binary_schedule_antitone (l : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule l) := by
  apply antitone_nat_of_succ_le
  intro j
  cases j with
  | zero => exact l.property.2
  | succ j =>
    cases j with
    | zero => exact l.property.1
    | succ j => simp only [anisotropicBinaryObservationSchedule,le_refl]

theorem hasDerivWithinAt_nativeStreamingPattern_normalizer_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (l : Paper.Overlap) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D := followupCavitySpinModel n β ρ hβ hρ u hu
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.normalizer l))
      ((followupCavityAlpha n β ρ/2)*
        (nativeStreamingSourceSixBracket D μ a q T F *
          nativeStreamingOldTerminalExpectation D μ a (anisotropicBinaryObservationSchedule l)
            anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n l) +
        nativeStreamingOldTerminalExpectation D μ a q T F *
          nativeStreamingSourceSixBracket D μ a (anisotropicBinaryObservationSchedule l)
            anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n l)))
      (Icc (0:ℝ) 1) u := by
  dsimp only
  have ho := hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F u hu
  have hb := hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
    (anisotropicBinaryObservationSchedule l) (normalizerSource_binary_schedule_antitone l)
    (by norm_num) rfl rfl anisotropicBinaryObservationTree
    (nativeStreamingNormalizerBinaryTerminalTest n l) u hu
  have hp := ho.mul hb
  apply (hp.congr_of_mem ?_ hu).congr_deriv
  · rw [followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a q T F u hu,
      followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule l) anisotropicBinaryObservationTree
        (nativeStreamingNormalizerBinaryTerminalTest n l) u hu]
    ring
  · intro v hv
    simp only [nativeStreamingPatternParameterMoment,dif_pos hv,Pi.mul_apply]
    rw [nativeStreamingPatternMoment_normalizer_eq_terminal_product,
      followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a q T F v hv,
      followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule l) anisotropicBinaryObservationTree
        (nativeStreamingNormalizerBinaryTerminalTest n l) v hv]

end QuantitativeFollowup
