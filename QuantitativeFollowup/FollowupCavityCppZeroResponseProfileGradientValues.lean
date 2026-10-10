module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileGradientIntegrand
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileRestartDerivative

@[expose] public section

/-! The true contracted initial-field derivative passes through the native
weak-profile tilt. The actual restart derivative limit is evaluated at the
moving same-driver state and actual earlier magnetization. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 750000
set_option maxSynthPendingDepth 128

theorem tendsto_cavitySignedResponseFutureGradient_profile_level
    (D : AnisotropicSpinModel n) {μ : ℕ→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ atTop (𝓝 ν)) (a : ℝ)
    {q r : ℕ→Paper.Overlap} {q₀ r₀ : Paper.Overlap}
    (hq : Tendsto q atTop (𝓝 q₀)) (hr : Tendsto r atTop (𝓝 r₀))
    (hqr : ∀j,q j≤r j) (hqr₀ : q₀≤r₀) :
    Tendsto (fun j=>cavitySignedResponseFutureGradient D (μ j) a (q j) (r j)) atTop
      (𝓝 (cavitySignedResponseFutureGradient D ν a q₀ r₀)) := by
  unfold cavitySignedResponseFutureGradient
  apply Tendsto.div_const
  refine tendsto_integral_anisotropicMeasureSampleLaw_profile_bounded D hμ a _ _ ?_
    (cavityNativeFutureGradientBound D) (cavityNativeFutureGradientBound_nonneg D) ?_ ?_
  · intro j
    exact (measurable_cavityNativeFutureGradientIntegrand D (μ j) (q j) (r j) (hqr j)).aestronglyMeasurable
  · intro j ω
    exact norm_cavityNativeFutureGradientIntegrand_le D (μ j) (q j) (r j) (hqr j) ω
  · exact .of_forall fun ω=>
      ((isBoundedBilinearMap_apply (𝕜:=ℝ) (E:=Field n) (F:=ℝ)).continuous.tendsto _).comp
        ((tendsto_anisotropicRestartMeanSquare_field_derivative_profile_moving D hμ ω.1
          hq hr hqr hqr₀ (tendsto_anisotropicMeasureState_profile_time D hμ hq ω)).prodMk_nhds
            (tendsto_anisotropicProcessMagnetization_profile_time D hμ hq ω))

end QuantitativeFollowup
