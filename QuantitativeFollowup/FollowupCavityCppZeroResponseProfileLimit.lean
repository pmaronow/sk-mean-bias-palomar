module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileColumns
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileT12
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileT3Algebra
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileStrictGradient
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfilePenalty
public import QuantitativeFollowup.FollowupCavityLinearResponseIntegral

@[expose] public section

/-! The literal native diagonal-linear right-hand side is the actual
limit of its atom-preserving finite-profile counterparts. Every term is
passed through its real model law; neither the response identity nor a
convergence premise is an input. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128

theorem tendsto_cavitySignedResponseT_preserving (D : AnisotropicSpinModel n) (hn : 0<n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (p : Paper.Overlap) (hp : p∈S) (a β : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hfloor : μ∈scalarFloor a) (hβ : β≠0) :
    Tendsto (fun N=>cavitySignedResponseT D (FRSB.preservingMeasure μ S N) a β hβ p)
      atTop (𝓝 (cavitySignedResponseT D μ a β hβ p)) := by
  unfold cavitySignedResponseT cavitySignedResponseT2 cavitySignedResponseT3
  exact ((tendsto_cavitySignedResponseT1_preserving D μ S hzero a β ha hfloor hβ p).add
    ((tendsto_cavitySignedResponseT2First_preserving D μ S hzero a β ha hfloor hβ p).add
      (tendsto_cavitySignedResponseT2Double_preserving D μ S hzero a β ha hfloor hβ p))).add
    (((tendsto_cavitySignedResponseT3Diagonal_preserving D μ S p hp a β hβ).sub
      (tendsto_cavitySignedResponseStrictGradientIntegral_preserving D hn μ S hzero p hp a β ha hfloor hβ)).sub
      (tendsto_cavitySignedResponseT3LastHessian_preserving D μ S hzero p a β ha hfloor hβ))

theorem tendsto_followupCavityLinearResponseRightSide_preserving
    (n : ℕ) (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (p : Paper.Overlap) (hp : p∈S) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) :
    Tendsto (fun N=>followupCavityLinearResponseRightSide n β ρ hβ hρ
      (FRSB.preservingMeasure μ S N) a p) atTop
      (𝓝 (followupCavityLinearResponseRightSide n β ρ hβ hρ μ a p)) := by
  let D := followupCavityRestSpinModel n β ρ hβ hρ
  let β0 := followupCavityScalarBeta n β ρ
  have hb : β0≠0 := (followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
  have hμ := FRSB.tendsto_preservingMeasure μ S
  have hJ := tendsto_scalarResponseOperator_profile_covariance D β0 hb a ha
    (fun N=>nativeStreaming_preserving_floor μ S hzero a hfloor N) hfloor hμ
    (tendsto_const_nhds (x:=p))
  have hT := tendsto_cavitySignedResponseT_preserving D hn μ S hzero p hp a β0 ha hfloor hb
  have hR := tendsto_cavityResponseFutureRemainder_preserving β0 hb D μ S hzero p hp a ha hfloor
  exact (((hJ.const_mul (1/followupCavityD n β ρ)).add hT).add
    (hR.const_mul (1/2:ℝ))).const_mul (followupCavityAlpha n β ρ)

theorem tendsto_followupCavityLinearResponseRightSide_prescribed
    (n : ℕ) (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hfloor : μ∈scalarFloor a) :
    Tendsto (fun N=>followupCavityLinearResponseRightSide n β ρ hβ hρ
      (FRSB.preservingMeasure μ {zeroOverlap,p} N) a p) atTop
      (𝓝 (followupCavityLinearResponseRightSide n β ρ hβ hρ μ a p)) :=
  tendsto_followupCavityLinearResponseRightSide_preserving n hn β ρ hβ hρ μ
    {zeroOverlap,p} (by simp) p (by simp) a ha hfloor

end QuantitativeFollowup
