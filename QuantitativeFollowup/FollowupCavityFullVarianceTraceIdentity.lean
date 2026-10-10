module
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceIntegral
public import QuantitativeFollowup.FollowupCavityLinearResponseIntegral
public import QuantitativeFollowup.FollowupCavityCppNativeTaylor
public import QuantitativeFollowup.FollowupCavityCppTaylorMeasurable

@[expose] public section

/-! Integration of the actual endpoint and Taylor identities. Identification
of the genuine zero-coupling derivative with the printed response remains
explicit in these supporting reducers and is supplied by the physical
zero-response theorem in the final paper consumer. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open FourPapersCommon.FiniteStreamingPolynomials
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def followupCavityIntegratedTaylorRemainder (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ) : ℝ :=
  ∫p, followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p ∂parisiFreeMeasure μ a

theorem followup_full_variance_trace_identity_of_zero_response (hn : 0 < n)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (hfloor : a ≤ Paper.parisiCDF μ 0)
    (hone : parisiFreeMeasure μ a {(1 : Paper.Overlap)} = 0)
    (hResponse : (fun p : Paper.Overlap =>
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 0) =ᵐ[parisiFreeMeasure μ a]
        followupCavityLinearResponseRightSide n β ρ hβ hρ μ a) :
    vectorIntegratedSelfOverlapVariance (n:=n+1) μ a β (1-ρ) (by linarith [hρ.1]) =
      followupCavitySiteVariance n β ρ hρ μ a / ((n+1 : ℕ) : ℝ) +
      (n : ℝ)/((n+1 : ℕ) : ℝ) *
        (followupCavityAlpha n β ρ / followupCavityD n β ρ *
          followupCavityTraceMinus n β ρ hβ hρ μ a ha hμ -
          followupCavityAlpha n β ρ / 2 * followupCavityPenalty n β ρ hβ hρ μ a +
          followupCavityAlpha n β ρ *
            (∫p, cavitySignedResponseT (followupCavityRestSpinModel n β ρ hβ hρ) μ a
              (followupCavityScalarBeta n β ρ) (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p
              ∂parisiFreeMeasure μ a) +
          followupCavityIntegratedTaylorRemainder n β ρ hβ hρ μ a) := by
  have hiD := integrable_followupCavityLinearResponseRightSide n hn β ρ hβ hρ μ a ha hμ
  have hiR := integrable_followupCavityCppTaylorRemainder
    hn β ρ hβ hρ μ a ha hfloor
  have he : (∫p, followupCavityCpp n β ρ hβ hρ μ a 1 (by norm_num) p
      ∂parisiFreeMeasure μ a) =
      ∫p, (followupCavityLinearResponseRightSide n β ρ hβ hρ μ a p +
        followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p) ∂parisiFreeMeasure μ a := by
    apply integral_congr_ae
    filter_upwards [hResponse] with p hp
    have h := followupCavityCpp_taylor hn β ρ hβ hρ μ a ha hfloor p
    simpa only [hp] using h
  rw [integral_add hiD hiR,
    followupCavityLinearResponseRightSide_integral n hn β ρ hβ hρ μ a ha hμ hone] at he
  rw [followup_full_variance_trace_endpoint_integral hn μ β ρ a hβ hρ, he]
  unfold followupCavityIntegratedTaylorRemainder
  ring

end QuantitativeFollowup
