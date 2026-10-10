module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseResults
public import QuantitativeFollowup.FollowupCavityLinearResponseIntegral

@[expose] public section

/-! Actual integrated diagonal-linear response. The derivative is identified
by the proved scalar/rest physical response, then integrated using the genuine
trace-class covariance and signed-response objects. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open FourPapersCommon.FiniteStreamingPolynomials
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

theorem integrable_followupCavityCpp_zero_firstJet (n : ℕ) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) :
    Integrable (fun p=>withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p)
      (Icc (0:ℝ) 1) 1 0) (parisiFreeMeasure μ a):=by
  exact (integrable_followupCavityLinearResponseRightSide n hn β ρ hβ hρ μ a ha hfloor).congr
    (followupCavityCpp_zero_response_ae n hn β ρ hβ hρ μ a ha hfloor).symm

theorem followupCavityCpp_zero_response_integral (n : ℕ) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    (∫p,withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p)
      (Icc (0:ℝ) 1) 1 0 ∂parisiFreeMeasure μ a)=
      followupCavityAlpha n β ρ*
        ((1/followupCavityD n β ρ)*followupCavityTraceMinus n β ρ hβ hρ μ a ha hfloor-
          followupCavityPenalty n β ρ hβ hρ μ a/2+
          ∫p,cavitySignedResponseT (followupCavityRestSpinModel n β ρ hβ hρ) μ a
            (followupCavityScalarBeta n β ρ) (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p
            ∂parisiFreeMeasure μ a):=by
  exact (integral_congr_ae
    (followupCavityCpp_zero_response_ae n hn β ρ hβ hρ μ a ha hfloor)).trans
    (followupCavityLinearResponseRightSide_integral n hn β ρ hβ hρ μ a ha hfloor hone)

end QuantitativeFollowup
