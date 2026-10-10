module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseCheckpoint
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceIdentity

@[expose] public section

/-! The actual full-variance trace formula and sharp one-site bound. The
physical zero-response theorem discharges the supporting reducer's response
hypothesis; only the deterministic profile standing conditions remain. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open FourPapersCommon.FiniteStreamingPolynomials
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem followup_actual_full_variance_trace (n : ℕ) (hn : 0 < n)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1 : Paper.Overlap)}=0) :
    followupCavitySiteVariance n β ρ hρ μ a ∈ Icc (0 : ℝ) (1/4) ∧
      vectorIntegratedSelfOverlapVariance (n:=n+1) μ a β (1-ρ) (by linarith [hρ.1])=
        followupCavitySiteVariance n β ρ hρ μ a / ((n+1 : ℕ) : ℝ)+
        (n : ℝ)/((n+1 : ℕ) : ℝ)*
          (followupCavityAlpha n β ρ / followupCavityD n β ρ *
            followupCavityTraceMinus n β ρ hβ hρ μ a ha hμ-
            followupCavityAlpha n β ρ / 2 * followupCavityPenalty n β ρ hβ hρ μ a+
            followupCavityAlpha n β ρ *
              (∫p,cavitySignedResponseT (followupCavityRestSpinModel n β ρ hβ hρ) μ a
                (followupCavityScalarBeta n β ρ) (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p
                ∂parisiFreeMeasure μ a)+
            followupCavityIntegratedTaylorRemainder n β ρ hβ hρ μ a) := by
  have hfloor : a  ≤  Paper.parisiCDF μ 0 := by
    rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero] at hμ
    exact hμ
  exact ⟨followupCavitySiteVariance_bounds n β ρ hρ μ a ha,
    followup_full_variance_trace_identity_of_zero_response hn β ρ hβ hρ μ a ha hμ hfloor hone
      (followupCavityCpp_zero_response_ae n hn β ρ hβ hρ μ a ha hμ)⟩

end QuantitativeFollowup
