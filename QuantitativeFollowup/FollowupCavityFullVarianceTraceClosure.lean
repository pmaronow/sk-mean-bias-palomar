module
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceIdentity
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceOrder
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceNotation
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceAlgebra
public import QuantitativeFollowup.FollowupCavitySignedResponseLemma
public import QuantitativeFollowup.FollowupCavityFourRestVarianceComparison
public import QuantitativeFollowup.FollowupCavityThirdRestMomentThermalIntegral

@[expose] public section

/-! Closure at the actual model scope. The genuine zero-response and
actual Taylor norm estimate are the two remaining explicit inputs in
this supporting consumer, before the final native response wrapper. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open FourPapersCommon.FiniteStreamingPolynomials
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem followup_cavity_contraction_of_native_response_and_remainder (n : ℕ) (hn : 0 < n)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) (1/2))
    (hμ : μ ∈ scalarFloor a)
    (hmin : ∀ν ∈ scalarFloor a, vectorMeasureFunctional (n+1) μ β (1-ρ) a ≤
      vectorMeasureFunctional (n+1) ν β (1-ρ) a)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) (ρ/4))
    (hJ : ∀f : endpointFixedL2 (parisiFreeMeasure μ a),
      inner ℝ f (scalarResponseL2Operator (followupCavityScalarBeta n β ρ)
        (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ a
        ⟨ha.1.le, by linarith [ha.2]⟩ hμ f) ≤ (1+ε)*‖f‖^2)
    (hResponse : (fun p : Paper.Overlap =>
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 0) =ᵐ[parisiFreeMeasure μ a]
        followupCavityLinearResponseRightSide n β ρ hβ hρ μ a)
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hRem : |followupCavityIntegratedTaylorRemainder n β ρ hβ hρ μ a| ≤
      CR*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ) :
    (3*ρ/4)*vectorIntegratedSelfOverlapVariance (n:=n+1) μ a β (1-ρ) (by linarith [hρ.1]) ≤
      followupCavityClosureConstant β CR*
        (1/((n+1 : ℕ) : ℝ)+
          vectorInterpolationTraceError (n:=n+1) μ a β (1-ρ) (by linarith [hρ.1])+
          vectorMeanDirectionCovarianceIntegral (n:=n+1) μ a β (1-ρ) a (by linarith [hρ.1])+
          vectorIntegratedSelfOverlapCubic (n:=n+1) μ a β (1-ρ) (by linarith [hρ.1])) := by
  have hN : 0 < n+1 := by omega
  have ht : 1-ρ < 1 := by linarith [hρ.1]
  have haIcc : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, by linarith [ha.2]⟩
  have haIoo : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  have hfloor : a ≤ Paper.parisiCDF μ 0 := scalarFloor_cdf_lower hμ (by norm_num)
  have hone := followupCavity_minimizer_no_upper_atom hN μ β (1-ρ) a hβ.ne' ht haIoo hμ hmin
  have hTrace := followup_full_variance_trace_identity_of_zero_response
    hn β ρ hβ hρ μ a haIcc hμ hfloor hone hResponse
  have hOrder := followupCavity_scaled_trace_le_of_quadratic_order
    n hn β ρ hβ hρ μ a haIcc hμ hone ε hε hJ
  have hSigned := (followup_signed_response_estimate hn μ β ρ a hβ hρ haIcc hμ).2
  have hComparison := followup_cavity_four_rest_variance_comparison
    hn μ β ρ a hβ hρ haIoo hμ hmin
  have hThermal := followup_cavity_third_rest_moment_thermal hn μ β ρ a hβ hρ haIcc hfloor
  rw [followupCavity_thermal_trace_integral,
    followupCavity_source_covariance_integral hN μ β (1-ρ) a hβ.ne' ht] at hSigned hThermal
  rw [followupCavity_source_cubic_integral] at hThermal
  rw [followupCavity_source_variance_integral hN] at hComparison
  have hV : 0 ≤ vectorIntegratedSelfOverlapVariance (n:=n+1) μ a β (1-ρ) ht.le := by
    rw [vectorIntegratedSelfOverlapVariance_eq_free_integral hN]
    exact integral_nonneg fun q => variance_nonneg _ _
  have hA : 0 ≤ vectorInterpolationTraceError (n:=n+1) μ a β (1-ρ) ht.le := by
    rw [←followupCavity_thermal_trace_integral]
    exact integral_nonneg fun q => foundationThermalTrace_nonneg μ β (1-ρ) a ht.le q
  have hCov : 0 ≤ vectorMeanDirectionCovarianceIntegral (n:=n+1) μ a β (1-ρ) a ht.le :=
    integral_nonneg fun q => (vectorMeanDirectionCovariance_nonneg_le_one hN μ β (1-ρ) a hβ.ne' ht q).1
  have hH : 0 ≤ vectorIntegratedSelfOverlapCubic (n:=n+1) μ a β (1-ρ) ht.le := by
    rw [vectorIntegratedSelfOverlapCubic_eq_free_integral]
    exact integral_nonneg fun q => integral_nonneg fun z => by positivity
  have hVm := cavityRestVariance_nonneg (followupCavityRestSpinModel n β ρ hβ hρ) μ a
  have hSite := (followupCavitySiteVariance_bounds n β ρ hρ μ a haIcc).2
  have hAlpha := followupCavityAlpha_nonneg n β ρ hρ.2
  have hPenalty : 0 ≤ followupCavityAlpha n β ρ/2*followupCavityPenalty n β ρ hβ hρ μ a :=
    mul_nonneg (by positivity) (cavityResidualPenalty_nonneg _ _ μ a)
  have hSigned' : |followupCavityAlpha n β ρ *
      (∫p, cavitySignedResponseT (followupCavityRestSpinModel n β ρ hβ hρ) μ a
        (followupCavityScalarBeta n β ρ) (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p
        ∂parisiFreeMeasure μ a)| ≤
      192*β^2*Real.exp (43*β^2)*
        (vectorInterpolationTraceError (n:=n+1) μ a β (1-ρ) ht.le+
          vectorMeanDirectionCovarianceIntegral (n:=n+1) μ a β (1-ρ) a ht.le+
          1/((n+1 : ℕ) : ℝ)^2) := by
    simpa only [abs_mul, abs_of_nonneg hAlpha] using hSigned
  exact cavityFullTrace_scalar_closure n hn β ρ CR _ _ _ _ _ _ _ _ _ _ _
    hρ hCR hV hVm hSite hPenalty hA hCov hH hTrace hOrder hSigned' hRem hThermal hComparison

end QuantitativeFollowup
