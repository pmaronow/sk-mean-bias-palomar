module
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceNativeRemainder
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceStability
public import QuantitativeFollowup.FollowupCavityStableDefectModel

@[expose] public section

/-! Assemble the actual reference-error criterion, native cubic remainder,
and stable defect estimate. Identification of the actual zero response is
explicit until the separate posterior calculation supplies it. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open FourPapersCommon.FiniteStreamingPolynomials
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def followupCavityNativeStableDefectConstant (β : ℝ) : ℝ :=
  followupCavityStableDefectConstant β (followupCavityNativeClosureConstant β)

theorem followupCavityNativeStableDefectConstant_pos (β : ℝ) (hβ : 1 < β) :
    0 < followupCavityNativeStableDefectConstant β :=
  followupCavityStableDefectConstant_pos β _ hβ (followupCavityNativeClosureConstant_one_le β)

theorem followup_cavity_stable_defect_of_zero_response
    (N : ℕ) (hN : 2 ≤ N) (β : ℝ) (hβ : 1 < β)
    (μ : Paper.ParisiMeasure) (lam ρ : ℝ)
    (hlam : lam ∈ Ioc (0 : ℝ) (min 1 (β/4))) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (hNr : (N : ℝ)⁻¹ ≤ ρ) (hμ : μ ∈ scalarFloor (lam/β))
    (hmin : ∀ν ∈ scalarFloor (lam/β),
      vectorMeasureFunctional N μ β (1-ρ) (lam/β) ≤
        vectorMeasureFunctional N ν β (1-ρ) (lam/β))
    (hstable : scalarOperatorStabilityError β μ (followupScalarCoefficient N β ρ) ≤ ρ/4)
    (hResponse : (fun p : Paper.Overlap =>
      withinJet (followupCavityCppFunction (N-1) β ρ (zero_lt_one.trans hβ) hρ μ (lam/β) p)
        (Icc 0 1) 1 0) =ᵐ[parisiFreeMeasure μ (lam/β)]
        followupCavityLinearResponseRightSide (N-1) β ρ (zero_lt_one.trans hβ) hρ μ (lam/β)) :
    β*vectorInterpolationDefect (n:=N) μ (lam/β) β (1-ρ) (by linarith [hρ.1]) ≤
      followupCavityNativeStableDefectConstant β*(Real.log (2+(N : ℝ)))^2/
        ((N : ℝ)*lam*ρ^2) := by
  have hn : 0 < N-1 := by omega
  have hsucc : N-1+1=N := by omega
  have hβp : 0 < β := zero_lt_one.trans hβ
  have hlamQuarter : lam ≤ β/4 := hlam.2.trans (min_le_right _ _)
  have ha : lam/β ∈ Ioc (0 : ℝ) (1/2) :=
    ⟨div_pos hlam.1 hβp, (div_le_iff₀ hβp).mpr (by linarith)⟩
  have haIcc : lam/β ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, by linarith [ha.2]⟩
  obtain ⟨ε,hε,hJ⟩ := followupCavity_quadratic_order_of_reference_error
    (N-1) hn β ρ hβ hρ μ (lam/β) haIcc hμ (by simpa only [hsucc] using hstable)
  have hcontract := followup_cavity_contraction_of_zero_response (N-1) hn β ρ hβp hρ
    μ (lam/β) ha hμ (by simpa only [hsucc] using hmin) ε hε hJ hResponse
  have hcontract' : (3*ρ/4)*
      vectorIntegratedSelfOverlapVariance (n:=N) μ (lam/β) β (1-ρ) (by linarith [hρ.1]) ≤
      followupCavityNativeClosureConstant β*((N : ℝ)⁻¹+
        vectorInterpolationTraceError (n:=N) μ (lam/β) β (1-ρ) (by linarith [hρ.1])+
        vectorMeanDirectionCovarianceIntegral (n:=N) μ (lam/β) β (1-ρ) (lam/β)
          (by linarith [hρ.1])+
        vectorIntegratedSelfOverlapCubic (n:=N) μ (lam/β) β (1-ρ) (by linarith [hρ.1])) := by
    simpa only [hsucc, one_div] using hcontract
  exact followupCavityStableDefect_of_contraction N hN β (followupCavityNativeClosureConstant β)
    hβ (followupCavityNativeClosureConstant_one_le β) μ lam ρ
    ⟨hlam.1, by linarith⟩ hρ hNr hμ hmin hcontract'

end QuantitativeFollowup
