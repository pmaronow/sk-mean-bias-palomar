module
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceClosure
public import QuantitativeFollowup.FollowupCavityCppTaylorCubic

@[expose] public section

/-! The actual cubic Taylor theorem discharges the remainder input of the
physical trace closure. Only identification of the genuine zero derivative
with the printed response remains explicit in this supporting consumer. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open FourPapersCommon.FiniteStreamingPolynomials
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def followupCavityNativeClosureConstant (β : ℝ) : ℝ :=
  followupCavityClosureConstant β (followupCavityCppTaylorCubicConstant β)

theorem followupCavityNativeClosureConstant_one_le (β : ℝ) :
    1 ≤ followupCavityNativeClosureConstant β := by
  apply followupCavityClosureConstant_one_le
  exact followupCavityCppTaylorCubicConstant_nonneg β

theorem followup_cavity_contraction_of_zero_response (n : ℕ) (hn : 0 < n)
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
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 0)
        =ᵐ[parisiFreeMeasure μ a] followupCavityLinearResponseRightSide n β ρ hβ hρ μ a) :
    (3*ρ/4)*vectorIntegratedSelfOverlapVariance (n:=n+1) μ a β (1-ρ) (by linarith [hρ.1]) ≤
      followupCavityNativeClosureConstant β*
        (1/((n+1 : ℕ) : ℝ)+
          vectorInterpolationTraceError (n:=n+1) μ a β (1-ρ) (by linarith [hρ.1])+
          vectorMeanDirectionCovarianceIntegral (n:=n+1) μ a β (1-ρ) a (by linarith [hρ.1])+
          vectorIntegratedSelfOverlapCubic (n:=n+1) μ a β (1-ρ) (by linarith [hρ.1])) := by
  have haIcc : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, by linarith [ha.2]⟩
  have hfloor : a ≤ Paper.parisiCDF μ 0 := scalarFloor_cdf_lower hμ (by norm_num)
  have hCR : 0 ≤ followupCavityCppTaylorCubicConstant β :=
    followupCavityCppTaylorCubicConstant_nonneg β
  have hR : |followupCavityIntegratedTaylorRemainder n β ρ hβ hρ μ a| ≤
      followupCavityCppTaylorCubicConstant β*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ := by
    have h := (norm_integral_le_integral_norm
      (followupCavityCppTaylorRemainder n β ρ hβ hρ μ a)).trans
      (integral_norm_followupCavityCppTaylorRemainder_cubic_le hn β ρ hβ hρ μ a haIcc hfloor)
    simpa only [followupCavityIntegratedTaylorRemainder, Real.norm_eq_abs] using h
  exact followup_cavity_contraction_of_native_response_and_remainder n hn β ρ hβ hρ
    μ a ha hμ hmin ε hε hJ hResponse (followupCavityCppTaylorCubicConstant β) hCR hR

end QuantitativeFollowup
