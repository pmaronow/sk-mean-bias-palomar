module
public import QuantitativeFollowup.FollowupCavitySignedResponsePhysicalTransfer

@[expose] public section

/-! The literal signed response lemma at the actual isolated-spin
variance d of the physical cavity interpolation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n:ℕ}

theorem followup_signed_response_estimate (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (ha:a∈Icc (0:ℝ) 1) (hμ:μ∈scalarFloor a) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let β0:=followupCavityScalarBeta n β ρ
    let hβ0:β0≠0:=(followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
    |∫p,cavitySignedResponseT D μ a β0 hβ0 p∂parisiFreeMeasure μ a|≤
      cavitySignedResponseWeightedA D μ a β0+24*cavitySignedResponseWeightedJ D μ a β0 Finset.univ ∧
    followupCavityAlpha n β ρ*
      |∫p,cavitySignedResponseT D μ a β0 hβ0 p∂parisiFreeMeasure μ a|≤
      192*β^2*Real.exp (43*β^2)*
        ((∫q,foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q∂parisiFreeMeasure μ a)+
          followupSourceMeanCovarianceIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1])+
          1/((n+1:ℕ):ℝ)^2) := by
  dsimp only
  exact ⟨cavitySignedResponse_T_native_integral_bound _ hn μ a _ _ ha hμ,
    followup_cavity_signed_response_physical_transfer hn μ β ρ a _ hβ hρ _ ha hμ⟩

end QuantitativeFollowup
