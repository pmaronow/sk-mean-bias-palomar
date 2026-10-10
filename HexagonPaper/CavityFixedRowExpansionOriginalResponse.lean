module
public import HexagonPaper.CavityFixedRowExpansionLastEvaluation
public import HexagonPaper.CavityFixedRowExpansionDensityEvaluation
public import HexagonPaper.CavityFixedRowExpansionRestEvaluation
public import QuantitativeFollowup.FollowupCavityCppZeroResponseResults
public import QuantitativeFollowup.FollowupCavityCppZeroResponseEvaluatedAlgebra

@[expose] public section

/-! Actual three-group marked expectation and the literal diagonal-linear
zero response (275), for every profile. The physical derivative is supplied
by the proven native terminal-jet limit factory, never as a premise. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
open FourPapersCommon.FiniteStreamingPolynomials
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cavityFixedRowMarked_three_group_data_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let F:=fun z=>cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z+
      cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z+
      cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z
    Integrable F P ∧ (∫z,F z ∂P)=cavityScalarRestModifiedSeven D B μ a p+
      cavitySignedResponseT D μ a B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p := by
  dsimp only
  have hL:=cavityFixedRowLastResponseIntegrand_data_all_profiles μ n β ρ hβ hρ a p
  have hR:=cavityFixedRowRestResponseIntegrand_data_all_profiles μ n β ρ hβ hρ a p
  have hD:=cavityFixedRowDensityResponseIntegrand_data_all_profiles μ n β ρ hβ hρ a p
  refine ⟨(hL.1.add hR.1).add hD.1,?_⟩
  rw [integral_add
    (f:=fun z=>cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z+cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z)
    (g:=fun z=>cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z) (hL.1.add hR.1) hD.1,
    integral_add (f:=fun z=>cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z)
      (g:=fun z=>cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z) hL.1 hR.1,hL.2,hR.2,hD.2]
  have he:=cavityZeroResponse_evaluated_native_algebra
    (followupCavityRestSpinModel n β ρ hβ hρ) (followupCavityScalarBeta n β ρ)
    (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ a p
  dsimp only at he
  convert he using 1 <;> ring

theorem cavityFixedRowMarked_three_group_eq_printed_linear_response
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    followupCavityAlpha n β ρ*(∫z,cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z+
      cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z+
      cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z
      ∂anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      followupCavityLinearResponseRightSide n β ρ hβ hρ μ a p := by
  rw [(cavityFixedRowMarked_three_group_data_all_profiles μ n β ρ hβ hρ a p).2]
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let b:=followupCavityD n β ρ
  have hb:B≠0:=(followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
  have hbp:0<b:=followupCavityD_pos n β ρ hβ hρ
  have hB:B^2=b:=Real.sq_sqrt hbp.le
  have he:=cavityScalarRestModifiedSeven_eq_response_add_half_remainder D B hb μ a p
  rw [hB] at he
  have hnorm:cavityScalarRestModifiedSeven D B μ a p=
      (1/b)*scalarResponseOperator B hb μ a (cavityRestCovarianceColumn D μ a p) p+
        (1/2:ℝ)*cavityResponseFutureRemainder B D μ a p:=by
    apply mul_left_cancel₀ hbp.ne'
    rw [he]
    field_simp [hbp.ne']
    <;> ring
  change followupCavityAlpha n β ρ*(cavityScalarRestModifiedSeven D B μ a p+cavitySignedResponseT D μ a B hb p)=_
  rw [hnorm]
  unfold followupCavityLinearResponseRightSide
  dsimp only
  ring

theorem cavityOriginalCpp_zero_response_three_group
    (μ : Paper.ParisiMeasure) (n : ℕ) (hn : 0<n) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (p : Paper.Overlap) :
    withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 0=
      followupCavityAlpha n β ρ*(∫z,cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z+
        cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z+
        cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z
        ∂anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) := by
  rw [cavityFixedRowMarked_three_group_eq_printed_linear_response]
  exact followupCavityCpp_zero_response n hn β ρ hβ hρ μ a ha hμ p

theorem hasDerivWithinAt_cavityOriginalCpp_zero_printed_linear_response
    (μ : Paper.ParisiMeasure) (n : ℕ) (hn : 0<n) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (p : Paper.Overlap) :
    HasDerivWithinAt (followupCavityCppFunction n β ρ hβ hρ μ a p)
      (followupCavityLinearResponseRightSide n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 0 := by
  have hf:a≤Paper.parisiCDF μ 0:=by
    rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero] at hμ
    exact hμ
  have hd:=hasDerivWithinAt_followupCavityCppFunction_withinJet hn β ρ hβ hρ μ a ha hf p 0 0
    (show (0:ℝ)∈Icc 0 1 from ⟨le_rfl,zero_le_one⟩)
  change HasDerivWithinAt (followupCavityCppFunction n β ρ hβ hρ μ a p)
    (withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 0) (Icc (0:ℝ) 1) 0 at hd
  rw [followupCavityCpp_zero_response n hn β ρ hβ hρ μ a ha hμ p] at hd
  exact hd

end HexagonPaper
