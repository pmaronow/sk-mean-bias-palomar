module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteExpectation
public import QuantitativeFollowup.FollowupCavityCppZeroResponseEvaluatedAlgebra
public import QuantitativeFollowup.FollowupCavityLinearResponseIntegral

@[expose] public section

/-! The printed diagonal-linear response at every original finite-profile
observation, derived from the actual physical first response and the
genuine scalar/rest marked expectations. No response equality is an input. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open FourPapersCommon.FiniteStreamingPolynomials
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem native_cpp_firstJet_scheme_zero_eq_seven_add_native_T
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2) :
    let μ:=Paper.parisiSchemeMeasure s
    let p:=anisotropicSchemeNode s (k+2-d) (by omega)
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let hb:=(followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
    withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 0=
      followupCavityAlpha n β ρ*
        (cavityScalarRestModifiedSeven D B μ a p+cavitySignedResponseT D μ a B hb p):=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let p:=anisotropicSchemeNode s (k+2-d) (by omega)
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  have hb:B≠0:=(followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
  rw [native_cpp_firstJet_scheme_zero_eq_three_expectations hn β ρ hβ hρ s a ha has hq d hd,
    integral_cavityZeroLastResponseIntegrand s n β ρ hβ hρ a ha has hq p,
    integral_cavityZeroRestResponseIntegrand s n β ρ hβ hρ a ha has hq p,
    integral_cavityZeroDensityResponseIntegrand s n β ρ hβ hρ a ha has hq p]
  apply congrArg (fun x=>followupCavityAlpha n β ρ*x)
  have he:=cavityZeroResponse_evaluated_native_algebra D B hb μ a p
  dsimp only at he
  convert he using 1 <;> ring

theorem native_cpp_firstJet_scheme_zero_eq_linear_response
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2) :
    let μ:=Paper.parisiSchemeMeasure s
    let p:=anisotropicSchemeNode s (k+2-d) (by omega)
    withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 0=
      followupCavityLinearResponseRightSide n β ρ hβ hρ μ a p:=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let p:=anisotropicSchemeNode s (k+2-d) (by omega)
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
  rw [native_cpp_firstJet_scheme_zero_eq_seven_add_native_T hn β ρ hβ hρ s a ha has hq d hd,
    hnorm]
  unfold followupCavityLinearResponseRightSide
  dsimp only
  ring

end QuantitativeFollowup
