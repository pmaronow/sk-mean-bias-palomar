module
public import HexagonPaper.CavityFixedRowExpansionDensityPairs
public import HexagonPaper.CavityFixedRowExpansionDensitySimple
public import QuantitativeFollowup.FollowupCavityCppZeroResponseDensityEvaluation

@[expose] public section

/-! Literal density response (270), evaluated under the genuine native marked
law for every Parisi profile. All section and product integrability is proved. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup FRSB
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem integral_density_combination {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F0 F1 F2 F3 F4 : Ω→ℝ) (c : ℝ)
    (h0 : Integrable F0 P) (h1 : Integrable F1 P) (h2 : Integrable F2 P)
    (h3 : Integrable F3 P) (h4 : Integrable F4 P) :
    (∫z,c*F0 z-F1 z+(1/2:ℝ)*F2 z+(1/2:ℝ)*F3 z+(1/2:ℝ)*F4 z ∂P)=
      c*(∫z,F0 z ∂P)-(∫z,F1 z ∂P)+(1/2:ℝ)*(∫z,F2 z ∂P)+
        (1/2:ℝ)*(∫z,F3 z ∂P)+(1/2:ℝ)*(∫z,F4 z ∂P) :=by
  have h01 : Integrable (fun z=>c*F0 z-F1 z) P := (h0.const_mul c).sub h1
  have h012 : Integrable (fun z=>c*F0 z-F1 z+(1/2:ℝ)*F2 z) P :=
    h01.add (h2.const_mul (1/2))
  have h0123 : Integrable (fun z=>c*F0 z-F1 z+(1/2:ℝ)*F2 z+(1/2:ℝ)*F3 z) P :=
    h012.add (h3.const_mul (1/2))
  rw [integral_add h0123 (h4.const_mul (1/2)),
    integral_add h012 (h3.const_mul (1/2)),
    integral_add h01 (h2.const_mul (1/2)),
    integral_sub (h0.const_mul c) h1,
    integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul]

theorem cavityFixedRowDensityResponseIntegrand_data_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    Integrable (fun z=>cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z)
      (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) ∧
    (∫z,cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      -(∫r,cavityRestCovarianceColumn D μ a p r*scalarResponseKernel4 B μ p r 0
        ∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,∫l,cavityRestCovarianceColumn D μ a p (min r l)*scalarResponseKernel6 B μ p r l
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,Paper.parisiCDF μ r*(cavityRestCovarianceColumn D μ a p r*
        scalarResponseKernel5 B μ p r r) ∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*cavityScalarRestThetaLast D B μ a p+
      cavitySignedResponseT2 D μ a B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p :=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
  let xr:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
    (cavityZeroMarkedSampleSplit n z).1
  let xs:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
    (cavityZeroMarkedSampleSplit n z).2
  let A:=fun z=>cavitySignedResponseCenteredSelfOverlap D μ a p (xr z).1
  let F0:=fun z=>A z*scalarCenteredSquare B μ p (xs z).1
  let F1:=fun z=>∫r,cavityRestTerminalMeanPairing D μ r (xr z)*A z*
    scalarResponseSample 4 B μ p r 0 (xs z) ∂parisiFreeMeasure μ a
  let F2:=fun z=>∫r,∫l,cavityRestTwoTimeMeanPairing D μ r l (xr z).1*A z*
    scalarResponseSample 6 B μ p r l (xs z) ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a
  let F3:=fun z=>∫r,Paper.parisiCDF μ r*(cavitySignedResponseSelfOverlap D μ r (xr z).1*A z*
    scalarResponseSample 5 B μ p r r (xs z)) ∂parisiFreeMeasure μ a
  let F4:=fun z=>∫r,∫l,if r<l then cavityRestFutureSquare D μ r l (xr z).1*A z*
    scalarResponseSample 7 B μ p r l (xs z) else 0 ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a
  have hi0 : Integrable F0 P:=by
    have hG : Measurable (fun z : Paper.BrownianSample×Bool=>scalarCenteredSquare B μ p z.1):=
      (((measurable_M B μ p p.property).pow_const 2).sub measurable_const).comp measurable_fst
    have h:=integrable_cavityZeroMarked_rest_centered_product μ n β ρ hβ hρ a p
      (fun _=>1) (fun z=>scalarCenteredSquare B μ p z.1) measurable_const hG
      1 1 zero_le_one (fun _=>by norm_num) (fun z=>scalarCenteredSquare_norm_le_one B μ p z.1)
    simpa only [one_mul] using h
  have h1:=cavityFixedRowMarked_kernel4_data_all_profiles μ n β ρ hβ hρ a p
  have h2:=cavityFixedRowMarked_kernel6_data_all_profiles μ n β ρ hβ hρ a p
  have h3:=cavityFixedRowMarked_cdf_kernel5_data_all_profiles μ n β ρ hβ hρ a p
  have h4:=cavityFixedRowMarked_strict_future_kernel7_data_all_profiles μ n β ρ hβ hρ a p
  have hi1 : Integrable F1 P:=h1.1
  have hi2 : Integrable F2 P:=h2.1
  have hi3 : Integrable F3 P:=h3.1
  have hi4 : Integrable F4 P:=h4.1
  refine ⟨?_,?_⟩
  · change Integrable (fun z=>((1-(∫r,(1:ℝ) ∂parisiFreeMeasure μ a))/2)*F0 z-F1 z+(1/2:ℝ)*F2 z+(1/2:ℝ)*F3 z+(1/2:ℝ)*F4 z) P
    exact ((((hi0.const_mul ((1-(∫r,(1:ℝ) ∂parisiFreeMeasure μ a))/2)).sub hi1).add (hi2.const_mul (1/2))).add (hi3.const_mul (1/2))).add (hi4.const_mul (1/2))
  · change (∫z,((1-(∫r,(1:ℝ) ∂parisiFreeMeasure μ a))/2)*F0 z-F1 z+
      (1/2:ℝ)*F2 z+(1/2:ℝ)*F3 z+(1/2:ℝ)*F4 z ∂P)=_
    rw [integral_density_combination P F0 F1 F2 F3 F4 _ hi0 hi1 hi2 hi3 hi4]
    have h0 : (∫z,F0 z ∂P)=0:=integral_cavityZeroMarked_centered_self_scalar_zero μ n β ρ hβ hρ a p
    rw [h0,h1.2,h2.2,h3.2,h4.2]
    rw [cavitySignedResponseT2,cavitySignedResponseT2First,
      cavitySignedResponseT2Double_eq_iterated D μ a B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p]
    ring


end HexagonPaper
