module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestIntegrand
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestProductMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeWeightedFubini
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedSampleIntegrability
public import QuantitativeFollowup.FollowupCavitySignedResponseNativeDefinitions

@[expose] public section

/-! Evaluation of the actual rest-observable part of the full zero-row
response. All six moments use the genuine marked product law and finite
free-measure Fubini. The future differential is the original native one. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem restEvaluation_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

private theorem scalar_mean_centered_sign_measurable (B : ℝ) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) :
    Measurable (fun z : Paper.BrownianSample×Bool=>scalarCenteredSquare B μ p z.1*
      M B μ p z.1*Paper.spinSign z.2):=
  (((((measurable_M B μ p p.property).pow_const 2).sub measurable_const).mul
    (measurable_M B μ p p.property)).comp measurable_fst).mul
      ((measurable_of_finite Paper.spinSign).comp measurable_snd)

private theorem scalar_mean_centered_sign_bound (B : ℝ) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) (z : Paper.BrownianSample×Bool) :
    ‖scalarCenteredSquare B μ p z.1*M B μ p z.1*Paper.spinSign z.2‖≤1:=by
  rw [norm_mul,Real.norm_eq_abs (Paper.spinSign _),Paper.abs_spinSign,mul_one,norm_mul]
  exact (mul_le_mul (scalarCenteredSquare_norm_le_one B μ p z.1)
    (scalar_M_norm_le_one B μ p z.1) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

private theorem scalar_kernel1_diagonal_eq_one (B : ℝ) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) : scalarResponseKernel1 B μ p 0 0=cavitySignedScalarKernelOne B μ p p:=by
  apply integral_congr_ae
  exact .of_forall fun z=>by ring

private theorem integral_rest_combination {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F0 F1 F2 F3 F4 F5 : Ω→ℝ) (c : ℝ)
    (h0 : Integrable F0 P) (h1 : Integrable F1 P) (h2 : Integrable F2 P)
    (h3 : Integrable F3 P) (h4 : Integrable F4 P) (h5 : Integrable F5 P) :
    (∫z,F0 z+4*F1 z-c*F2 z+2*F3 z-F4 z-2*F5 z ∂P)=
      (∫z,F0 z ∂P)+4*(∫z,F1 z ∂P)-c*(∫z,F2 z ∂P)+2*(∫z,F3 z ∂P)-
        (∫z,F4 z ∂P)-2*(∫z,F5 z ∂P):=by
  have hi01 : Integrable (fun z=>F0 z+4*F1 z) P:=h0.add (h1.const_mul 4)
  have hi012 : Integrable (fun z=>F0 z+4*F1 z-c*F2 z) P:=hi01.sub (h2.const_mul c)
  have hi0123 : Integrable (fun z=>F0 z+4*F1 z-c*F2 z+2*F3 z) P:=hi012.add (h3.const_mul 2)
  have hi01234 : Integrable (fun z=>F0 z+4*F1 z-c*F2 z+2*F3 z-F4 z) P:=hi0123.sub h4
  rw [integral_sub hi01234 (h5.const_mul 2),
    integral_sub hi0123 h4,
    integral_add hi012 (h3.const_mul 2),
    integral_sub hi01 (h2.const_mul c),integral_add h0 (h1.const_mul 4),
    integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul]

theorem cavityZeroRestResponseIntegrand_data
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    Integrable (fun z=>cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z)
      (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 restEvaluation_zero_mem) μ a) ∧
    (∫z,cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 restEvaluation_zero_mem) μ a)=
      cavitySignedResponseT3 D μ a B p:=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 restEvaluation_zero_mem) μ a
  let xr:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
    (cavityZeroMarkedSampleSplit n z).1
  let xs:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
    (cavityZeroMarkedSampleSplit n z).2
  let F0:=fun z=>cavityZeroRestHessianSquare D μ p (xr z).1*scalarResponseSample 5 B μ p p 0 (xs z)
  let F1:=fun z=>cavityZeroRestMixedHessian D μ p p (xr z).1*scalarResponseSample 1 B μ p 0 0 (xs z)
  let F2:=fun z=>cavityZeroRestMixedHessian D μ p p (xr z).1*scalarResponseSample 5 B μ p p 0 (xs z)
  let F3:=fun z=>cavityZeroRestTerminalHessian D μ p (xr z)*
    (scalarCenteredSquare B μ p (xs z).1*M B μ p (xs z).1*Paper.spinSign (xs z).2)
  let G4:=fun z r=>if p<r then cavityZeroRestFutureFieldDerivative D μ p r (xr z).1*
    (scalarCenteredSquare B μ p (xs z).1*scalarFutureSquareExtended B μ p r
      (parisiPhysicalSplitState B 0 μ p (xs z).1)) else 0
  let G5:=fun z r=>cavityZeroRestMixedHessian D μ r p (xr z).1*scalarResponseSample 6 B μ p p r (xs z)
  let F4:=fun z=>∫r,G4 z r ∂parisiFreeMeasure μ a
  let F5:=fun z=>∫r,G5 z r ∂parisiFreeMeasure μ a
  have hi0:Integrable F0 P:=integrable_cavityZeroMarked_scalarResponseSample_product μ n β ρ hβ hρ a
    (fun z=>cavityZeroRestHessianSquare D μ p z.1)
    ((measurable_cavityZeroRestHessianSquare D μ p).comp measurable_fst)
    (4*(n:ℝ)^2/|(n:ℝ)^2|) (by positivity) (fun z=>norm_cavityZeroRestHessianSquare_le D μ p z.1) 5 p p 0
  have hiM (j : Fin 8) (r l t : Paper.Overlap):Integrable (fun z=>
      cavityZeroRestMixedHessian D μ t p (xr z).1*scalarResponseSample j B μ p r l (xs z)) P:=
    integrable_cavityZeroMarked_scalarResponseSample_product μ n β ρ hβ hρ a
      (fun z=>cavityZeroRestMixedHessian D μ t p z.1)
      ((measurable_cavityZeroRestMixedHessian D μ t p).comp measurable_fst)
      ((n:ℝ)^2/|(n:ℝ)^2|) (by positivity) (fun z=>norm_cavityZeroRestMixedHessian_le D μ t p z.1) j p r l
  have hi1:Integrable F1 P:=hiM 1 0 0 p
  have hi2:Integrable F2 P:=hiM 5 p 0 p
  have hi3:Integrable F3 P:=integrable_cavityZeroMarked_bounded_product μ n β ρ hβ hρ a
    (cavityZeroRestTerminalHessian D μ p)
    (fun z=>scalarCenteredSquare B μ p z.1*M B μ p z.1*Paper.spinSign z.2)
    (measurable_cavityZeroRestTerminalHessian D μ p) (scalar_mean_centered_sign_measurable B μ p)
    ((∑i : Fin n,cavitySignedResponseHessianMeanCoordinateBound D i)/|(n:ℝ)^2|) 1
    (by unfold cavitySignedResponseHessianMeanCoordinateBound;positivity)
    (norm_cavityZeroRestTerminalHessian_le D μ p) (scalar_mean_centered_sign_bound B μ p)
  have hi4 (r : Paper.Overlap):Integrable (fun z=>G4 z r) P:=by
    dsimp only [G4]
    split_ifs with hr
    · exact integrable_cavityZeroMarked_bounded_product μ n β ρ hβ hρ a
        (fun z=>cavityZeroRestFutureFieldDerivative D μ p r z.1)
        (fun z=>scalarCenteredSquare B μ p z.1*scalarFutureSquareExtended B μ p r
          (parisiPhysicalSplitState B 0 μ p z.1))
        (((measurable_cavityNativeFutureGradientIntegrand D μ p r hr.le).div_const _).comp measurable_fst)
        (measurable_scalarCenteredSquare_future_extended B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ p r hr.le)
        (cavityNativeFutureGradientBound D/|(n:ℝ)|) 1
        (div_nonneg (cavityNativeFutureGradientBound_nonneg D) (abs_nonneg _))
        (fun z=>norm_cavityZeroRestFutureFieldDerivative_le D μ p r hr.le z.1)
        (norm_scalarCenteredSquare_future_extended_le B μ p r hr.le)
    · exact integrable_const 0
  have hiF4:Integrable F4 P:=integrable_cavityFiniteFree_section P s a ha has hq G4 hi4
  have hi5 (r : Paper.Overlap):Integrable (fun z=>G5 z r) P:=hiM 6 p r r
  have hiF5:Integrable F5 P:=integrable_cavityFiniteFree_section P s a ha has hq G5 hi5
  refine ⟨?_,?_⟩
  · change Integrable (fun z=>F0 z+4*F1 z-2*Paper.parisiCDF μ p*F2 z+2*F3 z-F4 z-2*F5 z) P
    exact ((((hi0.add (hi1.const_mul 4)).sub (hi2.const_mul (2*Paper.parisiCDF μ p))).add (hi3.const_mul 2)).sub hiF4).sub (hiF5.const_mul 2)
  · change (∫z,F0 z+4*F1 z-2*Paper.parisiCDF μ p*F2 z+2*F3 z-F4 z-2*F5 z ∂P)=_
    rw [integral_rest_combination P F0 F1 F2 F3 F4 F5 _ hi0 hi1 hi2 hi3 hiF4 hiF5]
    have h0:=cavityZeroMarked_hessian_trace_scalar_variance μ n β ρ hβ hρ a p
    have h1:=cavityZeroMarked_mixed_hessian_scalar_sample μ n β ρ hβ hρ a 1 p 0 0 p
    have h2:=cavityZeroMarked_mixed_hessian_scalar_sample μ n β ρ hβ hρ a 5 p p 0 p
    have h3:=cavityZeroMarked_terminal_hessian_scalar_variance μ n β ρ hβ hρ a p
    have h4:(∫z,F4 z ∂P)=∫r,cavitySignedScalarStrictFutureKernel B μ p r*
        cavitySignedResponseFutureGradient D μ a p r ∂parisiFreeMeasure μ a:=by
      rw [integral_cavityFiniteFree_swap P s a ha has hq G4 hi4]
      apply integral_congr_ae
      exact .of_forall fun r=>by
        dsimp only [G4]
        by_cases hr:p<r
        · simp only [if_pos hr]
          rw [cavityZeroMarked_future_gradient_scalar_covariance μ n β ρ hβ hρ a p r hr.le]
          simp only [cavitySignedScalarStrictFutureKernel,if_pos hr]
          ring
        · simp only [if_neg hr,integral_zero,cavitySignedScalarStrictFutureKernel,zero_mul]
    have h5:(∫z,F5 z ∂P)=∫r,cavitySignedScalarKernelTriple B μ (p,r) p*
        cavitySignedResponseMixedHessianMoment D μ a r p ∂parisiFreeMeasure μ a:=by
      rw [integral_cavityFiniteFree_swap P s a ha has hq G5 hi5]
      apply integral_congr_ae
      exact .of_forall fun r=>by
        dsimp only [G5,xr,xs]
        rw [cavityZeroMarked_mixed_hessian_scalar_sample μ n β ρ hβ hρ a 6 p p r r,
          scalarResponseCoefficient6_eq_cavitySignedScalarKernelTriple]
        ring
    rw [h0,h1,h2,h3,h4,h5]
    change cavitySignedResponseHessianTraceMoment D μ a p*cavitySignedScalarVariance B μ p+
      4*(cavitySignedResponseMixedHessianMoment D μ a p p*scalarResponseKernel1 B μ p 0 0)-
      2*Paper.parisiCDF μ p*(cavitySignedResponseMixedHessianMoment D μ a p p*scalarResponseKernel5 B μ p p 0)+
      2*(cavitySignedResponseMixedHessianMoment D μ a p p*cavitySignedScalarVariance B μ p)-
      (∫r,cavitySignedScalarStrictFutureKernel B μ p r*cavitySignedResponseFutureGradient D μ a p r ∂parisiFreeMeasure μ a)-
      2*(∫r,cavitySignedScalarKernelTriple B μ (p,r) p*cavitySignedResponseMixedHessianMoment D μ a r p
        ∂parisiFreeMeasure μ a)=_
    rw [scalar_kernel1_diagonal_eq_one,scalarResponseKernel5_diagonal_eq_cavitySignedScalarVariance]
    unfold cavitySignedResponseT3 cavitySignedResponseT3Diagonal cavitySignedScalarDiagonalCoefficient
      cavitySignedResponseT3LastHessian
    ring

theorem integral_cavityZeroRestResponseIntegrand
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 restEvaluation_zero_mem) μ a)=
      cavitySignedResponseT3 D μ a B p:=by
  dsimp only
  exact (cavityZeroRestResponseIntegrand_data s n β ρ hβ hρ a ha has hq p).2

end QuantitativeFollowup
