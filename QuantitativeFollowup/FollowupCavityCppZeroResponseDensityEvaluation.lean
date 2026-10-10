module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeK34Integrals
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeK5Integral
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeK6Integral
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeK7Integral
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedCenteredIntegrability
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedCenteredZero
public import QuantitativeFollowup.FollowupCavityCppZeroResponseT2DoubleIterated
public import QuantitativeFollowup.FollowupCavitySignedResponseNativeDefinitions

@[expose] public section

/-! The density part of the complete zero-row response is evaluated under
the genuine marked product law. The constant vanishes by independence;
the terminal and two-time residuals give the literal original T2. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem densityEvaluation_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

def cavityZeroDensityResponseIntegrand (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) : ℝ :=
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let xr:=(cavityZeroMarkedSampleSplit n z).1
  let xs:=(cavityZeroMarkedSampleSplit n z).2
  let A:=cavitySignedResponseCenteredSelfOverlap D μ a p xr.1
  ((1-(∫r,(1:ℝ) ∂parisiFreeMeasure μ a))/2)*
      (A*scalarCenteredSquare B μ p xs.1)-
    (∫r,cavityRestTerminalMeanPairing D μ r xr*A*scalarResponseSample 4 B μ p r 0 xs
      ∂parisiFreeMeasure μ a)+
    (1/2:ℝ)*(∫r,∫l,cavityRestTwoTimeMeanPairing D μ r l xr.1*A*
      scalarResponseSample 6 B μ p r l xs ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
    (1/2:ℝ)*(∫r,Paper.parisiCDF μ r*(cavitySignedResponseSelfOverlap D μ r xr.1*A*
      scalarResponseSample 5 B μ p r r xs) ∂parisiFreeMeasure μ a)+
    (1/2:ℝ)*(∫r,∫l,if r<l then cavityRestFutureSquare D μ r l xr.1*A*
      scalarResponseSample 7 B μ p r l xs else 0
      ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)

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

theorem cavityZeroDensityResponseIntegrand_data
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    Integrable (fun z=>cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z)
      (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 densityEvaluation_zero_mem) μ a) ∧
    (∫z,cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 densityEvaluation_zero_mem) μ a)=
      -(∫r,cavityRestCovarianceColumn D μ a p r*scalarResponseKernel4 B μ p r 0
        ∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,∫l,cavityRestCovarianceColumn D μ a p (min r l)*scalarResponseKernel6 B μ p r l
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,Paper.parisiCDF μ r*(cavityRestCovarianceColumn D μ a p r*
        scalarResponseKernel5 B μ p r r) ∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*cavityScalarRestThetaLast D B μ a p+
      cavitySignedResponseT2 D μ a B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p :=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 densityEvaluation_zero_mem) μ a
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
  have hi1 : Integrable F1 P:=by
    apply integrable_cavityFiniteFree_section P s a ha has hq
    intro r
    exact integrable_cavityZeroMarked_rest_centered_sample μ n β ρ hβ hρ a p
      (cavityRestTerminalMeanPairing D μ r) (measurable_cavityRestTerminalMeanPairing D μ r)
      3 (by norm_num) (norm_cavityRestTerminalMeanPairing_le_three D μ r) 4 r 0
  have hi2 : Integrable F2 P:=by
    apply integrable_cavityFiniteFree_section P s a ha has hq
    intro r
    apply integrable_cavityFiniteFree_section P s a ha has hq
    intro l
    exact integrable_cavityZeroMarked_rest_centered_sample μ n β ρ hβ hρ a p
      (fun z=>cavityRestTwoTimeMeanPairing D μ r l z.1)
      ((measurable_cavityRestTwoTimeMeanPairing D μ r l).comp measurable_fst)
      3 (by norm_num) (fun z=>norm_cavityRestTwoTimeMeanPairing_le_three D μ r l z.1) 6 r l
  have hi3 : Integrable F3 P:=by
    apply integrable_cavityFiniteFree_section P s a ha has hq
    intro r
    have hm : Measurable (fun z : AnisotropicDisorderBrownianSample n=>(r,z)):=
      measurable_const.prodMk measurable_id
    have hself : Measurable (cavitySignedResponseSelfOverlap D μ r):=by
      simpa only [Function.comp_def,Function.uncurry_def] using
        (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hm
    exact (integrable_cavityZeroMarked_rest_centered_sample μ n β ρ hβ hρ a p
      (fun z=>cavitySignedResponseSelfOverlap D μ r z.1) (hself.comp measurable_fst)
      1 zero_le_one (fun z=>norm_cavitySignedResponseSelfOverlap_le D μ r z.1) 5 r r).const_mul _
  have hi4 : Integrable F4 P:=by
    apply integrable_cavityFiniteFree_section P s a ha has hq
    intro r
    apply integrable_cavityFiniteFree_section P s a ha has hq
    intro l
    split_ifs
    · have hm : Measurable (fun z : AnisotropicDisorderBrownianSample n=>(r,(l,z))):=
        measurable_const.prodMk (measurable_const.prodMk measurable_id)
      exact integrable_cavityZeroMarked_rest_centered_sample μ n β ρ hβ hρ a p
        (fun z=>cavityRestFutureSquare D μ r l z.1)
        (((measurable_cavityRestFutureSquare D μ).comp hm).comp measurable_fst)
        1 zero_le_one (fun z=>by
          rw [Real.norm_of_nonneg (cavityRestFutureSquare_mem_unit D μ r l z.1).1]
          exact (cavityRestFutureSquare_mem_unit D μ r l z.1).2) 7 r l
    · exact integrable_const 0
  refine ⟨?_,?_⟩
  · change Integrable (fun z=>((1-(∫r,(1:ℝ) ∂parisiFreeMeasure μ a))/2)*F0 z-F1 z+(1/2:ℝ)*F2 z+(1/2:ℝ)*F3 z+(1/2:ℝ)*F4 z) P
    exact ((((hi0.const_mul ((1-(∫r,(1:ℝ) ∂parisiFreeMeasure μ a))/2)).sub hi1).add (hi2.const_mul (1/2))).add (hi3.const_mul (1/2))).add (hi4.const_mul (1/2))
  · change (∫z,((1-(∫r,(1:ℝ) ∂parisiFreeMeasure μ a))/2)*F0 z-F1 z+
      (1/2:ℝ)*F2 z+(1/2:ℝ)*F3 z+(1/2:ℝ)*F4 z ∂P)=_
    rw [integral_density_combination P F0 F1 F2 F3 F4 _ hi0 hi1 hi2 hi3 hi4]
    have h0 : (∫z,F0 z ∂P)=0:=integral_cavityZeroMarked_centered_self_scalar_zero μ n β ρ hβ hρ a p
    have h1:=integral_cavityZeroMarked_free_kernel4 s n β ρ hβ hρ a ha has hq p
    have h2:=integral_cavityZeroMarked_double_free_kernel6 s n β ρ hβ hρ a ha has hq p
    have h3:=integral_cavityZeroMarked_cdf_free_kernel5 s n β ρ hβ hρ a ha has hq p
    have h4:=integral_cavityZeroMarked_double_strict_future_kernel7 s n β ρ hβ hρ a ha has hq p
    rw [h0,h1,h2,h3,h4]
    rw [cavitySignedResponseT2,cavitySignedResponseT2First,
      cavitySignedResponseT2Double_eq_iterated D μ a B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p]
    ring

theorem integral_cavityZeroDensityResponseIntegrand
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 densityEvaluation_zero_mem) μ a)=
      -(∫r,cavityRestCovarianceColumn D μ a p r*scalarResponseKernel4 B μ p r 0
        ∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,∫l,cavityRestCovarianceColumn D μ a p (min r l)*scalarResponseKernel6 B μ p r l
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*(∫r,Paper.parisiCDF μ r*(cavityRestCovarianceColumn D μ a p r*
        scalarResponseKernel5 B μ p r r) ∂parisiFreeMeasure μ a)+
      (1/2:ℝ)*cavityScalarRestThetaLast D B μ a p+
      cavitySignedResponseT2 D μ a B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p :=by
  dsimp only
  exact (cavityZeroDensityResponseIntegrand_data s n β ρ hβ hρ a ha has hq p).2

end QuantitativeFollowup
