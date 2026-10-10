module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseSeparatedMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedSampleIntegrability
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeFubini

@[expose] public section

/-! The actual right-CDF weighted current density term contracts to the
literal scalar K5 kernel and the rest covariance column. The current atom
and the finite outer root charge remain in the genuine free measure. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem integral_cavityZeroMarked_cdf_free_kernel5
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,∫r,Paper.parisiCDF μ r*(cavitySignedResponseSelfOverlap D μ r
      (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 5 B μ p r r (cavityZeroMarkedSampleSplit n z).2)
      ∂parisiFreeMeasure μ a
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      ∫r,Paper.parisiCDF μ r*(cavityRestCovarianceColumn D μ a p r*
        scalarResponseKernel5 B μ p r r) ∂parisiFreeMeasure μ a :=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
  let F:=fun (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))
      (r : Paper.Overlap)=>Paper.parisiCDF μ r*(cavitySignedResponseSelfOverlap D μ r
    (cavityZeroMarkedSampleSplit n z).1.1*
    cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
    scalarResponseSample 5 B μ p r r (cavityZeroMarkedSampleSplit n z).2)
  have hi (r : Paper.Overlap) : Integrable (fun z=>F z r) P :=by
    have hcenter : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
      (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
        ((anisotropicBrownianFiltration n).le _) le_rfl
    have hm : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(r,sample)) :=
      measurable_const.prodMk measurable_id
    have hself : Measurable (cavitySignedResponseSelfOverlap D μ r) :=by
      simpa only [Function.comp_def,Function.uncurry_def] using
        (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hm
    exact (integrable_cavityZeroMarked_scalarResponseSample_product μ n β ρ hβ hρ a
      (fun z=>cavitySignedResponseSelfOverlap D μ r z.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
      ((hself.mul hcenter).comp measurable_fst)
      2 (by norm_num) (fun z=>by
        rw [norm_mul]
        exact (mul_le_mul (norm_cavitySignedResponseSelfOverlap_le D μ r z.1)
          (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1)
          (norm_nonneg _) zero_le_one).trans_eq (by norm_num)) 5 p r r).const_mul _
  change (∫z,∫r,F z r ∂parisiFreeMeasure μ a ∂P)=_
  rw [integral_cavityFiniteFree_swap P s a ha has hq F hi]
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only [F]
    rw [integral_const_mul,cavityZeroMarked_scalarSample_self_centered μ n β ρ hβ hρ a 5 p r r]
    rfl

end QuantitativeFollowup
