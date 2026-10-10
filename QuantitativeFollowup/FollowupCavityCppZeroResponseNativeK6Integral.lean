module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseContractedMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedSampleIntegrability
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeWeightedFubini
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeLinearity

@[expose] public section

/-! The literal two-time density term under the actual independent marked
law splits into its scalar K6 covariance-column term and the original
signed residual. Both free-measure integrations retain their root charges. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem kernel6_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem integral_cavityZeroMarked_double_free_kernel6
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,∫r,∫l,cavityRestTwoTimeMeanPairing D μ r l
      (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 6 B μ p r l (cavityZeroMarkedSampleSplit n z).2
      ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 kernel6_zero_mem) μ a)=
      (∫r,∫l,cavityRestCovarianceColumn D μ a p (min r l)*
        scalarResponseKernel6 B μ p r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
      ∫r,∫l,cavitySignedScalarKernelTriple B μ (r,l) p*
        (∫z,cavitySignedResponseSymmetricMeanResidual D μ r l z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z
          ∂anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a :=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 kernel6_zero_mem) μ a
  let F:=fun (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))
      (r l : Paper.Overlap)=>cavityRestTwoTimeMeanPairing D μ r l
    (cavityZeroMarkedSampleSplit n z).1.1*
    cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
    scalarResponseSample 6 B μ p r l (cavityZeroMarkedSampleSplit n z).2
  have hi (r l : Paper.Overlap) : Integrable (fun z=>F z r l) P :=by
    have hcenter : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
      (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
        ((anisotropicBrownianFiltration n).le _) le_rfl
    exact integrable_cavityZeroMarked_scalarResponseSample_product μ n β ρ hβ hρ a
      (fun z=>cavityRestTwoTimeMeanPairing D μ r l z.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
      (((measurable_cavityRestTwoTimeMeanPairing D μ r l).mul hcenter).comp measurable_fst)
      6 (by norm_num) (fun z=>by
        rw [norm_mul]
        exact (mul_le_mul (norm_cavityRestTwoTimeMeanPairing_le_three D μ r l z.1)
          (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1)
          (norm_nonneg _) (by norm_num : 0≤(3:ℝ))).trans_eq (by norm_num)) 6 p r l
  change (∫z,∫r,∫l,F z r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a ∂P)=_
  rw [integral_cavityFiniteFree_double_swap P s a ha has hq F hi]
  calc
    _ = ∫r,∫l,cavityRestCovarianceColumn D μ a p (min r l)*scalarResponseKernel6 B μ p r l+
        cavitySignedScalarKernelTriple B μ (r,l) p*
          (∫z,cavitySignedResponseSymmetricMeanResidual D μ r l z*
            cavitySignedResponseCenteredSelfOverlap D μ a p z
            ∂anisotropicMeasureSampleLaw D μ a)
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a :=by
      apply integral_congr_ae
      exact .of_forall fun r=>by
        apply integral_congr_ae
        exact .of_forall fun l=>cavityZeroMarked_kernel6_two_time_centered μ n β ρ hβ hρ a p r l
    _ = _ :=by
      let U:=fun r l=>cavityRestCovarianceColumn D μ a p (min r l)*scalarResponseKernel6 B μ p r l
      let V:=fun r l=>cavitySignedScalarKernelTriple B μ (r,l) p*
        (∫z,cavitySignedResponseSymmetricMeanResidual D μ r l z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a)
      change (∫r,∫l,U r l+V r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)=
        (∫r,∫l,U r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
          ∫r,∫l,V r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a
      calc
        _ = ∫r,(∫l,U r l ∂parisiFreeMeasure μ a)+
            (∫l,V r l ∂parisiFreeMeasure μ a) ∂parisiFreeMeasure μ a :=by
          apply integral_congr_ae
          exact .of_forall fun r=>integral_cavityFiniteFree_add s a ha has hq (U r) (V r)
        _ = _ :=integral_cavityFiniteFree_add s a ha has hq _ _

end QuantitativeFollowup
