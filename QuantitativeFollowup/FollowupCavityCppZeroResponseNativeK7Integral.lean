module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProjectedMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedSampleIntegrability
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeWeightedFubini

@[expose] public section

/-! The actual strict-future density term contracts to the original
conditional Theta term. Its expectation retains the whole marked product
law, and the strict mask is converted to the genuine restricted measure. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem integral_cavityZeroMarked_double_strict_future_kernel7
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,∫r,∫l,if r<l then
      (cavityRestFutureSquare D μ r l (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1)*
      scalarResponseSample 7 B μ p r l (cavityZeroMarkedSampleSplit n z).2 else 0
      ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      cavityScalarRestThetaLast D B μ a p :=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
  let F:=fun (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))
      (r l : Paper.Overlap)=>if r<l then
    (cavityRestFutureSquare D μ r l (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1)*
    scalarResponseSample 7 B μ p r l (cavityZeroMarkedSampleSplit n z).2 else 0
  have hi (r l : Paper.Overlap) : Integrable (fun z=>F z r l) P :=by
    dsimp only [F]
    split_ifs
    · have hm : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(r,(l,sample))) :=
        measurable_const.prodMk (measurable_const.prodMk measurable_id)
      have hfuture := (measurable_cavityRestFutureSquare D μ).comp hm
      have hcenter : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
        (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
          ((anisotropicBrownianFiltration n).le _) le_rfl
      exact integrable_cavityZeroMarked_scalarResponseSample_product μ n β ρ hβ hρ a
        (fun z=>cavityRestFutureSquare D μ r l z.1*
          cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
        ((hfuture.mul hcenter).comp measurable_fst) 2 (by norm_num)
        (fun z=>by
          rw [norm_mul,Real.norm_of_nonneg (cavityRestFutureSquare_mem_unit D μ r l z.1).1]
          exact (mul_le_mul (cavityRestFutureSquare_mem_unit D μ r l z.1).2
            (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1)
            (norm_nonneg _) zero_le_one).trans_eq (one_mul 2)) 7 p r l
    · exact integrable_const 0
  change (∫z,∫r,∫l,F z r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a ∂P)=_
  rw [integral_cavityFiniteFree_double_swap P s a ha has hq F hi]
  change (∫r,∫l,∫z,F z r l ∂P ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)=_
  unfold cavityScalarRestThetaLast
  apply integral_congr_ae
  exact .of_forall fun r=>by
    change (∫l,∫z,F z r l ∂P ∂parisiFreeMeasure μ a) =
      ∫l in Ioi r,scalarFutureCenteredPairing B μ p r l *
        cavityRestProjectedCovariance D μ a r l p ∂parisiFreeMeasure μ a
    rw [←integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact .of_forall fun l=>by
      dsimp only [F]
      by_cases hrl:r<l
      · simp only [if_pos hrl,Set.indicator_of_mem (show l∈Ioi r from hrl)]
        exact cavityZeroMarked_future_scalarSample7_centered μ n β ρ hβ hρ a p r l hrl.le
      · simp only [if_neg hrl,integral_zero,
          Set.indicator_of_notMem (show l∉Ioi r from hrl)]

end QuantitativeFollowup
