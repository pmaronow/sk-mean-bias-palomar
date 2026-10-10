module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFutureKernel2Expectation
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedSampleIntegrability
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeFubini

@[expose] public section

/-! The genuine strict-future last-field contribution contracts to the
literal scalar K2 kernel times the actual rest covariance column. Fubini
uses the exact finite free-measure charges, with no atom dropped. -/
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

private theorem nativeK2_rest_test_measurable {n : ℕ}
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p r : Paper.Overlap) :
    Measurable (fun sample : AnisotropicDisorderBrownianSample n=>
      cavityRestFutureSquare D μ p r sample*cavitySignedResponseCenteredSelfOverlap D μ a p sample):=by
  have hm:Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(p,(r,sample))):=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hfuture:=(measurable_cavityRestFutureSquare D μ).comp hm
  have hcenter:Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p):=
    (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
      ((anisotropicBrownianFiltration n).le _) le_rfl
  exact hfuture.mul hcenter

private theorem nativeK2_rest_test_bound {n : ℕ}
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p r : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖cavityRestFutureSquare D μ p r sample*cavitySignedResponseCenteredSelfOverlap D μ a p sample‖≤2:=by
  rw [norm_mul,Real.norm_of_nonneg (cavityRestFutureSquare_mem_unit D μ p r sample).1]
  exact (mul_le_mul (cavityRestFutureSquare_mem_unit D μ p r sample).2
    (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p sample)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 2)

theorem integral_cavityZeroMarked_strict_future_kernel2
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,∫r,if p<r then
      cavityRestFutureSquare D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 2 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2 else 0
      ∂parisiFreeMeasure μ a
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      ∫r,if p<r then cavityRestCovarianceColumn D μ a p r*
        scalarResponseKernel2 B μ p r 0 else 0 ∂parisiFreeMeasure μ a :=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
  let F:=fun z r=>if p<r then
    cavityRestFutureSquare D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
    cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
    scalarResponseSample 2 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2 else 0
  have hi (r : Paper.Overlap) : Integrable (fun z=>F z r) P :=by
    dsimp only [F]
    split_ifs
    · exact integrable_cavityZeroMarked_scalarResponseSample_product μ n β ρ hβ hρ a
        (fun z=>cavityRestFutureSquare D μ p r z.1*
          cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
        ((nativeK2_rest_test_measurable D μ a p r).comp measurable_fst) 2 (by norm_num)
        (fun z=>nativeK2_rest_test_bound D μ a p r z.1) 2 p r 0
    · exact integrable_const 0
  change (∫z,∫r,F z r ∂parisiFreeMeasure μ a ∂P)=_
  rw [integral_cavityFiniteFree_swap P s a ha has hq F hi]
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only [F]
    by_cases hpr:p<r
    · simp only [if_pos hpr]
      exact cavityZeroMarked_future_scalarSample2_centered μ n β ρ hβ hρ a p r hpr.le
    · simp only [if_neg hpr,integral_zero]

end QuantitativeFollowup
