module
public import HexagonPaper.CavityFixedRowExpansionMarkedFubini
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFutureKernel2Expectation

@[expose] public section

/-! Strict-future K2 contraction under the actual complete marked zero-row
law for every probability profile, with the starting atom excluded and
all future atoms retained. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {n : ℕ}

theorem cavityFixedRowMarked_strict_future_kernel2_data_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let R:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
      ∫r,if p<r then cavityRestFutureSquare D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 2 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2 else 0 ∂parisiFreeMeasure μ a
    Integrable R P ∧ (∫z,R z ∂P)=∫r,if p<r then
      cavityRestCovarianceColumn D μ a p r*scalarResponseKernel2 B μ p r 0 else 0 ∂parisiFreeMeasure μ a := by
  classical
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let F:=fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    if p<z.1 then cavityRestFutureSquare D μ p z.1 z.2.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1 else 0
  have hfuture : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavityRestFutureSquare D μ p z.1 z.2.1) := by
    simpa only [Function.comp_def] using (measurable_cavityRestFutureSquare D μ).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd.fst))
  have hcenter : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1) := by
    simpa only [Function.comp_def,Function.uncurry_def] using
      (measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp
        (measurable_const.prodMk measurable_snd.fst)
  have hm : Measurable F := by
    change Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      if p<z.1 then cavityRestFutureSquare D μ p z.1 z.2.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1 else 0)
    apply Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    · simpa only [Pi.mul_def] using hfuture.mul hcenter
    · exact measurable_const
  have hb (z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)) : ‖F z‖≤2 := by
    dsimp only [F]
    split_ifs
    · rw [norm_mul,Real.norm_of_nonneg (cavityRestFutureSquare_mem_unit D μ p z.1 z.2.1).1]
      exact (mul_le_mul (cavityRestFutureSquare_mem_unit D μ p z.1 z.2.1).2
        (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.2.1)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 2)
    · norm_num
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (parisiFreeMeasure μ a)
    (fun _=>p) id (fun _=>0) measurable_const measurable_id measurable_const F hm 2 (by norm_num) hb 2
  simp only [id_eq] at hi
  have hi' : Integrable (Function.uncurry (fun r z=>F (r,(cavityZeroMarkedSampleSplit n z).1)*
      scalarResponseSample 2 (followupCavityScalarBeta n β ρ) μ p r 0 (cavityZeroMarkedSampleSplit n z).2))
      ((parisiFreeMeasure μ a).prod (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)) := by
    simpa only [Function.uncurry_def] using hi
  have he (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) (r : Paper.Overlap) :
      F (r,(cavityZeroMarkedSampleSplit n z).1)*scalarResponseSample 2 (followupCavityScalarBeta n β ρ) μ p r 0
        (cavityZeroMarkedSampleSplit n z).2 =
      if p<r then cavityRestFutureSquare D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 2 (followupCavityScalarBeta n β ρ) μ p r 0 (cavityZeroMarkedSampleSplit n z).2 else 0 := by
    dsimp only [F]
    split_ifs <;> simp only [zero_mul]
  refine ⟨?_,?_⟩
  · have hh:=hi.integral_prod_right
    simpa only [he,D] using hh
  · have hs:= (integral_integral_swap hi').symm
    simp_rw [he] at hs
    rw [hs]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      by_cases hr:p<r
      · simp only [if_pos hr]
        exact cavityZeroMarked_future_scalarSample2_centered μ n β ρ hβ hρ a p r hr.le
      · simp only [if_neg hr,integral_zero]

end HexagonPaper
