module
public import HexagonPaper.CavityFixedRowExpansionDoubleFamilySections
public import HexagonPaper.CavityFixedRowExpansionRestFamilies
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProjectedMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseSeparatedMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseKernelContraction

@[expose] public section

/-! The actual right-CDF current K5 and strict double-future K7 density
contributions, with honest integrability and no finite-profile restriction. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cavityFixedRowMarked_cdf_kernel5_data_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let R:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
      ∫r,Paper.parisiCDF μ r*(cavitySignedResponseSelfOverlap D μ r (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 5 B μ p r r (cavityZeroMarkedSampleSplit n z).2) ∂parisiFreeMeasure μ a
    Integrable R P ∧ (∫z,R z ∂P)=∫r,Paper.parisiCDF μ r*
      (cavityRestCovarianceColumn D μ a p r*scalarResponseKernel5 B μ p r r) ∂parisiFreeMeasure μ a := by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let F:=fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    Paper.parisiCDF μ z.1*(cavitySignedResponseSelfOverlap D μ z.1 z.2.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1)
  have hS : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavitySignedResponseSelfOverlap D μ z.1 z.2.1) := by
    simpa only [Function.comp_def,Function.uncurry_def] using (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp
      (measurable_fst.prodMk measurable_snd.fst)
  have hA : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1) := by
    simpa only [Function.comp_def,Function.uncurry_def] using (measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp
      (measurable_const.prodMk measurable_snd.fst)
  have hm : Measurable F := by
    simpa only [F,Function.comp_def,Pi.mul_def] using
      ((Paper.parisiCDF_measurable μ).comp (measurable_subtype_coe.comp measurable_fst)).mul (hS.mul hA)
  have hb (z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)) : ‖F z‖≤2 := by
    dsimp only [F]
    rw [norm_mul,Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ z.1),norm_mul]
    exact (mul_le_mul (Paper.parisiCDF_le_one μ z.1)
      (mul_le_mul (norm_cavitySignedResponseSelfOverlap_le D μ z.1 z.2.1)
        (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.2.1) (norm_nonneg _) zero_le_one)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (by norm_num)
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (parisiFreeMeasure μ a)
    (fun _=>p) id id measurable_const measurable_id measurable_id F hm 2 (by norm_num) hb 5
  simp only [id_eq] at hi
  have he (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) (r : Paper.Overlap) :
      F (r,(cavityZeroMarkedSampleSplit n z).1)*scalarResponseSample 5 (followupCavityScalarBeta n β ρ) μ p r r
        (cavityZeroMarkedSampleSplit n z).2 =
      Paper.parisiCDF μ r*(cavitySignedResponseSelfOverlap D μ r (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 5 (followupCavityScalarBeta n β ρ) μ p r r (cavityZeroMarkedSampleSplit n z).2) := by
    dsimp only [F]
    ring
  refine ⟨?_,?_⟩
  · simpa only [he] using hi.integral_prod_right
  · have hi' : Integrable (Function.uncurry (fun r z=>F (r,(cavityZeroMarkedSampleSplit n z).1)*
        scalarResponseSample 5 (followupCavityScalarBeta n β ρ) μ p r r (cavityZeroMarkedSampleSplit n z).2))
        ((parisiFreeMeasure μ a).prod (anisotropicMeasureSpinPathLaw
          (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)) := by
      simpa only [Function.uncurry_def] using hi
    have hs:= (integral_integral_swap hi').symm
    simp_rw [he] at hs
    rw [hs]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      change (∫z,Paper.parisiCDF μ r*(cavitySignedResponseSelfOverlap D μ r (cavityZeroMarkedSampleSplit n z).1.1*
          cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
          scalarResponseSample 5 (followupCavityScalarBeta n β ρ) μ p r r (cavityZeroMarkedSampleSplit n z).2)
          ∂anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
        Paper.parisiCDF μ r*(cavityRestCovarianceColumn D μ a p r*scalarResponseKernel5 (followupCavityScalarBeta n β ρ) μ p r r)
      rw [integral_const_mul,cavityZeroMarked_scalarSample_self_centered μ n β ρ hβ hρ a 5 p r r]
      rfl

theorem cavityFixedRowMarked_strict_future_kernel7_data_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let R:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
      ∫r,∫l,if r<l then cavityRestFutureSquare D μ r l (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 7 B μ p r l (cavityZeroMarkedSampleSplit n z).2 else 0
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a
    Integrable R P ∧ (∫z,R z ∂P)=cavityScalarRestThetaLast D B μ a p := by
  classical
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let F:=fun z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    if z.1.1<z.1.2 then cavityRestFutureSquare D μ z.1.1 z.1.2 z.2.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1 else 0
  have hfuture : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavityRestFutureSquare D μ z.1.1 z.1.2 z.2.1) := by
    simpa only [Function.comp_def] using (measurable_cavityRestFutureSquare D μ).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd.fst))
  have hA : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1) := by
    simpa only [Function.comp_def,Function.uncurry_def] using (measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp
      (measurable_const.prodMk measurable_snd.fst)
  have hm : Measurable F := by
    change Measurable (fun z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      if z.1.1<z.1.2 then cavityRestFutureSquare D μ z.1.1 z.1.2 z.2.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1 else 0)
    apply Measurable.ite (measurableSet_lt measurable_fst.fst measurable_fst.snd)
    · simpa only [Pi.mul_def] using hfuture.mul hA
    · exact measurable_const
  have hb (z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)) : ‖F z‖≤2 := by
    dsimp only [F]
    split_ifs
    · rw [norm_mul,Real.norm_of_nonneg (cavityRestFutureSquare_mem_unit D μ z.1.1 z.1.2 z.2.1).1]
      exact (mul_le_mul (cavityRestFutureSquare_mem_unit D μ z.1.1 z.1.2 z.2.1).2
        (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.2.1) (norm_nonneg _) zero_le_one).trans_eq (one_mul 2)
    · norm_num
  have hh:=cavityMarkedScalar_double_family_data μ β ρ hβ hρ a (parisiFreeMeasure μ a)
    (fun _=>p) Prod.fst Prod.snd measurable_const measurable_fst measurable_snd F hm 2 (by norm_num) hb 7
  dsimp only at hh
  have he (r l : Paper.Overlap) (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
      F ((r,l),(cavityZeroMarkedSampleSplit n z).1)*scalarResponseSample 7 (followupCavityScalarBeta n β ρ) μ p r l
        (cavityZeroMarkedSampleSplit n z).2 =
      if r<l then cavityRestFutureSquare D μ r l (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 7 (followupCavityScalarBeta n β ρ) μ p r l (cavityZeroMarkedSampleSplit n z).2 else 0 := by
    dsimp only [F]
    split_ifs <;> simp only [zero_mul]
  simp_rw [he] at hh
  refine ⟨hh.1,?_⟩
  rw [hh.2]
  unfold cavityScalarRestThetaLast
  apply integral_congr_ae
  exact .of_forall fun r=>by
    change (∫l,∫z,if r<l then cavityRestFutureSquare D μ r l (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 7 (followupCavityScalarBeta n β ρ) μ p r l (cavityZeroMarkedSampleSplit n z).2 else 0
        ∂anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
        ∂parisiFreeMeasure μ a)=
      ∫l in Ioi r,scalarFutureCenteredPairing (followupCavityScalarBeta n β ρ) μ p r l*
        cavityRestProjectedCovariance D μ a r l p ∂parisiFreeMeasure μ a
    rw [←integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact .of_forall fun l=>by
      by_cases hr:r<l
      · simp only [if_pos hr,Set.indicator_of_mem (show l∈Ioi r from hr)]
        exact cavityZeroMarked_future_scalarSample7_centered μ n β ρ hβ hρ a p r l hr.le
      · simp only [if_neg hr,integral_zero,Set.indicator_of_notMem (show l∉Ioi r from hr)]

end HexagonPaper
