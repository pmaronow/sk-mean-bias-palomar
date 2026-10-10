module
public import HexagonPaper.CavityFixedRowExpansionFutureGradientJointNative
public import HexagonPaper.CavityFixedRowExpansionFamilySections
public import QuantitativeFollowup.FollowupCavitySignedResponseMixedHessianIntegrals

@[expose] public section

/-! Honest native sections and Fubini for the two varying-time rest terms. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cavityFixedRowMarked_rest_mixed_sections_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let R:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
      ∫r,cavityZeroRestMixedHessian D μ r p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 6 B μ p p r (cavityZeroMarkedSampleSplit n z).2 ∂parisiFreeMeasure μ a
    Integrable R P ∧ (∫z,R z ∂P)=
      ∫r,∫z,cavityZeroRestMixedHessian D μ r p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 6 B μ p p r (cavityZeroMarkedSampleSplit n z).2 ∂P ∂parisiFreeMeasure μ a := by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let F:=fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    cavityZeroRestMixedHessian D μ z.1 p z.2.1
  have hm : Measurable F := by
    simpa only [F,cavityZeroRestMixedHessian,Function.comp_def] using
      ((measurable_joint_cavitySignedResponseMixedHessian D μ).comp
        ((measurable_fst.prodMk measurable_const).prodMk measurable_snd.fst)).div_const ((n:ℝ)^2)
  have hb (z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)) :
      ‖F z‖≤(n:ℝ)^2/|(n:ℝ)^2| := norm_cavityZeroRestMixedHessian_le D μ z.1 p z.2.1
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (parisiFreeMeasure μ a)
    (fun _=>p) (fun _=>p) id measurable_const measurable_const measurable_id F hm
    ((n:ℝ)^2/|(n:ℝ)^2|) (by positivity) hb 6
  simp only [id_eq] at hi
  refine ⟨hi.integral_prod_right,?_⟩
  exact (integral_integral_swap hi).symm

theorem cavityFixedRowMarked_rest_future_sections_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let R:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
      ∫r,if p<r then cavityZeroRestFutureFieldDerivative D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 7 B μ p p r (cavityZeroMarkedSampleSplit n z).2 else 0 ∂parisiFreeMeasure μ a
    Integrable R P ∧ (∫z,R z ∂P)=
      ∫r,∫z,if p<r then cavityZeroRestFutureFieldDerivative D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 7 B μ p p r (cavityZeroMarkedSampleSplit n z).2 else 0 ∂P ∂parisiFreeMeasure μ a := by
  classical
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let F:=fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    if p<z.1 then cavityZeroRestFutureFieldDerivative D μ p z.1 z.2.1 else 0
  have hm : Measurable F := by
    simpa only [F,Function.comp_def] using (measurable_cavityZeroRestFutureFieldDerivative_strict_time_joint D μ p).comp
      (measurable_fst.prodMk measurable_snd.fst)
  have hb (z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)) :
      ‖F z‖≤cavityNativeFutureGradientBound D/|(n:ℝ)| := by
    dsimp only [F]
    split_ifs with hz
    · exact norm_cavityZeroRestFutureFieldDerivative_le D μ p z.1 hz.le z.2.1
    · simp only [norm_zero]
      exact div_nonneg (cavityNativeFutureGradientBound_nonneg D) (abs_nonneg _)
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (parisiFreeMeasure μ a)
    (fun _=>p) (fun _=>p) id measurable_const measurable_const measurable_id F hm
    (cavityNativeFutureGradientBound D/|(n:ℝ)|)
    (div_nonneg (cavityNativeFutureGradientBound_nonneg D) (abs_nonneg _)) hb 7
  simp only [id_eq] at hi
  have he (r : Paper.Overlap) (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
      F (r,(cavityZeroMarkedSampleSplit n z).1)*scalarResponseSample 7 (followupCavityScalarBeta n β ρ) μ p p r
        (cavityZeroMarkedSampleSplit n z).2 =
      if p<r then cavityZeroRestFutureFieldDerivative D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 7 (followupCavityScalarBeta n β ρ) μ p p r (cavityZeroMarkedSampleSplit n z).2 else 0 := by
    dsimp only [F]
    split_ifs <;> simp only [zero_mul]
  refine ⟨?_,?_⟩
  · simpa only [he] using hi.integral_prod_right
  · have hi' : Integrable (Function.uncurry (fun r z=>F (r,(cavityZeroMarkedSampleSplit n z).1)*
        scalarResponseSample 7 (followupCavityScalarBeta n β ρ) μ p p r (cavityZeroMarkedSampleSplit n z).2))
        ((parisiFreeMeasure μ a).prod (anisotropicMeasureSpinPathLaw
          (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)) := by
      simpa only [Function.uncurry_def] using hi
    have hs:=(integral_integral_swap hi').symm
    simpa only [he] using hs

end HexagonPaper
