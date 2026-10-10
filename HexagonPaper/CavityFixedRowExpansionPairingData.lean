module
public import HexagonPaper.CavityFixedRowExpansionCovarianceBounds
public import HexagonPaper.CavityFixedRowExpansionFamilySections

@[expose] public section

/-! Integrable all-profile K3 response, with the actual main covariance
column and the literal signed T1 residual separated by honest linearity. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem cavityFixedRowMarked_kernel3_data_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let R:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
      ∫r,cavityRestTwoTimeMeanPairing D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 3 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2 ∂parisiFreeMeasure μ a
    Integrable R P ∧ (∫z,R z ∂P)=
      (∫r,cavityRestCovarianceColumn D μ a p (min p r)*scalarResponseKernel3 B μ p r 0 ∂parisiFreeMeasure μ a)+
      ∫r,cavitySignedScalarKernelOne B μ r p*(∫z,cavitySignedResponseSymmetricMeanResidual D μ p r z*
        cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a := by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let F:=fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    cavityRestTwoTimeMeanPairing D μ p z.1 z.2.1*cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1
  have hm : Measurable F := by
    simpa only [Function.comp_def] using (measurable_cavityRestTwoTimeMeanPairing_centered_family D μ a p).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hb (z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)) : ‖F z‖≤6 := by
    dsimp only [F]
    exact norm_cavityRestTwoTimeMeanPairing_centered_family D μ a p p z.1 z.2
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (parisiFreeMeasure μ a)
    (fun _=>p) id (fun _=>0) measurable_const measurable_id measurable_const F hm 6 (by norm_num) hb 3
  simp only [id_eq] at hi
  let main:=fun r=>cavityRestCovarianceColumn D μ a p (min p r)*scalarResponseKernel3 B μ p r 0
  let res:=fun r=>cavitySignedScalarKernelOne B μ r p*(∫z,cavitySignedResponseSymmetricMeanResidual D μ p r z*
    cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a)
  have hmain : Integrable main (parisiFreeMeasure μ a) :=
    integrable_cavityRestCovarianceColumn_kernel3 D μ a B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p
  have hres : Integrable res (parisiFreeMeasure μ a) := by
    apply (hi.integral_prod_left.sub hmain).congr
    exact .of_forall fun r=>by
      dsimp only [Pi.sub_apply,F,main,res]
      rw [cavityZeroMarked_kernel3_two_time_centered μ n β ρ hβ hρ a p r]
      ring
  refine ⟨hi.integral_prod_right,?_⟩
  rw [cavityFixedRowMarked_kernel3_integral_all_profiles μ n β ρ hβ hρ a p]
  exact integral_add hmain hres

end HexagonPaper
