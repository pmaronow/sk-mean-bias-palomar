module
public import HexagonPaper.CavityFixedRowExpansionCoefficientIntegrability
public import HexagonPaper.CavityFixedRowExpansionDoubleFamilySections

@[expose] public section

/-! Actual K4/K6 density terms split into covariance columns and literal
signed T2 residuals under arbitrary profiles. Every integral is honest. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cavityFixedRowMarked_kernel4_data_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let R:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
      ∫r,cavityRestTerminalMeanPairing D μ r (cavityZeroMarkedSampleSplit n z).1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 4 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2 ∂parisiFreeMeasure μ a
    Integrable R P ∧ (∫z,R z ∂P)=
      (∫r,cavityRestCovarianceColumn D μ a p r*scalarResponseKernel4 B μ p r 0 ∂parisiFreeMeasure μ a)+
      ∫r,cavitySignedScalarKernelMarked B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ r p*
        (∫z,cavitySignedResponseTerminalResidual D μ r z*cavitySignedResponseCenteredSelfOverlap D μ a p z.1
          ∂anisotropicMeasureSpinPathLaw D μ a) ∂parisiFreeMeasure μ a := by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let F:=fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    cavityRestTerminalMeanPairing D μ z.1 z.2*cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (parisiFreeMeasure μ a)
    (fun _=>p) id (fun _=>0) measurable_const measurable_id measurable_const F
      (measurable_cavityRestTerminalMeanPairing_centered_family D μ a p) 6 (by norm_num)
      (fun z=>norm_cavityRestTerminalMeanPairing_centered_family D μ a p z.1 z.2) 4
  simp only [id_eq] at hi
  let main:=fun r=>cavityRestCovarianceColumn D μ a p r*scalarResponseKernel4 B μ p r 0
  let res:=fun r=>cavitySignedScalarKernelMarked B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ r p*
    (∫z,cavitySignedResponseTerminalResidual D μ r z*cavitySignedResponseCenteredSelfOverlap D μ a p z.1
      ∂anisotropicMeasureSpinPathLaw D μ a)
  have hk (r : Paper.Overlap) : scalarResponseCoefficient (4:Fin 8) B μ p r 0 = scalarResponseKernel4 B μ p r 0 := rfl
  have hmain : Integrable main (parisiFreeMeasure μ a) := by
    simpa only [main,hk,id_eq] using integrable_cavityRestCovarianceColumn_coefficient D μ a B
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p (parisiFreeMeasure μ a)
      id (fun _=>p) id (fun _=>0) measurable_id measurable_const measurable_id measurable_const 4
  have hres : Integrable res (parisiFreeMeasure μ a) := by
    apply (hi.integral_prod_left.sub hmain).congr
    exact .of_forall fun r=>by
      dsimp only [F,main,res,Pi.sub_apply]
      rw [cavityZeroMarked_kernel4_terminal_centered μ n β ρ hβ hρ a p r]
      ring
  refine ⟨hi.integral_prod_right,?_⟩
  rw [cavityFixedRowMarked_kernel4_integral_all_profiles μ n β ρ hβ hρ a p]
  exact integral_add hmain hres

theorem cavityFixedRowMarked_kernel6_data_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let R:=fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
      ∫r,∫l,cavityRestTwoTimeMeanPairing D μ r l (cavityZeroMarkedSampleSplit n z).1.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
        scalarResponseSample 6 B μ p r l (cavityZeroMarkedSampleSplit n z).2
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a
    Integrable R P ∧ (∫z,R z ∂P)=
      (∫r,∫l,cavityRestCovarianceColumn D μ a p (min r l)*scalarResponseKernel6 B μ p r l
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
      ∫r,∫l,cavitySignedScalarKernelTriple B μ (r,l) p*(∫z,cavitySignedResponseSymmetricMeanResidual D μ r l z*
        cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a)
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a := by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let ν:=parisiFreeMeasure μ a
  let F:=fun z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    cavityRestTwoTimeMeanPairing D μ z.1.1 z.1.2 z.2.1*cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1
  have hm : Measurable F := measurable_cavityRestTwoTimeMeanPairing_centered_family D μ a p
  have hb (z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)) : ‖F z‖≤6 :=
    norm_cavityRestTwoTimeMeanPairing_centered_family D μ a p z.1.1 z.1.2 z.2
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (ν.prod ν) (fun _=>p) Prod.fst Prod.snd
    measurable_const measurable_fst measurable_snd F hm 6 (by norm_num) hb 6
  let main:=fun x : Paper.Overlap×Paper.Overlap=>cavityRestCovarianceColumn D μ a p (min x.1 x.2)*scalarResponseKernel6 B μ p x.1 x.2
  let res:=fun x : Paper.Overlap×Paper.Overlap=>cavitySignedScalarKernelTriple B μ x p*(∫z,cavitySignedResponseSymmetricMeanResidual D μ x.1 x.2 z*
    cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a)
  have hk (r l : Paper.Overlap) : scalarResponseCoefficient (6:Fin 8) B μ p r l = scalarResponseKernel6 B μ p r l := rfl
  have hmain : Integrable main (ν.prod ν) := by
    simpa only [main,hk] using integrable_cavityRestCovarianceColumn_coefficient D μ a B
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p (ν.prod ν)
      (fun x=>min x.1 x.2) (fun _=>p) Prod.fst Prod.snd (measurable_fst.min measurable_snd)
      measurable_const measurable_fst measurable_snd 6
  have hp (x : Paper.Overlap×Paper.Overlap) :
      (∫z,F (x,(cavityZeroMarkedSampleSplit n z).1)*scalarResponseSample 6 B μ p x.1 x.2
        (cavityZeroMarkedSampleSplit n z).2 ∂anisotropicMeasureSpinPathLaw
          (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=main x+res x :=
    cavityZeroMarked_kernel6_two_time_centered μ n β ρ hβ hρ a p x.1 x.2
  have hres : Integrable res (ν.prod ν) := by
    apply (hi.integral_prod_left.sub hmain).congr
    exact .of_forall fun x=>by
      dsimp only [Pi.sub_apply]
      rw [hp]
      ring
  have hh:=cavityMarkedScalar_double_family_data μ β ρ hβ hρ a ν (fun _=>p) Prod.fst Prod.snd
    measurable_const measurable_fst measurable_snd F hm 6 (by norm_num) hb 6
  dsimp only at hh
  refine ⟨hh.1,?_⟩
  rw [hh.2]
  change (∫r,∫l,∫z,F ((r,l),(cavityZeroMarkedSampleSplit n z).1)*scalarResponseSample 6 B μ p r l
      (cavityZeroMarkedSampleSplit n z).2 ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a ∂ν ∂ν)=_
  rw [←integral_prod _ hi.integral_prod_left]
  have he : (∫x,∫z,F (x,(cavityZeroMarkedSampleSplit n z).1)*scalarResponseSample 6 B μ p x.1 x.2
      (cavityZeroMarkedSampleSplit n z).2 ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a ∂ν.prod ν)=
      ∫x,main x+res x ∂ν.prod ν := by
    apply integral_congr_ae
    exact .of_forall hp
  rw [he]
  rw [integral_add hmain hres,integral_prod _ hmain,integral_prod _ hres]

end HexagonPaper
