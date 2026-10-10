module
public import QuantitativeFollowup.ScalarSpinConditional
public import QuantitativeFollowup.ScalarProcessContinuity

@[expose] public section

/-! Actual terminal-spin conditioning used in the scalar transport response.
The curvature factor is measurable in the whole Brownian past, so the genuine
marked-spin conditional mean removes the terminal sign in the local score. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativeFollowup
open Paper FRSB FourPapersCommon
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem measurable_scalarC_past (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) :
    Measurable[canonicalBrownianFiltration (p:ℝ).toNNReal] (FRSB.C β μ p) := by
  have he : FRSB.C β μ p=fun ω=>Paper.parisiHessian β μ
      (p,parisiPhysicalSplitState β 0 μ p ω) :=
    funext fun ω=>(scalarHessian_physicalSplitState β hβ μ p ω).symm
  rw [he]
  exact (Paper.continuous_parisiHessian_all β μ).measurable.comp
    (measurable_const.prodMk (measurable_parisiPhysicalSplitState_past β 0 hβ μ p))

theorem integral_scalarMarkedSpinLaw_mean_curvature_sign (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    (∫z,FRSB.M β μ p z.1*FRSB.C β μ p z.1*Paper.spinSign z.2
      ∂scalarMarkedSpinLaw β hβ μ)=
      ∫ω,FRSB.M β μ p ω^2*FRSB.C β μ p ω ∂canonicalBrownianMeasure := by
  let Z := fun ω=>FRSB.M β μ p ω*FRSB.C β μ p ω
  have hZ := (measurable_scalarM_past β hβ μ p).mul (measurable_scalarC_past β hβ μ p)
  have hb (ω : Paper.BrownianSample) : ‖Z ω‖≤1 := by
    dsimp only [Z]
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (scalar_M_norm_le_one β μ p ω)
      (FRSB.norm_C_le_one β μ p ω) (norm_nonneg _) zero_le_one
  have he := integral_scalarMarkedSpinLaw_past_sign β hβ μ p Z hZ hb
  have hm : Measurable (fun ω=>FRSB.M β μ p ω^2*FRSB.C β μ p ω) :=
    ((FRSB.measurable_M β μ p p.property).pow_const 2).mul (FRSB.measurable_C β hβ μ p.property)
  calc
    _ = ∫z,Z z.1*FRSB.M β μ p z.1 ∂scalarMarkedSpinLaw β hβ μ := he
    _ = ∫z,FRSB.M β μ p z.1^2*FRSB.C β μ p z.1 ∂scalarMarkedSpinLaw β hβ μ := by
      apply integral_congr_ae
      exact .of_forall fun z=>by dsimp only [Z];ring
    _ = _ := integral_scalarMarkedSpinLaw_sample β hβ μ _ hm

end QuantitativeFollowup
