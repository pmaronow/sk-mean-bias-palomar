module
public import QuantitativeFollowup.ScalarRestartFlow
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The initial-field Jacobian is a measurable function of the actual
fresh Wiener path.  The construction uses the continuous Picard state,
rather than a supplied derivative process. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem scalarRestartFlow_eq_path (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (x : ℝ) (W : C(Paper.Overlap,ℝ)) (s : ℝ) :
    scalarRestartFlow β μ a ha x W s =
      parisiRestartNoiseStatePath β x μ a ha W (projIcc 0 1 zero_le_one s) := by
  simp only [scalarRestartFlow,parisiRestartNoiseStatePath,parisiStatePath,
    parisiStateReal,parisiNoiseExtension,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    smul_eq_mul]
  rfl

theorem measurable_uncurry_scalarRestartFlow_noise (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) (x : ℝ) :
    Measurable (fun z : C(Paper.Overlap,ℝ) × ℝ => scalarRestartFlow β μ a ha x z.1 z.2) := by
  have hp : Measurable (fun z : C(Paper.Overlap,ℝ) × ℝ =>
      parisiRestartNoiseStatePath β x μ a ha z.1) :=
    (measurable_parisiRestartNoiseStatePath β hβ μ a ha).comp
      (measurable_const.prodMk measurable_fst)
  have hproj : Measurable (fun z : C(Paper.Overlap,ℝ) × ℝ => projIcc 0 1 zero_le_one z.2) :=
    (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).measurable.comp measurable_snd
  have he : Measurable (fun z : C(Paper.Overlap,ℝ) × ℝ =>
      parisiRestartNoiseStatePath β x μ a ha z.1 (projIcc 0 1 zero_le_one z.2)) :=
    continuous_eval.measurable.comp
      (hp.prodMk hproj)
  simpa only [scalarRestartFlow_eq_path] using he

theorem measurable_scalarRestartFlowJacobian (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) (x t : ℝ) (ht : 0 ≤ t) :
    Measurable (fun W => scalarRestartFlowJacobian β μ a ha x W t) := by
  have hm : Measurable (fun z : C(Paper.Overlap,ℝ) × ℝ =>
      scalarRestartDriftDerivative β μ a ha z.2 (scalarRestartFlow β μ a ha x z.1 z.2)) :=
    (measurable_scalarRestartDriftDerivative β μ a ha).comp
      (measurable_snd.prodMk (measurable_uncurry_scalarRestartFlow_noise β hβ μ a ha x))
  have hi : Measurable (fun W : C(Paper.Overlap,ℝ) =>
      ∫ s in Ioc 0 t,scalarRestartDriftDerivative β μ a ha s
        (scalarRestartFlow β μ a ha x W s)) :=
    (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 t))).measurable
  simpa only [scalarRestartFlowJacobian,intervalIntegral.integral_of_le ht,Function.comp_def] using
    Real.continuous_exp.measurable.comp hi

end QuantitativeFollowup
