module
public import QuantitativeFollowup.ScalarFieldJointContinuity
public import QuantitativeFollowup.ScalarFutureSquare
public import FourPapersCommon.ParisiNoiseContinuity

@[expose] public section

/-! The actual scalar mean and curvature processes are jointly continuous
in the weak profile and observation level, for every Brownian sample.
Their expectations are therefore genuine continuous kernel coefficients. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

theorem continuous_parisiNoiseStatePath_parameter (β h : ℝ) :
    Continuous (fun z : Paper.ParisiMeasure×C(Paper.Overlap,ℝ) => parisiNoiseStatePath β h z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_parisiNoiseStatePath_of_weak_and_noise (L := 𝓝 p) β h
    (fun z : Paper.ParisiMeasure×C(Paper.Overlap,ℝ) => z.1) p.1 continuous_fst.continuousAt
    (fun z => z.2) p.2 continuous_snd.continuousAt

@[fun_prop] theorem continuous_scalarPhysicalSplitState_parameter (β h : ℝ) (ω : Paper.BrownianSample) :
    Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap => parisiPhysicalSplitState β h z.1 z.2 ω) := by
  have harg : Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap => (z.1,canonicalBrownianPath ω)) :=
    continuous_fst.prodMk continuous_const
  have hp := (continuous_parisiNoiseStatePath_parameter β h).comp harg
  exact continuous_eval.comp (hp.prodMk continuous_snd)

@[fun_prop] theorem continuous_scalarM_parameter (β : ℝ) (hβ : β ≠ 0) (ω : Paper.BrownianSample) :
    Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap => M β z.1 z.2 ω) := by
  have hp : Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap =>
      (z.1,((z.2 : ℝ),parisiPhysicalSplitState β 0 z.1 z.2 ω))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd |>.prodMk
      (continuous_scalarPhysicalSplitState_parameter β 0 ω))
  have hh := (continuous_parisiGradient_measure_joint β).comp hp
  change Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap =>
    parisiGradient β z.1 (z.2,parisiPhysicalSplitState β 0 z.1 z.2 ω)) at hh
  simpa only [scalarGradient_physicalSplitState β hβ] using hh

theorem scalarHessian_physicalSplitState (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (ω : Paper.BrownianSample) :
    parisiHessian β μ (q,parisiPhysicalSplitState β 0 μ q ω)=C β μ q ω := by
  simp only [parisiPhysicalSplitState,parisiNoiseStatePath_canonical β 0 hβ,
    C,jetProcess,parisiSpatialJet_two,optimalStateReal_eq_selected β hβ μ]

@[fun_prop] theorem continuous_scalarC_parameter (β : ℝ) (hβ : β ≠ 0) (ω : Paper.BrownianSample) :
    Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap => C β z.1 z.2 ω) := by
  have hp : Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap =>
      (z.1,((z.2 : ℝ),parisiPhysicalSplitState β 0 z.1 z.2 ω))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd |>.prodMk
      (continuous_scalarPhysicalSplitState_parameter β 0 ω))
  have hh := (continuous_parisiHessian_measure_joint β hβ).comp hp
  change Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap =>
    parisiHessian β z.1 (z.2,parisiPhysicalSplitState β 0 z.1 z.2 ω)) at hh
  simpa only [scalarHessian_physicalSplitState β hβ] using hh

@[fun_prop] theorem continuous_scalarGamma_parameter (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap => Gamma β z.1 z.2) := by
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _ => (1 : ℝ))
  · intro p
    exact ((measurable_M β p.1 p.2 p.2.property).pow_const 2).aestronglyMeasurable
  · intro p
    exact .of_forall fun ω => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (scalar_M_norm_le_one β p.1 p.2 ω)
  · exact integrable_const _
  · exact .of_forall fun ω => (continuous_scalarM_parameter β hβ ω).pow 2

@[fun_prop] theorem continuous_scalarCenteredSquare_parameter (β : ℝ) (hβ : β ≠ 0)
    (ω : Paper.BrownianSample) :
    Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap => scalarCenteredSquare β z.1 z.2 ω) :=
  (continuous_scalarM_parameter β hβ ω).pow 2 |>.sub (continuous_scalarGamma_parameter β hβ)

theorem scalarCenteredSquare_norm_le_one (β : ℝ) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) (ω : Paper.BrownianSample) : ‖scalarCenteredSquare β μ p ω‖ ≤ 1 := by
  have hM : M β μ p ω^2∈Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _,by simpa only [norm_pow,Real.norm_eq_abs,sq_abs] using
      (pow_le_one₀ (n := 2) (norm_nonneg (M β μ p ω)) (scalar_M_norm_le_one β μ p ω))⟩
  rw [scalarCenteredSquare,Real.norm_eq_abs,abs_le]
  constructor <;> linarith [scalarGamma_nonneg β μ p,scalarGamma_le_one β μ p p.property,hM.1,hM.2]

end QuantitativeFollowup
