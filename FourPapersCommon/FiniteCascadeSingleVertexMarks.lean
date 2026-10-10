module
public import FourPapersCommon.FiniteCascadeConditionalMarks

@[expose] public section

/-! A single genuine normalized terminal continuation from a retained
vertex, together with its exact weighted conditional-mean identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def finiteCascadeSingleVertexKernel (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    Kernel (FiniteStateField S×Records (FiniteStateField S) S T) S :=
  (finiteStateCascadeGibbsKernel V a L v.depth).comap
    (Function.uncurry (v.field (S:=S))) v.measurable_field

theorem finiteCascadeSingleVertexKernel_markov (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (finiteCascadeSingleVertexKernel V a L v) := by
  have := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L v.depth
  unfold finiteCascadeSingleVertexKernel
  infer_instance

def finiteCascadeSingleVertexMarkedLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S×Records (FiniteStateField S) S T)) :=
  P ⊗ₘ finiteCascadeSingleVertexKernel V a L v

theorem finiteCascadeSingleVertexMarkedLaw_probability (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S×Records (FiniteStateField S) S T)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (finiteCascadeSingleVertexMarkedLaw V a L v P) := by
  have := finiteCascadeSingleVertexKernel_markov V a ha L v
  unfold finiteCascadeSingleVertexMarkedLaw
  infer_instance

theorem finiteCascadeSingleVertexMarkedLaw_fst (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S×Records (FiniteStateField S) S T)) [SFinite P] :
    (finiteCascadeSingleVertexMarkedLaw V a L v P).fst=P := by
  have := finiteCascadeSingleVertexKernel_markov V a ha L v
  exact Measure.fst_compProd _ _

theorem integral_finiteCascadeSingleVertexMarkedLaw_product
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S×Records (FiniteStateField S) S T)) [IsProbabilityMeasure P]
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hFb : ∀z,|F z|≤C) (K : FiniteStateField S) :
    (∫z,F z.1*K z.2 ∂finiteCascadeSingleVertexMarkedLaw V a L v P)=
      ∫z,F z*fderiv ℝ (finiteStateGaussianTerminalCascade V a L v.depth) (v.field z.1 z.2) K ∂P := by
  have := finiteCascadeSingleVertexKernel_markov V a ha L v
  have := finiteCascadeSingleVertexMarkedLaw_probability V a ha L v P
  have hm : Measurable (fun z : (FiniteStateField S×Records (FiniteStateField S) S T)×S=>F z.1*K z.2) :=
    (hF.comp measurable_fst).mul ((measurable_of_finite K).comp measurable_snd)
  have hi : Integrable (fun z=>F z.1*K z.2) (finiteCascadeSingleVertexMarkedLaw V a L v P) := by
    apply (integrable_const (C*‖K‖)).mono' hm.aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖F z.1*K z.2‖≤_
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hFb z.1) (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K z.2)
        (abs_nonneg _) hC
  rw [finiteCascadeSingleVertexMarkedLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun z=>by
    dsimp only
    rw [finiteCascadeSingleVertexKernel,Kernel.comap_apply,integral_const_mul,
      ←fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha]
    rfl

end FourPapersCommon
