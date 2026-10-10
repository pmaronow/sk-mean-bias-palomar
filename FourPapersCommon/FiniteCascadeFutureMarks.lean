module
public import FourPapersCommon.FiniteCascadeConditionalMarks
public import FourPapersCommon.FiniteStateCascadeRecurrence

@[expose] public section

/-! Two genuine fresh terminal continuations share the actual future field
up to a prescribed cascade level and branch independently afterwards. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT FiniteTerminalGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def finiteCascadeFuturePairKernel (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ) :
    Kernel (FiniteStateField S×Records (FiniteStateField S) S T) (S×S) :=
  ((finiteStateCascadeGibbsKernel V a L p ×ₖ finiteStateCascadeGibbsKernel V a L p) ∘ₖ
    sourceKernelLaw (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+r))
      (v.depth-p)).comap (Function.uncurry (v.field (S:=S))) v.measurable_field

theorem finiteCascadeFuturePairKernel_markov (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ) :
    IsMarkovKernel (finiteCascadeFuturePairKernel V a L v p) := by
  have := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L p
  have := isMarkovKernel_sourceKernelLaw
    (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+r))
    (fun r=>isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L (p+r)) (v.depth-p)
  unfold finiteCascadeFuturePairKernel
  infer_instance

theorem finiteCascadeFuturePairKernel_apply (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (z : FiniteStateField S×Records (FiniteStateField S) S T) :
    finiteCascadeFuturePairKernel V a L v p z=
      finiteStateCascadeSplitLaw V a L p (v.depth-p) (v.field z.1 z.2) := by
  rw [finiteCascadeFuturePairKernel,Kernel.comap_apply,Kernel.comp_apply]
  rfl

def finiteCascadeFutureMarkedLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (P : Measure (FiniteStateField S×Records (FiniteStateField S) S T)) :=
  P ⊗ₘ finiteCascadeFuturePairKernel V a L v p

theorem finiteCascadeFutureMarkedLaw_probability (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (P : Measure (FiniteStateField S×Records (FiniteStateField S) S T)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (finiteCascadeFutureMarkedLaw V a L v p P) := by
  have := finiteCascadeFuturePairKernel_markov V a ha L v p
  unfold finiteCascadeFutureMarkedLaw
  infer_instance

theorem finiteCascadeFutureMarkedLaw_fst (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (P : Measure (FiniteStateField S×Records (FiniteStateField S) S T)) [SFinite P] :
    (finiteCascadeFutureMarkedLaw V a L v p P).fst=P := by
  have := finiteCascadeFuturePairKernel_markov V a ha L v p
  exact Measure.fst_compProd _ _

theorem integral_finiteCascadeFutureMarkedLaw_product (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (P : Measure (FiniteStateField S×Records (FiniteStateField S) S T)) [IsProbabilityMeasure P]
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hFb : ∀z,|F z|≤C)
    (K M : FiniteStateField S) :
    (∫z,F z.1*K z.2.1*M z.2.2 ∂finiteCascadeFutureMarkedLaw V a L v p P)=
      ∫z,F z*finiteStateCascadePairMoment V a L p (v.depth-p) (v.field z.1 z.2) K M ∂P := by
  have := finiteCascadeFuturePairKernel_markov V a ha L v p
  have := finiteCascadeFutureMarkedLaw_probability V a ha L v p P
  have hm : Measurable (fun z : (FiniteStateField S×Records (FiniteStateField S) S T)×(S×S)=>
      F z.1*K z.2.1*M z.2.2) :=
    ((hF.comp measurable_fst).mul ((measurable_of_finite K).comp
      (measurable_fst.comp measurable_snd))).mul ((measurable_of_finite M).comp
        (measurable_snd.comp measurable_snd))
  have hi : Integrable (fun z=>F z.1*K z.2.1*M z.2.2) (finiteCascadeFutureMarkedLaw V a L v p P) := by
    apply (integrable_const (C*‖K‖*‖M‖)).mono' hm.aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖F z.1*K z.2.1*M z.2.2‖≤_
      rw [Real.norm_eq_abs,abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hFb z.1)
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K z.2.1) (abs_nonneg _) hC)
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le M z.2.2)
        (abs_nonneg _) (mul_nonneg hC (norm_nonneg _))
  rw [finiteCascadeFutureMarkedLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun z=>by
    dsimp only
    rw [finiteCascadeFuturePairKernel_apply]
    rw [show (fun σ : S×S=>F z*K σ.1*M σ.2)=(fun σ : S×S=>F z*(K σ.1*M σ.2)) from by
      funext σ;ring,integral_const_mul]
    rw [←finiteStateCascadePairMoment_eq_splitLaw V a ha]

end FourPapersCommon
