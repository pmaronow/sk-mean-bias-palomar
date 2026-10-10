module
public import FourPapersCommon.FiniteCascadeConditionalMarks

@[expose] public section

/-! Independent terminal continuations from two arbitrary actual vertices.
The deletion law and their conditional mean-product formula are genuine. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def finiteCascadeCrossVertexPairKernel (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    Kernel (FiniteStateField S × Records (FiniteStateField S) S T) (S × S) :=
  (finiteStateCascadeGibbsKernel V a L v.depth).comap
    (Function.uncurry (v.field (S:=S))) v.measurable_field ×ₖ
  (finiteStateCascadeGibbsKernel V a L w.depth).comap
    (Function.uncurry (w.field (S:=S))) w.measurable_field

theorem finiteCascadeCrossVertexPairKernel_markov (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (finiteCascadeCrossVertexPairKernel V a L v w) := by
  have := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L v.depth
  have := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L w.depth
  unfold finiteCascadeCrossVertexPairKernel
  infer_instance

def finiteCascadeCrossVertexMarkedLaw (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S × Records (FiniteStateField S) S T)) :=
  P ⊗ₘ finiteCascadeCrossVertexPairKernel V a L v w

theorem finiteCascadeCrossVertexMarkedLaw_fst (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S × Records (FiniteStateField S) S T)) [SFinite P] :
    (finiteCascadeCrossVertexMarkedLaw V a L v w P).fst = P := by
  have := finiteCascadeCrossVertexPairKernel_markov V a ha L v w
  exact Measure.fst_compProd _ _

theorem finiteCascadeCrossVertexMarkedLaw_probability (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S × Records (FiniteStateField S) S T)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (finiteCascadeCrossVertexMarkedLaw V a L v w P) := by
  have := finiteCascadeCrossVertexPairKernel_markov V a ha L v w
  unfold finiteCascadeCrossVertexMarkedLaw
  infer_instance

theorem integral_finiteCascadeCrossVertexMarkedLaw_product (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S × Records (FiniteStateField S) S T)) [IsProbabilityMeasure P]
    (F : FiniteStateField S × Records (FiniteStateField S) S T → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C)
    (K M : FiniteStateField S) :
    (∫z,F z.1*K z.2.1*M z.2.2 ∂finiteCascadeCrossVertexMarkedLaw V a L v w P) =
      ∫z,F z * fderiv ℝ (finiteStateGaussianTerminalCascade V a L v.depth)
        (v.field z.1 z.2) K * fderiv ℝ (finiteStateGaussianTerminalCascade V a L w.depth)
          (w.field z.1 z.2) M ∂P := by
  classical
  have := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L v.depth
  have := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L w.depth
  have := finiteCascadeCrossVertexPairKernel_markov V a ha L v w
  have := finiteCascadeCrossVertexMarkedLaw_probability V a ha L v w P
  let BK : ℝ := ∑σ : S,|K σ|
  let BM : ℝ := ∑σ : S,|M σ|
  have hk (σ : S) : |K σ| ≤ BK := Finset.single_le_sum (fun τ _ => abs_nonneg (K τ)) (Finset.mem_univ σ)
  have hm (σ : S) : |M σ| ≤ BM := Finset.single_le_sum (fun τ _ => abs_nonneg (M τ)) (Finset.mem_univ σ)
  have hKm : Measurable (fun σ : S => K σ) := measurable_of_finite _
  have hMm : Measurable (fun σ : S => M σ) := measurable_of_finite _
  have hobs : Measurable (fun z :
      (FiniteStateField S × Records (FiniteStateField S) S T) × (S × S) =>
        F z.1*K z.2.1*M z.2.2) :=
    ((hF.comp measurable_fst).mul (hKm.comp (measurable_fst.comp measurable_snd))).mul
      (hMm.comp (measurable_snd.comp measurable_snd))
  have hi : Integrable (fun z => F z.1*K z.2.1*M z.2.2)
      (finiteCascadeCrossVertexMarkedLaw V a L v w P) := by
    apply (integrable_const (C*BK*BM)).mono' hobs.aestronglyMeasurable
    exact .of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hFb z.1) (hk z.2.1) (abs_nonneg _) hC)
        (hm z.2.2) (abs_nonneg _) (mul_nonneg hC (by dsimp [BK]; positivity))
  rw [finiteCascadeCrossVertexMarkedLaw, Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun z => by
    dsimp only
    rw [finiteCascadeCrossVertexPairKernel, Kernel.prod_apply, Kernel.comap_apply, Kernel.comap_apply]
    rw [show (fun σ : S × S => F z*K σ.1*M σ.2) =
      (fun σ : S × S => F z*(K σ.1*M σ.2)) from by funext σ; ring,
      integral_const_mul, integral_prod_mul]
    rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L v.depth,
      fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L w.depth]
    simp only [Function.uncurry, mul_assoc]


end FourPapersCommon
