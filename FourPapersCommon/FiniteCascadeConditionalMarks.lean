module
public import FourPapersCommon.FiniteCascadeTreeGaussianDensity
public import FourPapersCommon.FiniteStateCascadeExpectations

@[expose] public section

/-! Fresh conditional terminal marks at an actual recorded-tree vertex.
The new spins use independent genuine Gibbs-cascade continuations from
that vertex field. Deletion and the mean-product identity are proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

inductive FiniteCascadeRecordVertex : {j : ℕ} → FiniteTerminalGenealogy j → Type
  | root {j : ℕ} (T : FiniteTerminalGenealogy j) : FiniteCascadeRecordVertex T
  | child {j : ℕ} {T : FiniteTerminalGenealogy j} :
      FiniteCascadeRecordVertex T → FiniteCascadeRecordVertex (.advance T)
  | left {j : ℕ} {T U : FiniteTerminalGenealogy j} :
      FiniteCascadeRecordVertex T → FiniteCascadeRecordVertex (.fork T U)
  | right {j : ℕ} {T U : FiniteTerminalGenealogy j} :
      FiniteCascadeRecordVertex U → FiniteCascadeRecordVertex (.fork T U)

namespace FiniteCascadeRecordVertex

@[reducible] def depth : {j : ℕ} → {T : FiniteTerminalGenealogy j} →
    FiniteCascadeRecordVertex T → ℕ
  | j, _, .root _ => j
  | _, _, .child v => depth v
  | _, _, .left v => depth v
  | _, _, .right v => depth v

theorem depth_le {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    v.depth ≤ j := by
  induction v with
  | root T => exact le_rfl
  | child v ih => exact ih.trans (Nat.le_succ _)
  | left v ih => exact ih
  | right v ih => exact ih

@[reducible] def field : {j : ℕ} → {T : FiniteTerminalGenealogy j} →
    FiniteCascadeRecordVertex T → FiniteStateField S →
      Records (FiniteStateField S) S T → FiniteStateField S
  | _, _, .root _ => fun H _ => H
  | _, _, .child v => fun _ z => field v z.1 z.2
  | _, _, .left v => fun H z => field v H z.1
  | _, _, .right v => fun H z => field v H z.2

omit [MeasurableSingletonClass S] [Nonempty S] in
theorem measurable_field {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : Measurable (Function.uncurry (v.field (S:=S))) := by
  induction v with
  | root T => exact measurable_fst
  | child v ih => exact ih.comp measurable_snd
  | left v ih => exact ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  | right v ih => exact ih.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

end FiniteCascadeRecordVertex

def finiteCascadeVertexPairKernel (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    Kernel (FiniteStateField S × Records (FiniteStateField S) S T) (S × S) :=
  (finiteStateCascadeGibbsKernel V a L v.depth ×ₖ finiteStateCascadeGibbsKernel V a L v.depth).comap
    (Function.uncurry (v.field (S:=S))) v.measurable_field

theorem finiteCascadeVertexPairKernel_markov (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (finiteCascadeVertexPairKernel V a L v) := by
  have := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L v.depth
  unfold finiteCascadeVertexPairKernel
  infer_instance

def finiteCascadeVertexMarkedLaw (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S × Records (FiniteStateField S) S T)) :=
  P ⊗ₘ finiteCascadeVertexPairKernel V a L v

theorem finiteCascadeVertexMarkedLaw_fst (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S × Records (FiniteStateField S) S T)) [SFinite P] :
    (finiteCascadeVertexMarkedLaw V a L v P).fst = P := by
  have := finiteCascadeVertexPairKernel_markov V a ha L v
  exact Measure.fst_compProd _ _

theorem finiteCascadeVertexMarkedLaw_probability (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S × Records (FiniteStateField S) S T)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (finiteCascadeVertexMarkedLaw V a L v P) := by
  have := finiteCascadeVertexPairKernel_markov V a ha L v
  unfold finiteCascadeVertexMarkedLaw
  infer_instance

theorem integral_finiteCascadeVertexMarkedLaw_product (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S × Records (FiniteStateField S) S T)) [IsProbabilityMeasure P]
    (F : FiniteStateField S × Records (FiniteStateField S) S T → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C)
    (K M : FiniteStateField S) :
    (∫z,F z.1*K z.2.1*M z.2.2 ∂finiteCascadeVertexMarkedLaw V a L v P) =
      ∫z,F z * fderiv ℝ (finiteStateGaussianTerminalCascade V a L v.depth)
        (v.field z.1 z.2) K * fderiv ℝ (finiteStateGaussianTerminalCascade V a L v.depth)
          (v.field z.1 z.2) M ∂P := by
  classical
  have := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L v.depth
  have := finiteCascadeVertexPairKernel_markov V a ha L v
  have := finiteCascadeVertexMarkedLaw_probability V a ha L v P
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
      (finiteCascadeVertexMarkedLaw V a L v P) := by
    apply (integrable_const (C*BK*BM)).mono' hobs.aestronglyMeasurable
    exact .of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hFb z.1) (hk z.2.1) (abs_nonneg _) hC)
        (hm z.2.2) (abs_nonneg _) (mul_nonneg hC (by dsimp [BK]; positivity))
  rw [finiteCascadeVertexMarkedLaw, Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun z => by
    dsimp only
    rw [finiteCascadeVertexPairKernel, Kernel.comap_apply, Kernel.prod_apply]
    rw [show (fun σ : S × S => F z*K σ.1*M σ.2) =
      (fun σ : S × S => F z*(K σ.1*M σ.2)) from by funext σ; ring,
      integral_const_mul, integral_prod_mul]
    rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L v.depth,
      fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L v.depth]
    simp only [Function.uncurry, mul_assoc]

end FourPapersCommon
