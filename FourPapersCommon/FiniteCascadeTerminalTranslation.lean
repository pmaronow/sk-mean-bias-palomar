module
public import FourPapersCommon.FiniteCascadeTreeFeatureLaw
public import FourPapersCommon.FiniteStateCascadeGibbsTransport

@[expose] public section

/-! Translating a terminal energy feature translates the whole genuine
Gaussian cascade, including its terminal marked-spin genealogy. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT OverlapPaper FiniteCascadeGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S] in
theorem finiteStateGaussianStepLaw_translate (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : Measurable F)
    (K H : FiniteStateField S) :
    (finiteStateGaussianStepLaw a L (fun y => F (y+K)) H).map (fun y => y+K) =
      finiteStateGaussianStepLaw a L F (H+K) := by
  have hm : Measurable (fun y => F (y+K)) := hF.comp (by fun_prop)
  rw [finiteStateGaussianStepLaw_eq_map_tilted a L _ hm,
    Measure.map_map (by fun_prop) (by fun_prop),
    finiteStateGaussianStepLaw_eq_map_tilted a L F hF]
  have he : (fun z => a*F (H+L z+K)) = (fun z => a*F (H+K+L z)) := by
    funext z
    congr 2
    abel
  rw [he]
  congr 1
  funext z
  simp only [Function.comp_def]
  abel

theorem finiteStateGaussianCascadeKernel_terminal_add (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    (finiteStateGaussianCascadeKernel a L (gtStateLogPartition (fun σ => V σ+K σ)) j).map
        (fun H => H+K) =
      (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j).comap
        (fun H => H+K) (by fun_prop) := by
  ext H B hB
  rw [Kernel.map_apply _ (by fun_prop), Kernel.comap_apply]
  have hc := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable
  have hcp := (contDiff_one_finiteStateGaussianTerminalCascade (fun σ => V σ+K σ)
    a ha L j).continuous.measurable
  change (finiteStateGaussianStepKernel (a j) (L j)
      (finiteStateGaussianTerminalCascade (fun σ => V σ+K σ) a L j) H).map
      (fun H => H+K) B =
    finiteStateGaussianStepKernel (a j) (L j)
      (finiteStateGaussianTerminalCascade V a L j) (H+K) B
  rw [finiteStateGaussianStepKernel_apply _ _ _ hcp,
    finiteStateGaussianStepKernel_apply _ _ _ hc]
  have he : finiteStateGaussianTerminalCascade (fun σ => V σ+K σ) a L j =
      fun y => finiteStateGaussianTerminalCascade V a L j (y+K) := by
    funext y
    exact finiteStateGaussianTerminalCascade_terminal_add V K a L j y
  rw [he, finiteStateGaussianStepLaw_translate (a j) (L j) _ hc]

private theorem comp_comap_initial {A B C D : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (κ : Kernel A B) (η : Kernel B C) (f : D → A) (hf : Measurable f) :
    (η ∘ₖ κ).comap f hf = η ∘ₖ (κ.comap f hf) := by
  rw [← Kernel.comp_deterministic_eq_comap,
    ← Kernel.comp_deterministic_eq_comap, Kernel.comp_assoc]

theorem finiteStateGibbsKernel_terminal_add (V : S → ℝ) (K : FiniteStateField S) :
    finiteStateGibbsKernel (fun σ => V σ+K σ) =
      (finiteStateGibbsKernel V).comap (fun H => H+K) (by fun_prop) := by
  ext H B hB
  rw [Kernel.comap_apply, finiteStateGibbsKernel_apply, finiteStateGibbsKernel_apply]
  congr 2
  funext σ
  congr 1
  unfold gtStateGibbs gtStatePartition
  congr 1
  · simp only [PiLp.add_apply]
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro τ _
    simp only [PiLp.add_apply]
    congr 1
    ring

theorem finiteStateCascadeGibbsKernel_terminal_add (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    finiteStateCascadeGibbsKernel (fun σ => V σ+K σ) a L j =
      (finiteStateCascadeGibbsKernel V a L j).comap (fun H => H+K) (by fun_prop) := by
  induction j with
  | zero =>
      simpa only [finiteStateCascadeGibbsKernel, finiteStateCascadeFieldKernel,
        sourceKernelLaw, Kernel.comp_id] using finiteStateGibbsKernel_terminal_add V K
  | succ j ih =>
      rw [finiteStateCascadeGibbsKernel_succ, finiteStateCascadeGibbsKernel_succ, ih,
        ← Kernel.comp_map _ _ (by fun_prop),
        finiteStateGaussianCascadeKernel_terminal_add V K a ha L j,
        ← comp_comap_initial]

theorem finiteCascadeGenealogyKernel_terminal_add (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteCascadeGenealogy j) :
    finiteCascadeGenealogyKernel (fun σ => V σ+K σ) a L T =
      (finiteCascadeGenealogyKernel V a L T).comap (fun H => H+K) (by fun_prop) := by
  induction T with
  | leaf j => exact finiteStateCascadeGibbsKernel_terminal_add V K a ha L j
  | @advance j T ih =>
      change _ ∘ₖ _ = (_ ∘ₖ _).comap _ _
      rw [ih, ← Kernel.comp_map _ _ (by fun_prop),
        finiteStateGaussianCascadeKernel_terminal_add V K a ha L j,
        ← comp_comap_initial]
  | fork T U ihT ihU =>
      have := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L T
      have := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L U
      change _ ×ₖ _ = (_ ×ₖ _).comap _ _
      rw [ihT, ihU, Kernel.comap_prod]

end FourPapersCommon
