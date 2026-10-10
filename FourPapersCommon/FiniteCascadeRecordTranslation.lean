module
public import FourPapersCommon.FiniteCascadeTerminalTranslation
public import FourPapersCommon.FiniteCascadeTreeFeatureMeasurability

@[expose] public section

/-! A terminal-energy translation shifts every actual field record and
preserves the full normalized cascade record law, not only its spin marginal. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT OverlapPaper FiniteTerminalGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem comp_comap_initial {A B C D : Type} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (κ : Kernel A B) (η : Kernel B C) (f : D → A) (hf : Measurable f) :
    (η ∘ₖ κ).comap f hf = η ∘ₖ (κ.comap f hf) := by
  rw [← Kernel.comp_deterministic_eq_comap,
    ← Kernel.comp_deterministic_eq_comap, Kernel.comp_assoc]

theorem finiteCascadeTreeRecordKernel_terminal_add (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (finiteCascadeTreeRecordKernel (fun σ => V σ+K σ) a L T).map
        (finiteCascadeShiftRecords K 1 T) =
      (finiteCascadeTreeRecordKernel V a L T).comap (fun H => H+K) (by fun_prop) := by
  induction T with
  | leaf =>
      simpa only [finiteCascadeTreeRecordKernel, finiteCascadeShiftRecords, Kernel.map_id] using
        finiteStateGibbsKernel_terminal_add V K
  | @advance j T ih =>
      have := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
      have := isMarkovKernel_finiteCascadeTreeRecordKernel (fun σ => V σ+K σ) a ha L T
      simp only [finiteCascadeTreeRecordKernel, finiteCascadeShiftRecords, one_smul]
      change ((_ ×ₖ _) ∘ₖ _).map (Prod.map (fun H => H+K) (finiteCascadeShiftRecords K 1 T)) =
        ((_ ×ₖ _) ∘ₖ _).comap _ _
      rw [Kernel.map_comp, ← Kernel.map_prod_map _ _ (by fun_prop)
        (measurable_finiteCascadeShiftRecords K 1 T), ih,
        Kernel.id_map (by fun_prop), ← Kernel.id_comap (by fun_prop),
        ← Kernel.comap_prod, ← Kernel.comp_map _ _ (by fun_prop),
        finiteStateGaussianCascadeKernel_terminal_add V K a ha L j, ← comp_comap_initial]
  | fork T U ihT ihU =>
      have := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
      have := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L U
      have := isMarkovKernel_finiteCascadeTreeRecordKernel (fun σ => V σ+K σ) a ha L T
      have := isMarkovKernel_finiteCascadeTreeRecordKernel (fun σ => V σ+K σ) a ha L U
      change (_ ×ₖ _).map (Prod.map (finiteCascadeShiftRecords K 1 T)
        (finiteCascadeShiftRecords K 1 U)) = (_ ×ₖ _).comap _ _
      rw [← Kernel.map_prod_map _ _ (measurable_finiteCascadeShiftRecords K 1 T)
        (measurable_finiteCascadeShiftRecords K 1 U), ihT, ihU, ← Kernel.comap_prod]

end FourPapersCommon
