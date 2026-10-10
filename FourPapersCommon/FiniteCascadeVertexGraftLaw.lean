module
public import FourPapersCommon.FiniteCascadeVertexGraft
public import FourPapersCommon.FiniteCascadeSingleVertexMarks

@[expose] public section

/-! The explicit graft operation realizes a fresh conditional terminal mark
as an actual enlarged Gaussian tree. No marginal-law premise is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem finiteCascadeLinearRecordKernel_spin (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    (finiteCascadeTreeRecordKernel V a L (finiteCascadeLinearTerminalTree j)).map
      (finiteCascadeLinearRecordSpin j) = finiteStateCascadeGibbsKernel V a L j := by
  induction j with
  | zero =>
    simp only [finiteCascadeLinearTerminalTree, finiteCascadeTreeRecordKernel,
      finiteCascadeLinearRecordSpin, Kernel.map_id, finiteStateCascadeGibbsKernel,
      finiteStateCascadeFieldKernel, OverlapPaper.sourceKernelLaw, Kernel.comp_id]
  | succ j ih =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L
      (finiteCascadeLinearTerminalTree j)
    change ((_ ×ₖ _) ∘ₖ _).map (finiteCascadeLinearRecordSpin j ∘ Prod.snd) = _
    rw [Kernel.map_comp, Kernel.map_comp_right _ measurable_snd
      (measurable_finiteCascadeLinearRecordSpin j), ←Kernel.snd_eq, Kernel.snd_prod, ih,
      finiteStateCascadeGibbsKernel_succ]

private theorem lintegral_record_advance (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (G : Records (FiniteStateField S) S (.advance T) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻z, G z ∂finiteCascadeTreeRecordKernel V a L (.advance T) H) =
      ∫⁻Q, ∫⁻z, G (Q,z) ∂finiteCascadeTreeRecordKernel V a L T Q
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  change (∫⁻z, G z ∂((_ ×ₖ _) ∘ₖ _) H) = _
  rw [Kernel.lintegral_comp _ _ _ hG]
  apply lintegral_congr
  intro Q
  exact Kernel.lintegral_id_prod hG _ Q

theorem finiteCascadeVertexGraft_root_kernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (finiteCascadeTreeRecordKernel V a L (finiteCascadeVertexGraft (.root T))).map
      (finiteCascadeGraftRecordExtract (.root T)) =
      finiteCascadeTreeRecordKernel V a L T ×ₖ finiteStateCascadeGibbsKernel V a L j := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L
    (finiteCascadeLinearTerminalTree j)
  change (_ ×ₖ _).map (Prod.map id (finiteCascadeLinearRecordSpin j)) = _
  rw [←Kernel.map_prod_map _ _ measurable_id (measurable_finiteCascadeLinearRecordSpin j),
    Kernel.map_id, finiteCascadeLinearRecordKernel_spin V a ha L j]


private theorem measurable_single_mark_integral (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (G : Records (FiniteStateField S) S T × S → ℝ≥0∞)
    (hG : Measurable G) :
    Measurable (fun z => ∫⁻σ, G (z,σ)
      ∂finiteStateCascadeGibbsKernel V a L v.depth (v.field H z)) := by
  let κ := (finiteCascadeSingleVertexKernel V a L v).comap
    (fun z => (H,z)) (measurable_const.prodMk measurable_id)
  haveI := finiteCascadeSingleVertexKernel_markov V a ha L v
  haveI : IsMarkovKernel κ := inferInstance
  convert! hG.lintegral_kernel_prod_right' (κ:=κ) using 1


theorem lintegral_finiteCascadeVertexGraft (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (G : Records (FiniteStateField S) S T × S → ℝ≥0∞)
    (hG : Measurable G) :
    (∫⁻z, G (finiteCascadeGraftRecordExtract v z)
        ∂finiteCascadeTreeRecordKernel V a L (finiteCascadeVertexGraft v) H) =
      ∫⁻z, ∫⁻σ, G (z,σ)
        ∂finiteStateCascadeGibbsKernel V a L v.depth (v.field H z)
        ∂finiteCascadeTreeRecordKernel V a L T H := by
  induction v generalizing H with
  | @root j T =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
    haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
    rw [←Kernel.lintegral_map _ (measurable_finiteCascadeGraftRecordExtract _) _ hG,
      finiteCascadeVertexGraft_root_kernel V a ha L,
      Kernel.lintegral_prod _ _ _ hG]
  | @child j T v ih =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeVertexGraft v)
    haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L v.depth
    rw [lintegral_record_advance V a ha L _ _ _
      (hG.comp (measurable_finiteCascadeGraftRecordExtract _))]
    rw [lintegral_record_advance V a ha L T H _]
    · apply lintegral_congr
      intro Q
      simpa only [finiteCascadeGraftRecordExtract, FiniteCascadeRecordVertex.depth,
        FiniteCascadeRecordVertex.field] using
        ih Q (fun z => G ((Q,z.1),z.2))
          (hG.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    · exact measurable_single_mark_integral V a ha L (.child v) H G hG
  | @left j T U v ih =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L U
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeVertexGraft v)
    haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L v.depth
    change (∫⁻z, G (((finiteCascadeGraftRecordExtract v z.1).1,z.2),
      (finiteCascadeGraftRecordExtract v z.1).2) ∂(_ ×ₖ _) H) =
      ∫⁻z, ∫⁻σ, G (z,σ) ∂finiteStateCascadeGibbsKernel V a L v.depth (v.field H z.1)
        ∂(_ ×ₖ _) H
    have hm : Measurable (fun z : Records (FiniteStateField S) S
        (finiteCascadeVertexGraft v) × Records (FiniteStateField S) S U =>
        G (((finiteCascadeGraftRecordExtract v z.1).1,z.2),
          (finiteCascadeGraftRecordExtract v z.1).2)) := by
      simpa only [Function.comp_def] using hG.comp
        ((((measurable_finiteCascadeGraftRecordExtract v).fst.comp measurable_fst).prodMk
          measurable_snd).prodMk
            ((measurable_finiteCascadeGraftRecordExtract v).snd.comp measurable_fst))
    rw [Kernel.lintegral_prod _ _ _ hm]
    rw [ih H (fun z => ∫⁻u, G ((z.1,u),z.2) ∂finiteCascadeTreeRecordKernel V a L U H)
      ((hG.comp ((measurable_fst.comp measurable_fst |>.prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))).lintegral_prod_right')]
    rw [Kernel.lintegral_prod _ _ _]
    · apply lintegral_congr
      intro z
      exact MeasureTheory.lintegral_lintegral_swap
        (hG.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aemeasurable
    · exact measurable_single_mark_integral V a ha L (.left v) H G hG
  | @right j T U v ih =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L U
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeVertexGraft v)
    haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L v.depth
    change (∫⁻z, G ((z.1,(finiteCascadeGraftRecordExtract v z.2).1),
      (finiteCascadeGraftRecordExtract v z.2).2) ∂(_ ×ₖ _) H) =
      ∫⁻z, ∫⁻σ, G (z,σ) ∂finiteStateCascadeGibbsKernel V a L v.depth (v.field H z.2)
        ∂(_ ×ₖ _) H
    have hm : Measurable (fun z : Records (FiniteStateField S) S T ×
        Records (FiniteStateField S) S (finiteCascadeVertexGraft v) =>
        G ((z.1,(finiteCascadeGraftRecordExtract v z.2).1),
          (finiteCascadeGraftRecordExtract v z.2).2)) := by
      simpa only [Function.comp_def] using hG.comp
        ((measurable_fst.prodMk ((measurable_finiteCascadeGraftRecordExtract v).fst.comp
          measurable_snd)).prodMk
            ((measurable_finiteCascadeGraftRecordExtract v).snd.comp measurable_snd))
    rw [Kernel.lintegral_prod _ _ _ hm]
    rw [Kernel.lintegral_prod _ _ _]
    · apply lintegral_congr
      intro z
      exact ih H (fun u => G ((z,u.1),u.2))
        (hG.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    · exact measurable_single_mark_integral V a ha L (.right v) H G hG


theorem finiteCascadeVertexGraft_kernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    (finiteCascadeTreeRecordKernel V a L (finiteCascadeVertexGraft v)).map
      (finiteCascadeGraftRecordExtract v) =
      finiteCascadeTreeRecordKernel V a L T ⊗ₖ finiteCascadeSingleVertexKernel V a L v := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := finiteCascadeSingleVertexKernel_markov V a ha L v
  ext H : 1
  apply Measure.ext_of_lintegral
  intro G hG
  rw [Kernel.lintegral_map _ (measurable_finiteCascadeGraftRecordExtract _) _ hG,
    lintegral_finiteCascadeVertexGraft V a ha L v H G hG,
    Kernel.lintegral_compProd _ _ _ hG]
  rfl

theorem finiteCascadeVertexGraft_joint_law (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (μ : Measure (FiniteStateField S)) [SFinite μ] :
    (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L (finiteCascadeVertexGraft v)).map
      (fun z => ((z.1,(finiteCascadeGraftRecordExtract v z.2).1),
        (finiteCascadeGraftRecordExtract v z.2).2)) =
      finiteCascadeSingleVertexMarkedLaw V a L v (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L T) := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeVertexGraft v)
  haveI := finiteCascadeSingleVertexKernel_markov V a ha L v
  have hm := measurable_finiteCascadeGraftRecordExtract (S:=S) (E:=FiniteStateField S) v
  rw [show (fun z : FiniteStateField S × Records (FiniteStateField S) S
      (finiteCascadeVertexGraft v) =>
      ((z.1,(finiteCascadeGraftRecordExtract v z.2).1),
        (finiteCascadeGraftRecordExtract v z.2).2)) =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id (finiteCascadeGraftRecordExtract v)
      from rfl,
    ←Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap hm),
    ←Measure.compProd_map hm, finiteCascadeVertexGraft_kernel V a ha L v,
    Measure.compProd_assoc]
  rfl

end FourPapersCommon
