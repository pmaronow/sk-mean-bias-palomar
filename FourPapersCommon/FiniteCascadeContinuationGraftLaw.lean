module
public import FourPapersCommon.FiniteCascadeContinuationGraft
public import FourPapersCommon.FiniteCascadeSingleVertexMarks

@[expose] public section

/-! The explicit graft operation realizes a fresh conditional terminal mark
as an actual enlarged Gaussian tree. No marginal-law premise is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I A : Type} [MeasurableSpace A] [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def finiteCascadeContinuationKernel (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A) (j : ℕ) :=
  (finiteCascadeTreeRecordKernel V a L (U j)).map (extract j)

theorem finiteCascadeContinuationKernel_markov (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0≤a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    (he : ∀j,Measurable (extract j)) (j : ℕ) :
    IsMarkovKernel (finiteCascadeContinuationKernel V a L U extract j) := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (U j)
  exact Kernel.IsMarkovKernel.map _ (he j)

def finiteCascadeContinuationVertexKernel (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :=
  (finiteCascadeContinuationKernel V a L U extract v.depth).comap
    (Function.uncurry (v.field (S:=S))) v.measurable_field

theorem finiteCascadeContinuationVertexKernel_markov (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0≤a j) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (finiteCascadeContinuationVertexKernel V a L U extract v) := by
  haveI := finiteCascadeContinuationKernel_markov V a ha L U extract he v.depth
  unfold finiteCascadeContinuationVertexKernel
  infer_instance

def finiteCascadeContinuationMarkedLaw (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S × Records (FiniteStateField S) S T)) :=
  P ⊗ₘ finiteCascadeContinuationVertexKernel V a L U extract v

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

theorem finiteCascadeContinuationGraft_root_kernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (finiteCascadeTreeRecordKernel V a L (finiteCascadeContinuationGraft U (.root T))).map
      (finiteCascadeContinuationExtract U extract (.root T)) =
      finiteCascadeTreeRecordKernel V a L T ×ₖ finiteCascadeContinuationKernel V a L U extract j := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L
    (U j)
  change (_ ×ₖ _).map (Prod.map id (extract j)) = _
  rw [←Kernel.map_prod_map _ _ measurable_id (he j),
    Kernel.map_id]
  rfl


private theorem measurable_continuation_mark_integral (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (G : Records (FiniteStateField S) S T × A → ℝ≥0∞)
    (hG : Measurable G) :
    Measurable (fun z => ∫⁻σ, G (z,σ)
      ∂finiteCascadeContinuationKernel V a L U extract v.depth (v.field H z)) := by
  let κ := (finiteCascadeContinuationVertexKernel V a L U extract v).comap
    (fun z => (H,z)) (measurable_const.prodMk measurable_id)
  haveI := finiteCascadeContinuationVertexKernel_markov V a ha L U extract he v
  haveI : IsMarkovKernel κ := inferInstance
  convert! hG.lintegral_kernel_prod_right' (κ:=κ) using 1


theorem lintegral_finiteCascadeContinuationGraft (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (G : Records (FiniteStateField S) S T × A → ℝ≥0∞)
    (hG : Measurable G) :
    (∫⁻z, G (finiteCascadeContinuationExtract U extract v z)
        ∂finiteCascadeTreeRecordKernel V a L (finiteCascadeContinuationGraft U v) H) =
      ∫⁻z, ∫⁻σ, G (z,σ)
        ∂finiteCascadeContinuationKernel V a L U extract v.depth (v.field H z)
        ∂finiteCascadeTreeRecordKernel V a L T H := by
  induction v generalizing H with
  | @root j T =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
    haveI := finiteCascadeContinuationKernel_markov V a ha L U extract he j
    rw [←Kernel.lintegral_map _ (measurable_finiteCascadeContinuationExtract U extract he _) _ hG,
      finiteCascadeContinuationGraft_root_kernel V a ha L U extract he,
      Kernel.lintegral_prod _ _ _ hG]
  | @child j T v ih =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeContinuationGraft U v)
    haveI := finiteCascadeContinuationKernel_markov V a ha L U extract he v.depth
    rw [lintegral_record_advance V a ha L _ _ _
      (hG.comp (measurable_finiteCascadeContinuationExtract U extract he _))]
    rw [lintegral_record_advance V a ha L T H _]
    · apply lintegral_congr
      intro Q
      simpa only [finiteCascadeContinuationExtract, FiniteCascadeRecordVertex.depth,
        FiniteCascadeRecordVertex.field] using
        ih Q (fun z => G ((Q,z.1),z.2))
          (hG.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    · exact measurable_continuation_mark_integral V a ha L U extract he (.child v) H G hG
  | @left j T R v ih =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L R
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeContinuationGraft U v)
    haveI := finiteCascadeContinuationKernel_markov V a ha L U extract he v.depth
    change (∫⁻z, G (((finiteCascadeContinuationExtract U extract v z.1).1,z.2),
      (finiteCascadeContinuationExtract U extract v z.1).2) ∂(_ ×ₖ _) H) =
      ∫⁻z, ∫⁻σ, G (z,σ) ∂finiteCascadeContinuationKernel V a L U extract v.depth (v.field H z.1)
        ∂(_ ×ₖ _) H
    have hm : Measurable (fun z : Records (FiniteStateField S) S
        (finiteCascadeContinuationGraft U v) × Records (FiniteStateField S) S R =>
        G (((finiteCascadeContinuationExtract U extract v z.1).1,z.2),
          (finiteCascadeContinuationExtract U extract v z.1).2)) := by
      simpa only [Function.comp_def] using hG.comp
        ((((measurable_finiteCascadeContinuationExtract U extract he v).fst.comp measurable_fst).prodMk
          measurable_snd).prodMk
            ((measurable_finiteCascadeContinuationExtract U extract he v).snd.comp measurable_fst))
    rw [Kernel.lintegral_prod _ _ _ hm]
    rw [ih H (fun z => ∫⁻u, G ((z.1,u),z.2) ∂finiteCascadeTreeRecordKernel V a L R H)
      ((hG.comp ((measurable_fst.comp measurable_fst |>.prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))).lintegral_prod_right')]
    rw [Kernel.lintegral_prod _ _ _]
    · apply lintegral_congr
      intro z
      exact MeasureTheory.lintegral_lintegral_swap
        (hG.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aemeasurable
    · exact measurable_continuation_mark_integral V a ha L U extract he (.left v) H G hG
  | @right j T R v ih =>
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L R
    haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeContinuationGraft U v)
    haveI := finiteCascadeContinuationKernel_markov V a ha L U extract he v.depth
    change (∫⁻z, G ((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
      (finiteCascadeContinuationExtract U extract v z.2).2) ∂(_ ×ₖ _) H) =
      ∫⁻z, ∫⁻σ, G (z,σ) ∂finiteCascadeContinuationKernel V a L U extract v.depth (v.field H z.2)
        ∂(_ ×ₖ _) H
    have hm : Measurable (fun z : Records (FiniteStateField S) S T ×
        Records (FiniteStateField S) S (finiteCascadeContinuationGraft U v) =>
        G ((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
          (finiteCascadeContinuationExtract U extract v z.2).2)) := by
      simpa only [Function.comp_def] using hG.comp
        ((measurable_fst.prodMk ((measurable_finiteCascadeContinuationExtract U extract he v).fst.comp
          measurable_snd)).prodMk
            ((measurable_finiteCascadeContinuationExtract U extract he v).snd.comp measurable_snd))
    rw [Kernel.lintegral_prod _ _ _ hm]
    rw [Kernel.lintegral_prod _ _ _]
    · apply lintegral_congr
      intro z
      exact ih H (fun u => G ((z,u.1),u.2))
        (hG.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    · exact measurable_continuation_mark_integral V a ha L U extract he (.right v) H G hG


theorem finiteCascadeContinuationGraft_kernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    (finiteCascadeTreeRecordKernel V a L (finiteCascadeContinuationGraft U v)).map
      (finiteCascadeContinuationExtract U extract v) =
      finiteCascadeTreeRecordKernel V a L T ⊗ₖ finiteCascadeContinuationVertexKernel V a L U extract v := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := finiteCascadeContinuationVertexKernel_markov V a ha L U extract he v
  ext H : 1
  apply Measure.ext_of_lintegral
  intro G hG
  rw [Kernel.lintegral_map _ (measurable_finiteCascadeContinuationExtract U extract he _) _ hG,
    lintegral_finiteCascadeContinuationGraft V a ha L U extract he v H G hG,
    Kernel.lintegral_compProd _ _ _ hG]
  rfl

theorem finiteCascadeContinuationGraft_joint_law (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (FiniteStateField S) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (μ : Measure (FiniteStateField S)) [SFinite μ] :
    (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L (finiteCascadeContinuationGraft U v)).map
      (fun z => ((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
        (finiteCascadeContinuationExtract U extract v z.2).2)) =
      finiteCascadeContinuationMarkedLaw V a L U extract v (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L T) := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeContinuationGraft U v)
  haveI := finiteCascadeContinuationVertexKernel_markov V a ha L U extract he v
  have hm := measurable_finiteCascadeContinuationExtract (S:=S) (E:=FiniteStateField S) U extract he v
  rw [show (fun z : FiniteStateField S × Records (FiniteStateField S) S
      (finiteCascadeContinuationGraft U v) =>
      ((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
        (finiteCascadeContinuationExtract U extract v z.2).2)) =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id (finiteCascadeContinuationExtract U extract v)
      from rfl,
    ←Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap hm),
    ←Measure.compProd_map hm, finiteCascadeContinuationGraft_kernel V a ha L U extract he v,
    Measure.compProd_assoc]
  rfl

end FourPapersCommon
