module
public import FourPapersCommon.FiniteCascadeContinuationVertexGeometry
public import FourPapersCommon.FiniteCascadeGaussianContinuationGraft

@[expose] public section

/-! Two genuine independent continuation marks at arbitrary vertices,
including coincident vertices, are realized by an actual enlarged tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def finiteCascadeCrossContinuationGraft (U : (j : ℕ)→FiniteTerminalGenealogy j)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) : FiniteTerminalGenealogy j :=
  finiteCascadeContinuationGraft U (finiteCascadeContinuationVertexEmbed U v w)

@[reducible] def finiteCascadeCrossContinuationExtract {E S A : Type}
    (U : (j : ℕ)→FiniteTerminalGenealogy j) (extract : (j : ℕ)→Records E S (U j)→A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossContinuationGraft U v w)) : Records E S T×(A×A) :=
  let z':=finiteCascadeContinuationExtract U extract (finiteCascadeContinuationVertexEmbed U v w) z
  let z'':=finiteCascadeContinuationExtract U extract v z'.1
  (z''.1,(z''.2,z'.2))

theorem measurable_finiteCascadeCrossContinuationExtract {E S A : Type}
    [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace A]
    (U : (j : ℕ)→FiniteTerminalGenealogy j) (extract : (j : ℕ)→Records E S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    Measurable (finiteCascadeCrossContinuationExtract U extract v w) := by
  have h1:=measurable_finiteCascadeContinuationExtract U extract he (finiteCascadeContinuationVertexEmbed U v w)
  have h2:=(measurable_finiteCascadeContinuationExtract U extract he v).comp h1.fst
  exact h2.fst.prodMk (h2.snd.prodMk h1.snd)

variable {S I A : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S] [MeasurableSpace A]

private theorem finiteCascadeContinuationVertexEmbed_field_extract
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (FiniteStateField S) S (U j)→A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (z : Records (FiniteStateField S) S (finiteCascadeContinuationGraft U v)) :
    (finiteCascadeContinuationVertexEmbed U v w).field H z=w.field H (finiteCascadeContinuationExtract U extract v z).1 := by
  rw [finiteCascadeContinuationVertexEmbed_field,finiteCascadeContinuationExtract_eq_records]

def finiteCascadeCrossContinuationKernel (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (FiniteStateField S) S (U j)→A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :=
  finiteCascadeContinuationVertexKernel V a L U extract v ×ₖ finiteCascadeContinuationVertexKernel V a L U extract w

theorem finiteCascadeCrossContinuationKernel_markov (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (FiniteStateField S) S (U j)→A) (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (finiteCascadeCrossContinuationKernel V a L U extract v w) := by
  haveI:=finiteCascadeContinuationVertexKernel_markov V a ha L U extract he v
  haveI:=finiteCascadeContinuationVertexKernel_markov V a ha L U extract he w
  unfold finiteCascadeCrossContinuationKernel
  infer_instance

def finiteCascadeCrossContinuationMarkedLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (FiniteStateField S) S (U j)→A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (P : Measure (FiniteStateField S×Records (FiniteStateField S) S T)) :=
  P ⊗ₘ finiteCascadeCrossContinuationKernel V a L U extract v w

private theorem measurable_cross_mark_inner (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (FiniteStateField S) S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (w : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (G : Records (FiniteStateField S) S T × (A × A) → ℝ≥0∞)
    (hG : Measurable G) :
    Measurable (fun z : Records (FiniteStateField S) S T × A =>
      ∫⁻τ, G (z.1,(z.2,τ))
        ∂finiteCascadeContinuationKernel V a L U extract w.depth (w.field H z.1)) := by
  let κ : Kernel (Records (FiniteStateField S) S T × A) A :=
    (finiteCascadeContinuationVertexKernel (S:=S) (I:=I) V a L U extract w).comap
    (fun z : Records (FiniteStateField S) S T × A => (H,z.1))
      (measurable_const.prodMk measurable_fst)
  haveI := finiteCascadeContinuationVertexKernel_markov V a ha L U extract he w
  haveI : IsMarkovKernel κ := inferInstance
  have hm : Measurable (fun z : (Records (FiniteStateField S) S T × A) × A =>
      G (z.1.1,(z.1.2,z.2))) := by
    simpa only [Function.comp_def] using hG.comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  convert! hm.lintegral_kernel_prod_right' (κ:=κ) using 1

theorem lintegral_finiteCascadeCrossContinuationGraft (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (FiniteStateField S) S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (G : Records (FiniteStateField S) S T × (A × A) → ℝ≥0∞)
    (hG : Measurable G) :
    (∫⁻z, G (finiteCascadeCrossContinuationExtract U extract v w z)
        ∂finiteCascadeTreeRecordKernel V a L (finiteCascadeCrossContinuationGraft U v w) H) =
      ∫⁻z, ∫⁻σ, ∫⁻τ, G (z,(σ,τ))
        ∂finiteCascadeContinuationKernel V a L U extract w.depth (w.field H z)
        ∂finiteCascadeContinuationKernel V a L U extract v.depth (v.field H z)
        ∂finiteCascadeTreeRecordKernel V a L T H := by
  have hm : Measurable (fun z : Records (FiniteStateField S) S
      (finiteCascadeContinuationGraft U v) × A =>
      G ((finiteCascadeContinuationExtract U extract v z.1).1,
        ((finiteCascadeContinuationExtract U extract v z.1).2,z.2))) := by
    have he := (measurable_finiteCascadeContinuationExtract (E:=FiniteStateField S) (S:=S) U extract he v).comp
      (measurable_fst : Measurable (Prod.fst :
        Records (FiniteStateField S) S (finiteCascadeContinuationGraft U v) × A → _))
    simpa only [Function.comp_def] using hG.comp (he.fst.prodMk (he.snd.prodMk measurable_snd))
  change (∫⁻z, (fun z => G ((finiteCascadeContinuationExtract U extract v z.1).1,
      ((finiteCascadeContinuationExtract U extract v z.1).2,z.2)))
      (finiteCascadeContinuationExtract U extract (finiteCascadeContinuationVertexEmbed U v w) z) ∂_) = _
  rw [lintegral_finiteCascadeContinuationGraft V a ha L U extract he _ H _ hm]
  simpa only [finiteCascadeContinuationVertexEmbed_depth, finiteCascadeContinuationVertexEmbed_field,
    finiteCascadeContinuationExtract_eq_records] using
    lintegral_finiteCascadeContinuationGraft V a ha L U extract he v H _
      (measurable_cross_mark_inner V a ha L U extract he w H G hG)

theorem finiteCascadeCrossContinuationGraft_kernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (FiniteStateField S) S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    (finiteCascadeTreeRecordKernel V a L (finiteCascadeCrossContinuationGraft U v w)).map
      (finiteCascadeCrossContinuationExtract U extract v w) =
      finiteCascadeTreeRecordKernel V a L T ⊗ₖ finiteCascadeCrossContinuationKernel V a L U extract v w := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := finiteCascadeCrossContinuationKernel_markov V a ha L U extract he v w
  haveI := finiteCascadeContinuationVertexKernel_markov V a ha L U extract he v
  haveI := finiteCascadeContinuationVertexKernel_markov V a ha L U extract he w
  haveI := finiteCascadeContinuationKernel_markov V a ha L U extract he v.depth
  haveI := finiteCascadeContinuationKernel_markov V a ha L U extract he w.depth
  ext H : 1
  apply Measure.ext_of_lintegral
  intro G hG
  rw [Kernel.lintegral_map _ (measurable_finiteCascadeCrossContinuationExtract U extract he _ _) _ hG,
    lintegral_finiteCascadeCrossContinuationGraft V a ha L U extract he v w H G hG,
    Kernel.lintegral_compProd _ _ _ hG]
  apply lintegral_congr
  intro z
  rw [finiteCascadeCrossContinuationKernel, Kernel.prod_apply,
    finiteCascadeContinuationVertexKernel, finiteCascadeContinuationVertexKernel,
    Kernel.comap_apply, Kernel.comap_apply]
  have hm : Measurable (fun c : A × A => G (z,c)) := hG.comp measurable_prodMk_left
  exact (MeasureTheory.lintegral_prod _ hm.aemeasurable).symm


theorem finiteCascadeCrossContinuationGraft_joint_law (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (FiniteStateField S) S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (μ : Measure (FiniteStateField S)) [SFinite μ] :
    (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L (finiteCascadeCrossContinuationGraft U v w)).map
      (fun z => ((z.1,(finiteCascadeCrossContinuationExtract U extract v w z.2).1),
        (finiteCascadeCrossContinuationExtract U extract v w z.2).2)) =
      finiteCascadeCrossContinuationMarkedLaw V a L U extract v w (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L T) := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeCrossContinuationGraft U v w)
  haveI := finiteCascadeCrossContinuationKernel_markov V a ha L U extract he v w
  have hm := measurable_finiteCascadeCrossContinuationExtract (S:=S) (E:=FiniteStateField S) U extract he v w
  rw [show (fun z : FiniteStateField S × Records (FiniteStateField S) S
      (finiteCascadeCrossContinuationGraft U v w) =>
      ((z.1,(finiteCascadeCrossContinuationExtract U extract v w z.2).1),
        (finiteCascadeCrossContinuationExtract U extract v w z.2).2)) =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id (finiteCascadeCrossContinuationExtract U extract v w)
      from rfl,
    ←Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap hm),
    ←Measure.compProd_map hm, finiteCascadeCrossContinuationGraft_kernel V a ha L U extract he v w,
    Measure.compProd_assoc]
  rfl


end FourPapersCommon
