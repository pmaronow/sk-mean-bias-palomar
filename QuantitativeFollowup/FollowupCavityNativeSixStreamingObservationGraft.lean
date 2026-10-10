module
public import FourPapersCommon.FiniteCascadeContinuationGraftLaw
public import FourPapersCommon.FiniteObservationTreeTopology

@[expose] public section

/-! Generic normalized observation kernels, including genuine native
Picard transitions, realize a conditional fresh continuation by an actual
graft. The complete original record is retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
variable {E S A : Type} [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace A]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeStreamingVertexState : {j : ℕ} → {T : FiniteTerminalGenealogy j} →
    FiniteCascadeRecordVertex T → E → Records E S T → E
  | _, _, .root _ => fun H _ => H
  | _, _, .child v => fun _ z => nativeStreamingVertexState v z.1 z.2
  | _, _, .left v => fun H z => nativeStreamingVertexState v H z.1
  | _, _, .right v => fun H z => nativeStreamingVertexState v H z.2

theorem nativeStreamingVertexState_measurable {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) :
    Measurable (Function.uncurry (nativeStreamingVertexState (E:=E) (S:=S) v)) := by
  induction v with
  | root T => exact measurable_fst
  | child v ih => exact ih.comp measurable_snd
  | left v ih => exact ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  | right v ih => exact ih.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

theorem nativeStreamingContinuationExtract_continuous
    [TopologicalSpace E] [TopologicalSpace S] [TopologicalSpace A]
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records E S (U j)→A) (he : ∀j,Continuous (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    Continuous (finiteCascadeContinuationExtract U extract v) := by
  induction v with
  | root T => exact continuous_fst.prodMk ((he _).comp continuous_snd)
  | child v ih =>
      exact (continuous_fst.prodMk (ih.fst.comp continuous_snd)).prodMk (ih.snd.comp continuous_snd)
  | left v ih =>
      exact ((ih.fst.comp continuous_fst).prodMk continuous_snd).prodMk (ih.snd.comp continuous_fst)
  | right v ih =>
      exact (continuous_fst.prodMk (ih.fst.comp continuous_snd)).prodMk (ih.snd.comp continuous_snd)

def nativeStreamingContinuationKernel (κ : ℕ → Kernel E E) (θ : Kernel E S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A) (j : ℕ) :=
  (observationTreeKernel κ θ (U j)).map (extract j)

theorem nativeStreamingContinuationKernel_markov (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A)
    (he : ∀j,Measurable (extract j)) (j : ℕ) :
    IsMarkovKernel (nativeStreamingContinuationKernel κ θ U extract j) := by
  haveI := observationTreeKernel_markov κ hκ θ (U j)
  exact Kernel.IsMarkovKernel.map _ (he j)

def nativeStreamingContinuationVertexKernel (κ : ℕ → Kernel E E) (θ : Kernel E S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    Kernel (E×Records E S T) A :=
  (nativeStreamingContinuationKernel κ θ U extract v.depth).comap
    (Function.uncurry (nativeStreamingVertexState (E:=E) (S:=S) v))
      (nativeStreamingVertexState_measurable v)

theorem nativeStreamingContinuationVertexKernel_markov (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (nativeStreamingContinuationVertexKernel κ θ U extract v) := by
  haveI := nativeStreamingContinuationKernel_markov κ hκ θ U extract he v.depth
  unfold nativeStreamingContinuationVertexKernel
  infer_instance

def nativeStreamingContinuationMarkedLaw (κ : ℕ → Kernel E E) (θ : Kernel E S)
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (P : Measure (E × Records (E) S T)) :=
  P ⊗ₘ nativeStreamingContinuationVertexKernel κ θ U extract v

private theorem lintegral_record_advance (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : E)
    (G : Records (E) S (.advance T) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻z, G z ∂observationTreeKernel κ θ (.advance T) H) =
      ∫⁻Q, ∫⁻z, G (Q,z) ∂observationTreeKernel κ θ T Q
        ∂κ j H := by
  haveI := observationTreeKernel_markov κ hκ θ T
  haveI : IsMarkovKernel (κ j) := hκ j
  change (∫⁻z, G z ∂((_ ×ₖ _) ∘ₖ _) H) = _
  rw [Kernel.lintegral_comp _ _ _ hG]
  apply lintegral_congr
  intro Q
  exact Kernel.lintegral_id_prod hG _ Q

theorem nativeStreamingObservationGraft_root_kernel (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (observationTreeKernel κ θ (finiteCascadeContinuationGraft U (.root T))).map
      (finiteCascadeContinuationExtract U extract (.root T)) =
      observationTreeKernel κ θ T ×ₖ nativeStreamingContinuationKernel κ θ U extract j := by
  haveI := observationTreeKernel_markov κ hκ θ T
  haveI := observationTreeKernel_markov κ hκ θ
    (U j)
  change (_ ×ₖ _).map (Prod.map id (extract j)) = _
  rw [←Kernel.map_prod_map _ _ measurable_id (he j),
    Kernel.map_id]
  rfl


private theorem measurable_continuation_mark_integral (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (H : E) (G : Records (E) S T × A → ℝ≥0∞)
    (hG : Measurable G) :
    Measurable (fun z => ∫⁻σ, G (z,σ)
      ∂nativeStreamingContinuationKernel κ θ U extract v.depth (nativeStreamingVertexState v H z)) := by
  let νMark := (nativeStreamingContinuationVertexKernel κ θ U extract v).comap
    (fun z => (H,z)) (measurable_const.prodMk measurable_id)
  haveI := nativeStreamingContinuationVertexKernel_markov κ hκ θ U extract he v
  haveI : IsMarkovKernel νMark := inferInstance
  convert! hG.lintegral_kernel_prod_right' (κ:=νMark) using 1


theorem lintegral_nativeStreamingObservationGraft (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (H : E) (G : Records (E) S T × A → ℝ≥0∞)
    (hG : Measurable G) :
    (∫⁻z, G (finiteCascadeContinuationExtract U extract v z)
        ∂observationTreeKernel κ θ (finiteCascadeContinuationGraft U v) H) =
      ∫⁻z, ∫⁻σ, G (z,σ)
        ∂nativeStreamingContinuationKernel κ θ U extract v.depth (nativeStreamingVertexState v H z)
        ∂observationTreeKernel κ θ T H := by
  induction v generalizing H with
  | @root j T =>
    haveI := observationTreeKernel_markov κ hκ θ T
    haveI := nativeStreamingContinuationKernel_markov κ hκ θ U extract he j
    rw [←Kernel.lintegral_map _ (measurable_finiteCascadeContinuationExtract U extract he _) _ hG,
      nativeStreamingObservationGraft_root_kernel κ hκ θ U extract he,
      Kernel.lintegral_prod _ _ _ hG]
  | @child j T v ih =>
    haveI := observationTreeKernel_markov κ hκ θ T
    haveI := observationTreeKernel_markov κ hκ θ (finiteCascadeContinuationGraft U v)
    haveI := nativeStreamingContinuationKernel_markov κ hκ θ U extract he v.depth
    rw [lintegral_record_advance κ hκ θ _ _ _
      (hG.comp (measurable_finiteCascadeContinuationExtract U extract he _))]
    rw [lintegral_record_advance κ hκ θ T H _]
    · apply lintegral_congr
      intro Q
      simpa only [finiteCascadeContinuationExtract, FiniteCascadeRecordVertex.depth,
        nativeStreamingVertexState] using
        ih Q (fun z => G ((Q,z.1),z.2))
          (hG.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    · exact measurable_continuation_mark_integral κ hκ θ U extract he (.child v) H G hG
  | @left j T R v ih =>
    haveI := observationTreeKernel_markov κ hκ θ T
    haveI := observationTreeKernel_markov κ hκ θ R
    haveI := observationTreeKernel_markov κ hκ θ (finiteCascadeContinuationGraft U v)
    haveI := nativeStreamingContinuationKernel_markov κ hκ θ U extract he v.depth
    change (∫⁻z, G (((finiteCascadeContinuationExtract U extract v z.1).1,z.2),
      (finiteCascadeContinuationExtract U extract v z.1).2) ∂(_ ×ₖ _) H) =
      ∫⁻z, ∫⁻σ, G (z,σ) ∂nativeStreamingContinuationKernel κ θ U extract v.depth (nativeStreamingVertexState v H z.1)
        ∂(_ ×ₖ _) H
    have hm : Measurable (fun z : Records (E) S
        (finiteCascadeContinuationGraft U v) × Records (E) S R =>
        G (((finiteCascadeContinuationExtract U extract v z.1).1,z.2),
          (finiteCascadeContinuationExtract U extract v z.1).2)) := by
      simpa only [Function.comp_def] using hG.comp
        ((((measurable_finiteCascadeContinuationExtract U extract he v).fst.comp measurable_fst).prodMk
          measurable_snd).prodMk
            ((measurable_finiteCascadeContinuationExtract U extract he v).snd.comp measurable_fst))
    rw [Kernel.lintegral_prod _ _ _ hm]
    rw [ih H (fun z => ∫⁻u, G ((z.1,u),z.2) ∂observationTreeKernel κ θ R H)
      ((hG.comp ((measurable_fst.comp measurable_fst |>.prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))).lintegral_prod_right')]
    rw [Kernel.lintegral_prod _ _ _]
    · apply lintegral_congr
      intro z
      exact MeasureTheory.lintegral_lintegral_swap
        (hG.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aemeasurable
    · exact measurable_continuation_mark_integral κ hκ θ U extract he (.left v) H G hG
  | @right j T R v ih =>
    haveI := observationTreeKernel_markov κ hκ θ T
    haveI := observationTreeKernel_markov κ hκ θ R
    haveI := observationTreeKernel_markov κ hκ θ (finiteCascadeContinuationGraft U v)
    haveI := nativeStreamingContinuationKernel_markov κ hκ θ U extract he v.depth
    change (∫⁻z, G ((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
      (finiteCascadeContinuationExtract U extract v z.2).2) ∂(_ ×ₖ _) H) =
      ∫⁻z, ∫⁻σ, G (z,σ) ∂nativeStreamingContinuationKernel κ θ U extract v.depth (nativeStreamingVertexState v H z.2)
        ∂(_ ×ₖ _) H
    have hm : Measurable (fun z : Records (E) S T ×
        Records (E) S (finiteCascadeContinuationGraft U v) =>
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
    · exact measurable_continuation_mark_integral κ hκ θ U extract he (.right v) H G hG


theorem nativeStreamingObservationGraft_kernel (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    (observationTreeKernel κ θ (finiteCascadeContinuationGraft U v)).map
      (finiteCascadeContinuationExtract U extract v) =
      observationTreeKernel κ θ T ⊗ₖ nativeStreamingContinuationVertexKernel κ θ U extract v := by
  haveI := observationTreeKernel_markov κ hκ θ T
  haveI := nativeStreamingContinuationVertexKernel_markov κ hκ θ U extract he v
  ext H : 1
  apply Measure.ext_of_lintegral
  intro G hG
  rw [Kernel.lintegral_map _ (measurable_finiteCascadeContinuationExtract U extract he _) _ hG,
    lintegral_nativeStreamingObservationGraft κ hκ θ U extract he v H G hG,
    Kernel.lintegral_compProd _ _ _ hG]
  rfl

theorem nativeStreamingObservationGraft_joint_law (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (E) S (U j) → A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T)
    (μ : Measure (E)) [SFinite μ] :
    (μ ⊗ₘ observationTreeKernel κ θ (finiteCascadeContinuationGraft U v)).map
      (fun z => ((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
        (finiteCascadeContinuationExtract U extract v z.2).2)) =
      nativeStreamingContinuationMarkedLaw κ θ U extract v (μ ⊗ₘ observationTreeKernel κ θ T) := by
  haveI := observationTreeKernel_markov κ hκ θ T
  haveI := observationTreeKernel_markov κ hκ θ (finiteCascadeContinuationGraft U v)
  haveI := nativeStreamingContinuationVertexKernel_markov κ hκ θ U extract he v
  have hm := measurable_finiteCascadeContinuationExtract (S:=S) (E:=E) U extract he v
  rw [show (fun z : E × Records (E) S
      (finiteCascadeContinuationGraft U v) =>
      ((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
        (finiteCascadeContinuationExtract U extract v z.2).2)) =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id (finiteCascadeContinuationExtract U extract v)
      from rfl,
    ←Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap hm),
    ←Measure.compProd_map hm, nativeStreamingObservationGraft_kernel κ hκ θ U extract he v,
    Measure.compProd_assoc]
  rfl


end QuantitativeFollowup
