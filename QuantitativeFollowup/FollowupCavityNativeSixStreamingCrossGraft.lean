module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingObservationGraft
public import FourPapersCommon.FiniteCascadeCrossContinuationGraft

@[expose] public section

/-! Independent fresh continuations at two arbitrary native ancestral
states are the actual law of an enlarged genealogy, including coincident
vertices, jointly with the complete old record. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
variable {E S A : Type} [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace A]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingContinuationVertexEmbed_state
    (U : (j:ℕ)→FiniteTerminalGenealogy j) {j:ℕ} {T:FiniteTerminalGenealogy j}
    (v w:FiniteCascadeRecordVertex T) (H:E)
    (z:Records E S (finiteCascadeContinuationGraft U v)) :
    nativeStreamingVertexState (finiteCascadeContinuationVertexEmbed U v w) H z=
      nativeStreamingVertexState w H (finiteCascadeContinuationRecords U v z).1 := by
  induction v generalizing H with
  | root T => rfl
  | child v ih =>
      cases w with
      | root T => rfl
      | child w => exact ih w z.1 z.2
  | left v ih =>
      cases w with
      | root T => rfl
      | left w => exact ih w H z.1
      | right w => rfl
  | right v ih =>
      cases w with
      | root T => rfl
      | left w => rfl
      | right w => exact ih w H z.2

def nativeStreamingCrossContinuationKernel (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (E) S (U j)→A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :=
  nativeStreamingContinuationVertexKernel κ θ U extract v ×ₖ nativeStreamingContinuationVertexKernel κ θ U extract w

theorem nativeStreamingCrossContinuationKernel_markov (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (E) S (U j)→A) (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (nativeStreamingCrossContinuationKernel κ hκ θ U extract v w) := by
  haveI:=nativeStreamingContinuationVertexKernel_markov κ hκ θ U extract he v
  haveI:=nativeStreamingContinuationVertexKernel_markov κ hκ θ U extract he w
  unfold nativeStreamingCrossContinuationKernel
  infer_instance

def nativeStreamingCrossContinuationMarkedLaw (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (E) S (U j)→A)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (P : Measure (E×Records (E) S T)) :=
  P ⊗ₘ nativeStreamingCrossContinuationKernel κ hκ θ U extract v w

private theorem measurable_nativeStreaming_cross_mark_inner (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (E) S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (w : FiniteCascadeRecordVertex T)
    (H : E) (G : Records (E) S T × (A × A) → ℝ≥0∞)
    (hG : Measurable G) :
    Measurable (fun z : Records (E) S T × A =>
      ∫⁻τ, G (z.1,(z.2,τ))
        ∂nativeStreamingContinuationKernel κ θ U extract w.depth (nativeStreamingVertexState w H z.1)) := by
  let νMark : Kernel (Records (E) S T × A) A :=
    (nativeStreamingContinuationVertexKernel (S:=S) (E:=E) κ θ U extract w).comap
    (fun z : Records (E) S T × A => (H,z.1))
      (measurable_const.prodMk measurable_fst)
  haveI := nativeStreamingContinuationVertexKernel_markov κ hκ θ U extract he w
  haveI : IsMarkovKernel νMark := inferInstance
  have hm : Measurable (fun z : (Records (E) S T × A) × A =>
      G (z.1.1,(z.1.2,z.2))) := by
    simpa only [Function.comp_def] using hG.comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  convert! hm.lintegral_kernel_prod_right' (κ:=νMark) using 1

theorem lintegral_nativeStreamingCrossObservationGraft (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (E) S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (H : E) (G : Records (E) S T × (A × A) → ℝ≥0∞)
    (hG : Measurable G) :
    (∫⁻z, G (finiteCascadeCrossContinuationExtract U extract v w z)
        ∂observationTreeKernel κ θ (finiteCascadeCrossContinuationGraft U v w) H) =
      ∫⁻z, ∫⁻σ, ∫⁻τ, G (z,(σ,τ))
        ∂nativeStreamingContinuationKernel κ θ U extract w.depth (nativeStreamingVertexState w H z)
        ∂nativeStreamingContinuationKernel κ θ U extract v.depth (nativeStreamingVertexState v H z)
        ∂observationTreeKernel κ θ T H := by
  have hm : Measurable (fun z : Records (E) S
      (finiteCascadeContinuationGraft U v) × A =>
      G ((finiteCascadeContinuationExtract U extract v z.1).1,
        ((finiteCascadeContinuationExtract U extract v z.1).2,z.2))) := by
    have he := (measurable_finiteCascadeContinuationExtract (E:=E) (S:=S) U extract he v).comp
      (measurable_fst : Measurable (Prod.fst :
        Records (E) S (finiteCascadeContinuationGraft U v) × A → _))
    simpa only [Function.comp_def] using hG.comp (he.fst.prodMk (he.snd.prodMk measurable_snd))
  change (∫⁻z, (fun z => G ((finiteCascadeContinuationExtract U extract v z.1).1,
      ((finiteCascadeContinuationExtract U extract v z.1).2,z.2)))
      (finiteCascadeContinuationExtract U extract (finiteCascadeContinuationVertexEmbed U v w) z) ∂_) = _
  rw [lintegral_nativeStreamingObservationGraft κ hκ θ U extract he _ H _ hm]
  simpa only [finiteCascadeContinuationVertexEmbed_depth, nativeStreamingContinuationVertexEmbed_state,
    finiteCascadeContinuationExtract_eq_records] using
    lintegral_nativeStreamingObservationGraft κ hκ θ U extract he v H _
      (measurable_nativeStreaming_cross_mark_inner κ hκ θ U extract he w H G hG)

theorem nativeStreamingCrossObservationGraft_kernel (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (E) S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    (observationTreeKernel κ θ (finiteCascadeCrossContinuationGraft U v w)).map
      (finiteCascadeCrossContinuationExtract U extract v w) =
      observationTreeKernel κ θ T ⊗ₖ nativeStreamingCrossContinuationKernel κ hκ θ U extract v w := by
  haveI := observationTreeKernel_markov κ hκ θ T
  haveI := nativeStreamingCrossContinuationKernel_markov κ hκ θ U extract he v w
  haveI := nativeStreamingContinuationVertexKernel_markov κ hκ θ U extract he v
  haveI := nativeStreamingContinuationVertexKernel_markov κ hκ θ U extract he w
  haveI := nativeStreamingContinuationKernel_markov κ hκ θ U extract he v.depth
  haveI := nativeStreamingContinuationKernel_markov κ hκ θ U extract he w.depth
  ext H : 1
  apply Measure.ext_of_lintegral
  intro G hG
  rw [Kernel.lintegral_map _ (measurable_finiteCascadeCrossContinuationExtract U extract he _ _) _ hG,
    lintegral_nativeStreamingCrossObservationGraft κ hκ θ U extract he v w H G hG,
    Kernel.lintegral_compProd _ _ _ hG]
  apply lintegral_congr
  intro z
  rw [nativeStreamingCrossContinuationKernel, Kernel.prod_apply,
    nativeStreamingContinuationVertexKernel, nativeStreamingContinuationVertexKernel,
    Kernel.comap_apply, Kernel.comap_apply]
  have hm : Measurable (fun c : A × A => G (z,c)) := hG.comp measurable_prodMk_left
  exact (MeasureTheory.lintegral_prod _ hm.aemeasurable).symm


theorem nativeStreamingCrossObservationGraft_joint_law (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ]
    (U : (j : ℕ)→FiniteTerminalGenealogy j)
    (extract : (j : ℕ)→Records (E) S (U j)→A)
    (he : ∀j,Measurable (extract j))
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (μ : Measure (E)) [SFinite μ] :
    (μ ⊗ₘ observationTreeKernel κ θ (finiteCascadeCrossContinuationGraft U v w)).map
      (fun z => ((z.1,(finiteCascadeCrossContinuationExtract U extract v w z.2).1),
        (finiteCascadeCrossContinuationExtract U extract v w z.2).2)) =
      nativeStreamingCrossContinuationMarkedLaw κ hκ θ U extract v w (μ ⊗ₘ observationTreeKernel κ θ T) := by
  haveI := observationTreeKernel_markov κ hκ θ T
  haveI := observationTreeKernel_markov κ hκ θ (finiteCascadeCrossContinuationGraft U v w)
  haveI := nativeStreamingCrossContinuationKernel_markov κ hκ θ U extract he v w
  have hm := measurable_finiteCascadeCrossContinuationExtract (S:=S) (E:=E) U extract he v w
  rw [show (fun z : E × Records (E) S
      (finiteCascadeCrossContinuationGraft U v w) =>
      ((z.1,(finiteCascadeCrossContinuationExtract U extract v w z.2).1),
        (finiteCascadeCrossContinuationExtract U extract v w z.2).2)) =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id (finiteCascadeCrossContinuationExtract U extract v w)
      from rfl,
    ←Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap hm),
    ←Measure.compProd_map hm, nativeStreamingCrossObservationGraft_kernel κ hκ θ U extract he v w,
    Measure.compProd_assoc]
  rfl



end QuantitativeFollowup
