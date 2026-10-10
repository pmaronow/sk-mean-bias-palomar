module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairKernelOrder

@[expose] public section

/-! Equal physical times share the actual same ancestral state, even when
the observation mesh contains several distinct indices at that time.
The zero-time native transition is the proved identity kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreaming_id_prod_duplicate {E S : Type*}
    [MeasurableSpace E] [MeasurableSpace S] (K : Kernel E S) [IsSFiniteKernel K] :
    Kernel.id ×ₖ (Kernel.id ×ₖ K)=
      (Kernel.id ×ₖ K).map (fun z=>(z.1,(z.1,z.2))) := by
  ext z u hu
  rw [Kernel.id_prod_apply' _ z hu,
    Kernel.id_prod_apply' _ z (hu.preimage measurable_prodMk_left),
    Kernel.map_apply' _
      (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd)) z hu,
    Kernel.id_prod_apply' _ z
      (hu.preimage (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd)))]
  rfl

theorem nativeStreamingSameEdgeObservedKernel_equalTime (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (o : Ordering) (r : Paper.Overlap) :
    nativeStreamingEdgePairObservedKernel D μ q o (.advance T) (.here T) (.here T) r r=
      (nativeStreamingEdgeObservedKernel D μ q (.advance T) (.here T) r).map
        (fun z=>(z.1,(z.1,z.2))) := by
  cases o with
  | eq => rfl
  | gt =>
      change (Kernel.id ×ₖ ((Kernel.id ×ₖ
          ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
            anisotropicObservationTransition D μ r (q j))) ∘ₖ
              anisotropicObservationTransition D μ r r)) ∘ₖ
                anisotropicObservationTransition D μ (q (j+1)) r=_
      rw [anisotropicObservationTransition_same_time,Kernel.comp_id,
        nativeStreaming_id_prod_duplicate,←Kernel.map_comp]
  | lt =>
      change ((Kernel.id ×ₖ ((Kernel.id ×ₖ
          ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
            anisotropicObservationTransition D μ r (q j))) ∘ₖ
              anisotropicObservationTransition D μ r r)) ∘ₖ
                anisotropicObservationTransition D μ (q (j+1)) r).map
                  (fun z=>(z.2.1,(z.1,z.2.2)))=_
      rw [anisotropicObservationTransition_same_time,Kernel.comp_id,
        nativeStreaming_id_prod_duplicate,←Kernel.map_comp,
        ←Kernel.map_comp_right _
          (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd))
          (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))]
      rfl

theorem nativeStreamingEdgePairObservedKernel_order_equal_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (o₁ o₂ : Ordering)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (e f : NativeStreamingEdge T)
    (r : Paper.Overlap) :
    nativeStreamingEdgePairObservedKernel D μ q o₁ T e f r r=
      nativeStreamingEdgePairObservedKernel D μ q o₂ T e f r r := by
  by_cases he : e=f
  · subst f
    induction e with
    | here T =>
        rw [nativeStreamingSameEdgeObservedKernel_equalTime,
          nativeStreamingSameEdgeObservedKernel_equalTime]
    | @child j T e ih =>
        change ((Kernel.id ×ₖ nativeStreamingEdgePairObservedKernel D μ q o₁ T e e r r) ∘ₖ
            anisotropicObservationTransition D μ (q (j+1)) (q j)).map _=
          ((Kernel.id ×ₖ nativeStreamingEdgePairObservedKernel D μ q o₂ T e e r r) ∘ₖ
            anisotropicObservationTransition D μ (q (j+1)) (q j)).map _
        rw [ih]
    | @left j T U e ih =>
        change (nativeStreamingEdgePairObservedKernel D μ q o₁ T e e r r ×ₖ
          anisotropicRecordedProfileTreeKernel D μ q U).map _=
          (nativeStreamingEdgePairObservedKernel D μ q o₂ T e e r r ×ₖ
            anisotropicRecordedProfileTreeKernel D μ q U).map _
        rw [ih]
    | @right j T U e ih =>
        change (anisotropicRecordedProfileTreeKernel D μ q T ×ₖ
          nativeStreamingEdgePairObservedKernel D μ q o₁ U e e r r).map _=
          (anisotropicRecordedProfileTreeKernel D μ q T ×ₖ
            nativeStreamingEdgePairObservedKernel D μ q o₂ U e e r r).map _
        rw [ih]
  · exact nativeStreamingEdgePairObservedKernel_order_independent D μ q o₁ o₂ T e f he r r

end QuantitativeFollowup
