module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairObservedKernel

@[expose] public section

/-! The ancestral observation kernels are genuine probability kernels.
Their sequential and branch products use the actual native transitions;
all record-selection maps are measurable. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 instance nativeStreamingEdgeObservedKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (e : NativeStreamingEdge T) (r : Paper.Overlap) :
    IsMarkovKernel (nativeStreamingEdgeObservedKernel D μ q T e r) := by
  induction e with
  | here T =>
      dsimp only [nativeStreamingEdgeObservedKernel]
      infer_instance
  | child e ih =>
      haveI := ih
      dsimp only [nativeStreamingEdgeObservedKernel]
      exact Kernel.IsMarkovKernel.map _
        (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
  | left e ih =>
      haveI := ih
      dsimp only [nativeStreamingEdgeObservedKernel]
      exact Kernel.IsMarkovKernel.map _
        (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  | right e ih =>
      haveI := ih
      dsimp only [nativeStreamingEdgeObservedKernel]
      exact Kernel.IsMarkovKernel.map _
        (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))

 instance nativeStreamingEdgePairObservedKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (order : Ordering)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (e f : NativeStreamingEdge T) (r l : Paper.Overlap) :
    IsMarkovKernel (nativeStreamingEdgePairObservedKernel D μ q order T e f r l) := by
  induction T with
  | leaf => cases e
  | @advance j T ih =>
      cases e with
      | here =>
          cases f with
          | here =>
              cases order with
              | eq =>
                  exact Kernel.IsMarkovKernel.map _
                    (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd))
              | lt =>
                  exact Kernel.IsMarkovKernel.map _
                    (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
              | gt =>
                  change IsMarkovKernel ((Kernel.id ×ₖ ((Kernel.id ×ₖ
                    ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
                      anisotropicObservationTransition D μ l (q j))) ∘ₖ
                        anisotropicObservationTransition D μ r l)) ∘ₖ
                          anisotropicObservationTransition D μ (q (j+1)) r)
                  infer_instance
          | child f =>
              exact Kernel.IsMarkovKernel.map _
                (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk
                  (measurable_snd.fst.prodMk measurable_snd.snd.snd)))
      | child e =>
          cases f with
          | here =>
              exact Kernel.IsMarkovKernel.map _
                (measurable_snd.snd.fst.prodMk (measurable_fst.prodMk
                  (measurable_snd.fst.prodMk measurable_snd.snd.snd)))
          | child f =>
              haveI := ih e f
              exact Kernel.IsMarkovKernel.map _
                (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk
                  (measurable_fst.prodMk measurable_snd.snd.snd)))
  | fork T U ihT ihU =>
      cases e with
      | left e =>
          cases f with
          | left f =>
              haveI := ihT e f
              exact Kernel.IsMarkovKernel.map _
                (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
                  (measurable_fst.snd.snd.prodMk measurable_snd)))
          | right f =>
              exact Kernel.IsMarkovKernel.map _
                (measurable_fst.fst.prodMk (measurable_snd.fst.prodMk
                  (measurable_fst.snd.prodMk measurable_snd.snd)))
      | right e =>
          cases f with
          | left f =>
              exact Kernel.IsMarkovKernel.map _
                (measurable_snd.fst.prodMk (measurable_fst.fst.prodMk
                  (measurable_fst.snd.prodMk measurable_snd.snd)))
          | right f =>
              haveI := ihU e f
              exact Kernel.IsMarkovKernel.map _
                (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk
                  (measurable_fst.prodMk measurable_snd.snd.snd)))

end QuantitativeFollowup
