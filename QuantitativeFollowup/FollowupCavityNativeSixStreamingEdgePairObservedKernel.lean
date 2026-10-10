module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedLaw

@[expose] public section

/-! The native joint law of two selected ancestral fields and every old
record. Two fields on the same edge use successive restart transitions;
fields in different branches use the true conditional branch product. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeStreamingEdgePairObservedKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) (order : Ordering) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → NativeStreamingEdge T → NativeStreamingEdge T →
      Paper.Overlap → Paper.Overlap → Kernel (AnisotropicObservationState n)
        (AnisotropicObservationState n × (AnisotropicObservationState n ×
          Records (AnisotropicObservationState n) (Configuration n) T))
  | _, @FiniteTerminalGenealogy.advance j T, .here _, .here _, r, l =>
      match order with
      | .eq => (nativeStreamingEdgeObservedKernel D μ q (.advance T) (.here T) r).map
          (fun z=> (z.1,(z.1,z.2)))
      | .lt => ((Kernel.id ×ₖ ((Kernel.id ×ₖ
          ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
            anisotropicObservationTransition D μ r (q j))) ∘ₖ
              anisotropicObservationTransition D μ l r)) ∘ₖ
                anisotropicObservationTransition D μ (q (j+1)) l).map
                  (fun z=> (z.2.1,(z.1,z.2.2)))
      | .gt => (Kernel.id ×ₖ ((Kernel.id ×ₖ
          ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
            anisotropicObservationTransition D μ l (q j))) ∘ₖ
              anisotropicObservationTransition D μ r l)) ∘ₖ
                anisotropicObservationTransition D μ (q (j+1)) r
  | _, @FiniteTerminalGenealogy.advance j T, .here _, .child f, r, l =>
      ((Kernel.id ×ₖ ((Kernel.id ×ₖ nativeStreamingEdgeObservedKernel D μ q T f l) ∘ₖ
        anisotropicObservationTransition D μ r (q j))) ∘ₖ
          anisotropicObservationTransition D μ (q (j+1)) r).map
            (fun z=> (z.1,(z.2.2.1,(z.2.1,z.2.2.2))))
  | _, @FiniteTerminalGenealogy.advance j T, .child e, .here _, r, l =>
      ((Kernel.id ×ₖ ((Kernel.id ×ₖ nativeStreamingEdgeObservedKernel D μ q T e r) ∘ₖ
        anisotropicObservationTransition D μ l (q j))) ∘ₖ
          anisotropicObservationTransition D μ (q (j+1)) l).map
            (fun z=> (z.2.2.1,(z.1,(z.2.1,z.2.2.2))))
  | _, @FiniteTerminalGenealogy.advance j T, .child e, .child f, r, l =>
      ((Kernel.id ×ₖ nativeStreamingEdgePairObservedKernel D μ q order T e f r l) ∘ₖ
        anisotropicObservationTransition D μ (q (j+1)) (q j)).map
          (fun z=> (z.2.1,(z.2.2.1,(z.1,z.2.2.2))))
  | _, @FiniteTerminalGenealogy.fork j T U, .left e, .left f, r, l =>
      (nativeStreamingEdgePairObservedKernel D μ q order T e f r l ×ₖ
        anisotropicRecordedProfileTreeKernel D μ q U).map
          (fun z=> (z.1.1,(z.1.2.1,(z.1.2.2,z.2))))
  | _, @FiniteTerminalGenealogy.fork j T U, .right e, .right f, r, l =>
      (anisotropicRecordedProfileTreeKernel D μ q T ×ₖ
        nativeStreamingEdgePairObservedKernel D μ q order U e f r l).map
          (fun z=> (z.2.1,(z.2.2.1,(z.1,z.2.2.2))))
  | _, @FiniteTerminalGenealogy.fork j T U, .left e, .right f, r, l =>
      (nativeStreamingEdgeObservedKernel D μ q T e r ×ₖ
        nativeStreamingEdgeObservedKernel D μ q U f l).map
          (fun z=> (z.1.1,(z.2.1,(z.1.2,z.2.2))))
  | _, @FiniteTerminalGenealogy.fork j T U, .right e, .left f, r, l =>
      (nativeStreamingEdgeObservedKernel D μ q T f l ×ₖ
        nativeStreamingEdgeObservedKernel D μ q U e r).map
          (fun z=> (z.2.1,(z.1.1,(z.1.2,z.2.2))))

def nativeStreamingEdgeIndexOrder (p k : ℕ) : Ordering :=
  if p=k then .eq else if p<k then .lt else .gt

end QuantitativeFollowup
