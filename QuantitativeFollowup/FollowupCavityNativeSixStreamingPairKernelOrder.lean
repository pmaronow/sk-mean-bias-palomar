module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairObservedKernel

@[expose] public section

/-! The relative observation index is used only when both selected
ancestors are on the very same edge. It has no effect on different-edge
joint laws, including different branches at the same physical depth. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem nativeStreamingEdgePairObservedKernel_order_independent (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (o₁ o₂ : Ordering)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (e f : NativeStreamingEdge T)
    (hne : e≠f) (r l : Paper.Overlap) :
    nativeStreamingEdgePairObservedKernel D μ q o₁ T e f r l=
      nativeStreamingEdgePairObservedKernel D μ q o₂ T e f r l := by
  induction T with
  | leaf => cases e
  | @advance j T ih =>
      cases e with
      | here =>
          cases f with
          | here => exact (hne rfl).elim
          | child f => rfl
      | child e =>
          cases f with
          | here => rfl
          | child f =>
              have hchild : e≠f := fun h=>hne (congrArg NativeStreamingEdge.child h)
              change ((Kernel.id ×ₖ nativeStreamingEdgePairObservedKernel D μ q o₁ T e f r l) ∘ₖ
                anisotropicObservationTransition D μ (q (j+1)) (q j)).map _=
                ((Kernel.id ×ₖ nativeStreamingEdgePairObservedKernel D μ q o₂ T e f r l) ∘ₖ
                  anisotropicObservationTransition D μ (q (j+1)) (q j)).map _
              rw [ih e f hchild]
  | fork T U ihT ihU =>
      cases e with
      | left e =>
          cases f with
          | left f =>
              have hchild : e≠f := fun h=>hne (congrArg NativeStreamingEdge.left h)
              change (nativeStreamingEdgePairObservedKernel D μ q o₁ T e f r l ×ₖ
                anisotropicRecordedProfileTreeKernel D μ q U).map _=
                (nativeStreamingEdgePairObservedKernel D μ q o₂ T e f r l ×ₖ
                  anisotropicRecordedProfileTreeKernel D μ q U).map _
              rw [ihT e f hchild]
          | right f => rfl
      | right e =>
          cases f with
          | left f => rfl
          | right f =>
              have hchild : e≠f := fun h=>hne (congrArg NativeStreamingEdge.right h)
              change (anisotropicRecordedProfileTreeKernel D μ q T ×ₖ
                nativeStreamingEdgePairObservedKernel D μ q o₁ U e f r l).map _=
                (anisotropicRecordedProfileTreeKernel D μ q T ×ₖ
                  nativeStreamingEdgePairObservedKernel D μ q o₂ U e f r l).map _
              rw [ihU e f hchild]

end QuantitativeFollowup
