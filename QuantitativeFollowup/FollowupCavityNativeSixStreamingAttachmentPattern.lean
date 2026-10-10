module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginCross
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginFuture
public import FourPapersCommon.FiniteObservationLeafGeometry

@[expose] public section

/-! The six source patterns carry their genuine old leaves and mark
origins.  Only the normalizer pattern opens an independent component.
Counts concern new time coordinates, separately from charge coefficients
and any unary observation padding. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
variable {J : ℕ}

inductive NativeStreamingAttachmentPattern (T : FiniteTerminalGenealogy J) where
  | original (i k : ObservationLeaf T)
  | originalFresh (i : ObservationLeaf T) (o : NativeStreamingOrigin T)
  | cross (o p : NativeStreamingOrigin T)
  | current (o : NativeStreamingOrigin T)
  | future (o : NativeStreamingOrigin T) (j : ℕ) (l : Paper.Overlap)
  | normalizer (l : Paper.Overlap)

@[reducible] def nativeStreamingAttachmentNewMarkCount
    {T : FiniteTerminalGenealogy J} : NativeStreamingAttachmentPattern T → ℕ
  | .original _ _ => 0
  | .originalFresh _ o => nativeStreamingOriginNewMarkCount o
  | .cross o p => nativeStreamingOriginNewMarkCount o + nativeStreamingOriginNewMarkCount p
  | .current o => nativeStreamingOriginNewMarkCount o
  | .future o _ _ => nativeStreamingOriginNewMarkCount o + 1
  | .normalizer _ => 1

@[reducible] def nativeStreamingAttachmentIndependentComponentCount
    {T : FiniteTerminalGenealogy J} : NativeStreamingAttachmentPattern T → ℕ
  | .normalizer _ => 1
  | _ => 0

theorem nativeStreamingAttachmentNewMarkCount_le_two
    {T : FiniteTerminalGenealogy J} (p : NativeStreamingAttachmentPattern T) :
    nativeStreamingAttachmentNewMarkCount p ≤ 2 := by
  cases p with
  | original i k => simp only [nativeStreamingAttachmentNewMarkCount]; omega
  | originalFresh i o =>
      exact (nativeStreamingOriginNewMarkCount_le_one o).trans (by omega)
  | cross o p => exact nativeStreamingOriginPairNewMarkCount_le_two o p
  | current o => exact (nativeStreamingOriginNewMarkCount_le_one o).trans (by omega)
  | future o j l => exact nativeStreamingOriginFutureNewMarkCount_le_two o
  | normalizer l => simp only [nativeStreamingAttachmentNewMarkCount]; omega

theorem nativeStreamingAttachmentIndependentComponentCount_le_one
    {T : FiniteTerminalGenealogy J} (p : NativeStreamingAttachmentPattern T) :
    nativeStreamingAttachmentIndependentComponentCount p ≤ 1 := by
  cases p <;> simp only [nativeStreamingAttachmentIndependentComponentCount] <;> omega

end QuantitativeFollowup
