module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFuturePatternsClocks
public import FourPapersCommon.FiniteCascadeContinuationLeafGeometry
public import FourPapersCommon.FiniteCascadeFuturePairSpins

@[expose] public section

/-! Both shared-future marks are literal distinct new terminal leaves.
Their actual common ancestor has the sampled split clock. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def nativeStreamingGeneratedSharedFutureFirstLeaf
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth) :
    ObservationLeaf (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj).tree :=
  finiteCascadeContinuationNewLeaf (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).tree)
    (nativeStreamingGeneratedSharedFutureAnchor W v e)
    (observationPairFirstLeaf (finiteCascadeFuturePairTree (e.depth+1)
      (nativeStreamingGeneratedSharedFutureAnchor W v e).depth))

def nativeStreamingGeneratedSharedFutureSecondLeaf
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth) :
    ObservationLeaf (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj).tree :=
  finiteCascadeContinuationNewLeaf (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).tree)
    (nativeStreamingGeneratedSharedFutureAnchor W v e)
    (observationPairSecondLeaf (finiteCascadeFuturePairTree (e.depth+1)
      (nativeStreamingGeneratedSharedFutureAnchor W v e).depth))

theorem nativeStreamingGeneratedSharedFutureFirstLeaf_ne_second
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth) :
    nativeStreamingGeneratedSharedFutureFirstLeaf W v b hb e hj ≠
      nativeStreamingGeneratedSharedFutureSecondLeaf W v b hb e hj := by
  intro he
  have hi := finiteCascadeContinuationNewLeaf_injective
    (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).tree)
    (nativeStreamingGeneratedSharedFutureAnchor W v e)
  exact observationPair_first_ne_second _ (hi he)

theorem nativeStreamingGeneratedSharedFutureExtract_pair_eq_leaf_spins
    {E S : Type} (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (z : Records E S (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj).tree) :
    (finiteCascadeFutureGraftExtract (nativeStreamingGeneratedSharedFutureAnchor W v e)
      (e.depth+1) z).2 =
      (observationLeafSpin _ (nativeStreamingGeneratedSharedFutureFirstLeaf W v b hb e hj) z,
        observationLeafSpin _ (nativeStreamingGeneratedSharedFutureSecondLeaf W v b hb e hj) z) := by
  rw [finiteCascadeFutureGraftExtract,finiteCascadeContinuationExtract_eq_records]
  let U := fun d => (finiteCascadeFuturePairTree (e.depth+1) d).tree
  let V := nativeStreamingGeneratedSharedFutureAnchor W v e
  let P := finiteCascadeFuturePairTree (e.depth+1) V.depth
  change P.spins (finiteCascadeContinuationRecords U V z).2 =
    (observationLeafSpin (finiteCascadeContinuationGraft U V)
      (finiteCascadeContinuationNewLeaf U V (observationPairFirstLeaf P)) z,
      observationLeafSpin (finiteCascadeContinuationGraft U V)
        (finiteCascadeContinuationNewLeaf U V (observationPairSecondLeaf P)) z)
  rw [finiteCascadeContinuationNewLeaf_spin,finiteCascadeContinuationNewLeaf_spin]
  exact observationPair_spins_eq_leaf_pair _ _

theorem nativeStreamingGeneratedSharedFutureLeaves_commonLevel
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth) :
    observationCommonLevel (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj).tree
      (nativeStreamingGeneratedSharedFutureFirstLeaf W v b hb e hj)
      (nativeStreamingGeneratedSharedFutureSecondLeaf W v b hb e hj) = e.depth+1 := by
  change observationCommonLevel (finiteCascadeContinuationGraft
    (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).tree)
    (nativeStreamingGeneratedSharedFutureAnchor W v e))
      (finiteCascadeContinuationNewLeaf (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).tree)
        (nativeStreamingGeneratedSharedFutureAnchor W v e)
        (observationPairFirstLeaf (finiteCascadeFuturePairTree (e.depth+1)
          (nativeStreamingGeneratedSharedFutureAnchor W v e).depth)))
      (finiteCascadeContinuationNewLeaf (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).tree)
        (nativeStreamingGeneratedSharedFutureAnchor W v e)
        (observationPairSecondLeaf (finiteCascadeFuturePairTree (e.depth+1)
          (nativeStreamingGeneratedSharedFutureAnchor W v e).depth))) = _
  rw [finiteCascadeContinuationNewLeaf_commonLevel,observationPair_commonLevel,
    finiteCascadeFuturePairTree_split _ _ (nativeStreamingGeneratedSharedFuture_split_le_anchor W v e hj)]

theorem nativeStreamingGeneratedSharedFutureLeaves_commonClock
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj)
      (Fin.snoc h r)
      (observationCommonLevel (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj).tree
        (nativeStreamingGeneratedSharedFutureFirstLeaf W v b hb e hj)
        (nativeStreamingGeneratedSharedFutureSecondLeaf W v b hb e hj)) = r := by
  rw [nativeStreamingGeneratedSharedFutureLeaves_commonLevel]
  exact nativeStreamingGeneratedSharedFuture_split_clock W v b hb e hj h r hh hr

end QuantitativeFollowup
