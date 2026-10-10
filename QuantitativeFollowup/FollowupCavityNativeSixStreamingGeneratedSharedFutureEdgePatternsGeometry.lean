module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFutureEdgePatternsLaw
public import FourPapersCommon.FiniteCascadeContinuationLeafGeometry
public import FourPapersCommon.FiniteCascadeFuturePairSpins
public import FourPapersCommon.FiniteObservationRefinementLeafGeometry

@[expose] public section

/-! The original terminal leaves and the two actual shared-future leaves
are retained literally by the enlarged genealogy, including their clocks. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def nativeStreamingGeneratedSharedFutureEdgeFirstLeaf
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    ObservationLeaf (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree :=
  finiteCascadeContinuationNewLeaf
    (fun d => (finiteCascadeFuturePairTree (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) d).tree)
    (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
    (observationPairFirstLeaf (finiteCascadeFuturePairTree (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)
      (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj).depth))

def nativeStreamingGeneratedSharedFutureEdgeSecondLeaf
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    ObservationLeaf (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree :=
  finiteCascadeContinuationNewLeaf
    (fun d => (finiteCascadeFuturePairTree (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) d).tree)
    (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
    (observationPairSecondLeaf (finiteCascadeFuturePairTree (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)
      (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj).depth))

def nativeStreamingGeneratedSharedFutureEdgeOldLeaf
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (i : ObservationLeaf W.tree) :
    ObservationLeaf (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree :=
  finiteCascadeContinuationOldLeaf
    (fun d => (finiteCascadeFuturePairTree (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) d).tree)
    (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
    (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision W.tree i)

theorem nativeStreamingGeneratedSharedFutureEdgeFirstLeaf_ne_second
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    nativeStreamingGeneratedSharedFutureEdgeFirstLeaf W e j hj≠
      nativeStreamingGeneratedSharedFutureEdgeSecondLeaf W e j hj := by
  intro he
  have hi := finiteCascadeContinuationNewLeaf_injective
    (fun d => (finiteCascadeFuturePairTree (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) d).tree)
    (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
  exact observationPair_first_ne_second _ (hi he)

theorem nativeStreamingGeneratedSharedFutureEdgeExtract_pair_eq_leaf_spins
    {E S : Type} (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth)
    (z : Records E S (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree) :
    (finiteCascadeFutureGraftExtract (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
      (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) z).2=
      (observationLeafSpin _ (nativeStreamingGeneratedSharedFutureEdgeFirstLeaf W e j hj) z,
        observationLeafSpin _ (nativeStreamingGeneratedSharedFutureEdgeSecondLeaf W e j hj) z) := by
  rw [finiteCascadeFutureGraftExtract,finiteCascadeContinuationExtract_eq_records]
  let p := nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j
  let U := fun d => (finiteCascadeFuturePairTree p d).tree
  let V := nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj
  let P := finiteCascadeFuturePairTree p V.depth
  change P.spins (finiteCascadeContinuationRecords U V z).2=
    (observationLeafSpin (finiteCascadeContinuationGraft U V)
      (finiteCascadeContinuationNewLeaf U V (observationPairFirstLeaf P)) z,
      observationLeafSpin (finiteCascadeContinuationGraft U V)
        (finiteCascadeContinuationNewLeaf U V (observationPairSecondLeaf P)) z)
  rw [finiteCascadeContinuationNewLeaf_spin,finiteCascadeContinuationNewLeaf_spin]
  exact observationPair_spins_eq_leaf_pair _ _

theorem nativeStreamingGeneratedSharedFutureEdgeOldLeaf_spin
    {E S : Type} (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (i : ObservationLeaf W.tree)
    (z : Records E S (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree) :
    observationLeafSpin _ (nativeStreamingGeneratedSharedFutureEdgeOldLeaf W e j hj i) z=
      observationLeafSpin W.tree i (observationRefinementProject nativeStreamingPairObservationSubdivision W.tree
        (finiteCascadeFutureGraftExtract (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
          (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) z).1) := by
  let p := nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j
  let U := fun d => (finiteCascadeFuturePairTree p d).tree
  let V := nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj
  change observationLeafSpin (finiteCascadeContinuationGraft U V)
    (finiteCascadeContinuationOldLeaf U V (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision W.tree i)) z=_
  rw [finiteCascadeContinuationOldLeaf_spin]
  change observationLeafSpin (observationRefineTree nativeStreamingPairObservationSubdivision W.tree)
    (observationRefinementLeafEmbed nativeStreamingPairObservationSubdivision W.tree i)
    (finiteCascadeContinuationRecords U V z).1=_
  rw [observationRefinementLeafEmbed_spin,
    finiteCascadeFutureGraftExtract,finiteCascadeContinuationExtract_eq_records]

theorem nativeStreamingGeneratedSharedFutureEdgeLeaves_commonLevel
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    observationCommonLevel (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree
      (nativeStreamingGeneratedSharedFutureEdgeFirstLeaf W e j hj)
      (nativeStreamingGeneratedSharedFutureEdgeSecondLeaf W e j hj)=
        nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j := by
  let p := nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j
  let U := fun d => (finiteCascadeFuturePairTree p d).tree
  let V := nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj
  let P := finiteCascadeFuturePairTree p V.depth
  change observationCommonLevel (finiteCascadeContinuationGraft U V)
    (finiteCascadeContinuationNewLeaf U V (observationPairFirstLeaf P))
    (finiteCascadeContinuationNewLeaf U V (observationPairSecondLeaf P))=p
  rw [finiteCascadeContinuationNewLeaf_commonLevel,observationPair_commonLevel,
    finiteCascadeFuturePairTree_split _ _ (nativeStreamingGeneratedSharedFutureEdge_split_le_anchor W e j hj)]

theorem nativeStreamingGeneratedSharedFutureEdgeLeaves_commonClock
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h e.depth)
    (hl : nativeStreamingGeneratedComponentClock W h (j+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h j)
    (hrl : r<l) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj)
      (nativeStreamingGeneratedCrossEdgeAppend h r l)
      (observationCommonLevel (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree
        (nativeStreamingGeneratedSharedFutureEdgeFirstLeaf W e j hj)
        (nativeStreamingGeneratedSharedFutureEdgeSecondLeaf W e j hj))=l := by
  rw [nativeStreamingGeneratedSharedFutureEdgeLeaves_commonLevel]
  exact nativeStreamingGeneratedSharedFutureEdge_split_clock W e j hj h r l hh hr hl hrl

theorem nativeStreamingGeneratedSharedFutureEdgeComponent_leafCount
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree)=
      FiniteCascadeGenealogy.leafCount (asGenealogy W.tree)+2 := by
  change FiniteCascadeGenealogy.leafCount (asGenealogy
    (finiteCascadeFutureVertexGraft (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
      (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)))=_
  rw [finiteCascadeFutureVertexGraft_leafCount]
  exact congrArg (fun L : ℕ => L+2)
    (leafCount_observationRefineTree nativeStreamingPairObservationSubdivision W.tree)

end QuantitativeFollowup
