module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawDefinitions
public import QuantitativeFollowup.SupportingGeneratedFutureOriginOldPairsGeometry
public import QuantitativeFollowup.SupportingGeneratedRawRefinementForkProvenance
public import QuantitativeFollowup.SupportingGeneratedRawForkProvenance

@[expose] public section

/-! A future operation on an actual observed tree. Its shape retains every
old unary observation. Both physical draws use the original clock cells;
the strict future condition determines the honest chronological slots. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {J : ℕ}

def cavityGeneratedObservedRawFutureOrigin (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (r : Paper.Overlap) : NativeStreamingOrigin T :=
  match γ with
  | .inl i => .vertex ((cavityGeneratedOriginForkVertices T).get i)
  | .inr (.inl i) => .edge ((cavityGeneratedOriginEdges T).get i) r
  | .inr (.inr _) => .vertex (.root T)

def cavityGeneratedObservedRawFutureSubdivision (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) : ℕ → ℕ :=
  match γ with
  | .inr (.inl _) => nativeStreamingPairObservationSubdivision
  | _ => nativeStreamingEdgeSubdivision j

def cavityGeneratedObservedRawFutureAnchor (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) :
    FiniteCascadeRecordVertex (observationRefineTree
      (cavityGeneratedObservedRawFutureSubdivision T γ j) T) :=
  match γ with
  | .inl i => nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T
      ((cavityGeneratedOriginForkVertices T).get i)
  | .inr (.inl i) =>
      let e := (cavityGeneratedOriginEdges T).get i
      nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
        (if e.depth = j then 1 else 0)
  | .inr (.inr _) => nativeStreamingRefinementVertexEmbed
      (nativeStreamingEdgeSubdivision j) T (.root T)

def cavityGeneratedObservedRawFutureSplit (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) : ℕ :=
  match γ with
  | .inr (.inl _) => observationRefinementDepth nativeStreamingPairObservationSubdivision j + 1
  | _ => j + 1

def cavityGeneratedObservedRawFutureTree (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) :=
  finiteCascadeFutureVertexGraft (cavityGeneratedObservedRawFutureAnchor T γ j)
    (cavityGeneratedObservedRawFutureSplit T γ j)

def cavityGeneratedObservedRawFutureClock (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap) : ℕ → Paper.Overlap :=
  match γ with
  | .inr (.inl i) => nativeStreamingPairObservationSchedule q
      ((cavityGeneratedOriginEdges T).get i).depth j r l
  | _ => nativeStreamingEdgeSchedule q j l

def cavityGeneratedObservedRawFutureSourceCell (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap) : Prop :=
  r = nativeStreamingOriginLevel q (cavityGeneratedObservedRawFutureOrigin T γ r) ∧
    (match γ with
    | .inr (.inl i) => r ∈ Ioc (q (((cavityGeneratedOriginEdges T).get i).depth + 1))
        (q ((cavityGeneratedOriginEdges T).get i).depth)
    | _ => True) ∧ l ∈ Ioc (q (j+1)) (q j) ∧ r < l

def cavityGeneratedObservedRawFutureTerminalProject {S : Type}
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) :=
  printedGeneratedRefinedFutureTerminalProject (S:=S)
    (cavityGeneratedObservedRawFutureSubdivision T γ j) T
    (cavityGeneratedObservedRawFutureAnchor T γ j) (cavityGeneratedObservedRawFutureSplit T γ j)

def cavityGeneratedObservedRawFutureOldLeaf (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) :=
  printedGeneratedRefinedFutureOldLeaf (cavityGeneratedObservedRawFutureSubdivision T γ j) T
    (cavityGeneratedObservedRawFutureAnchor T γ j) (cavityGeneratedObservedRawFutureSplit T γ j)

def cavityGeneratedObservedRawFutureFirstLeaf (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) :=
  printedGeneratedRefinedFutureFirstLeaf (cavityGeneratedObservedRawFutureSubdivision T γ j) T
    (cavityGeneratedObservedRawFutureAnchor T γ j) (cavityGeneratedObservedRawFutureSplit T γ j)

def cavityGeneratedObservedRawFutureSecondLeaf (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) :=
  printedGeneratedRefinedFutureSecondLeaf (cavityGeneratedObservedRawFutureSubdivision T γ j) T
    (cavityGeneratedObservedRawFutureAnchor T γ j) (cavityGeneratedObservedRawFutureSplit T γ j)

theorem cavityGeneratedObservedRawFutureTree_leafCount (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (cavityGeneratedObservedRawFutureTree T γ j)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T) + 2 := by
  rw [cavityGeneratedObservedRawFutureTree, finiteCascadeFutureVertexGraft_leafCount,
    leafCount_observationRefineTree]

theorem cavityGeneratedObservedRawFutureClock_refinement (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap) (k : ℕ) :
    cavityGeneratedObservedRawFutureClock q T γ j r l
      (observationRefinementDepth (cavityGeneratedObservedRawFutureSubdivision T γ j) k) = q k := by
  rcases γ with i | (i | u)
  · exact nativeStreamingEdgeSchedule_refinement q j l k
  · exact nativeStreamingPairObservationSchedule_refinement q _ j r l k
  · exact nativeStreamingEdgeSchedule_refinement q j l k

theorem cavityGeneratedObservedRawFutureClock_antitone (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) (r l : Paper.Overlap)
    (hc : cavityGeneratedObservedRawFutureSourceCell q T γ j r l) :
    Antitone (cavityGeneratedObservedRawFutureClock q T γ j r l) := by
  rcases γ with i | (i | u)
  · exact nativeStreamingEdgeSchedule_antitone q hq j l ⟨hc.2.2.1.1.le,hc.2.2.1.2⟩
  · exact nativeStreamingPairObservationSchedule_antitone q hq _ j r l
      ⟨hc.2.1.1.le,hc.2.1.2⟩ ⟨hc.2.2.1.1.le,hc.2.2.1.2⟩
  · exact nativeStreamingEdgeSchedule_antitone q hq j l ⟨hc.2.2.1.1.le,hc.2.2.1.2⟩

theorem cavityGeneratedObservedRawFutureSplit_le_anchor (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) (r l : Paper.Overlap)
    (hc : cavityGeneratedObservedRawFutureSourceCell q T γ j r l) :
    cavityGeneratedObservedRawFutureSplit T γ j ≤
      (cavityGeneratedObservedRawFutureAnchor T γ j).depth := by
  rcases γ with i | (i | u)
  · let v := (cavityGeneratedOriginForkVertices T).get i
    have hr : r = q v.depth := hc.1
    have hj : (j : ℕ) < v.depth := by
      by_contra hn
      have h := hq (show v.depth ≤ j by omega)
      exact (not_lt_of_ge h) (by rw [←hr]; exact hc.2.2.2.trans_le hc.2.2.1.2)
    change j+1 ≤ (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T v).depth
    rw [nativeStreamingRefinementVertexEmbed_depth,nativeStreamingEdgeSubdivision_depth,
      if_neg (by omega : ¬v.depth ≤ j)]
    omega
  · let e := (cavityGeneratedOriginEdges T).get i
    have hj : (j : ℕ) ≤ e.depth := by
      by_contra hn
      have h := hq (show e.depth+1 ≤ j by omega)
      exact (not_lt_of_ge h) ((hc.2.1.1.trans hc.2.2.2).trans_le hc.2.2.1.2)
    change observationRefinementDepth nativeStreamingPairObservationSubdivision j + 1 ≤
      (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
        (if e.depth = j then 1 else 0)).depth
    rw [nativeStreamingEdgeSelectedVertex_depth _ e _ (by
      unfold nativeStreamingPairObservationSubdivision; split_ifs <;> omega),
      nativeStreamingPairObservationSubdivision_depth,nativeStreamingPairObservationSubdivision_depth]
    split_ifs <;> omega
  · change j+1 ≤ (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T (.root T)).depth
    rw [nativeStreamingRefinementVertexEmbed_depth]
    change j+1 ≤ observationRefinementDepth (nativeStreamingEdgeSubdivision j) J
    rw [nativeStreamingEdgeSubdivision_depth,if_neg (by omega : ¬J ≤ j)]
    omega

theorem cavityGeneratedObservedRawFutureClock_split (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap) (hrl : r < l) :
    cavityGeneratedObservedRawFutureClock q T γ j r l
      (cavityGeneratedObservedRawFutureSplit T γ j) = l := by
  rcases γ with i | (i | u)
  · exact nativeStreamingEdgeSchedule_inserted q j l
  · have hidx : nativeStreamingPairObservationIndex j
        ((cavityGeneratedOriginEdges T).get i).depth l r = 0 := by
      simp only [nativeStreamingPairObservationIndex,if_neg (not_lt_of_ge hrl.le),ite_self]
    change nativeStreamingPairObservationSchedule q ((cavityGeneratedOriginEdges T).get i).depth
      j r l (observationRefinementDepth nativeStreamingPairObservationSubdivision j+1) = l
    simpa only [hidx,Nat.add_zero] using
      nativeStreamingPairObservationIndex_second_level q
        ((cavityGeneratedOriginEdges T).get i).depth j r l
  · exact nativeStreamingEdgeSchedule_inserted q j l

theorem cavityGeneratedObservedRawFutureClock_anchor (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap)
    (hc : cavityGeneratedObservedRawFutureSourceCell q T γ j r l) :
    cavityGeneratedObservedRawFutureClock q T γ j r l
      (cavityGeneratedObservedRawFutureAnchor T γ j).depth = r := by
  rcases γ with i | (i | u)
  · change nativeStreamingEdgeSchedule q j l
        (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T
          ((cavityGeneratedOriginForkVertices T).get i)).depth = r
    rw [nativeStreamingRefinementVertexEmbed_depth,nativeStreamingEdgeSchedule_refinement]
    exact hc.1.symm
  · let e := (cavityGeneratedOriginEdges T).get i
    change nativeStreamingPairObservationSchedule q e.depth j r l
      (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
        (if e.depth = j then 1 else 0)).depth = r
    rw [nativeStreamingEdgeSelectedVertex_depth _ e _ (by
      unfold nativeStreamingPairObservationSubdivision; split_ifs <;> omega)]
    have hi : nativeStreamingPairObservationIndex e.depth j r l =
        (if e.depth = j then 1 else 0) := by
      simp only [nativeStreamingPairObservationIndex,if_pos hc.2.2.2]
    rw [←hi]
    exact nativeStreamingPairObservationIndex_level q e.depth j r l
  · change nativeStreamingEdgeSchedule q j l
        (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T (.root T)).depth = r
    rw [nativeStreamingRefinementVertexEmbed_depth,nativeStreamingEdgeSchedule_refinement]
    exact hc.1.symm

theorem cavityGeneratedObservedRawFutureTerminalProject_old_leaf {S : Type}
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J)
    (i : ObservationLeaf T) (σ : TerminalSpins S (cavityGeneratedObservedRawFutureTree T γ j)) :
    observationTerminalSpin T i (cavityGeneratedObservedRawFutureTerminalProject T γ j σ).1 =
      observationTerminalSpin _ (cavityGeneratedObservedRawFutureOldLeaf T γ j i) σ :=
  printedGeneratedRefinedFutureTerminalProject_old_leaf _ T _ _ i σ

theorem cavityGeneratedObservedRawFutureTerminalProject_pair {S : Type}
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J)
    (σ : TerminalSpins S (cavityGeneratedObservedRawFutureTree T γ j)) :
    (cavityGeneratedObservedRawFutureTerminalProject T γ j σ).2 =
      (observationTerminalSpin _ (cavityGeneratedObservedRawFutureFirstLeaf T γ j) σ,
        observationTerminalSpin _ (cavityGeneratedObservedRawFutureSecondLeaf T γ j) σ) :=
  printedGeneratedRefinedFutureTerminalProject_pair _ T _ _ σ

theorem cavityGeneratedObservedRawFutureOldLeaves_commonClock (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap) (i k : ObservationLeaf T) :
    cavityGeneratedObservedRawFutureClock q T γ j r l
      (observationCommonLevel _ (cavityGeneratedObservedRawFutureOldLeaf T γ j i)
        (cavityGeneratedObservedRawFutureOldLeaf T γ j k)) = q (observationCommonLevel T i k) := by
  unfold cavityGeneratedObservedRawFutureOldLeaf
  rw [printedGeneratedRefinedFutureOldLeaves_commonLevel]
  exact cavityGeneratedObservedRawFutureClock_refinement q T γ j r l _

theorem cavityGeneratedObservedRawFutureFreshLeaves_commonClock (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) (r l : Paper.Overlap)
    (hc : cavityGeneratedObservedRawFutureSourceCell q T γ j r l) :
    cavityGeneratedObservedRawFutureClock q T γ j r l
      (observationCommonLevel _ (cavityGeneratedObservedRawFutureFirstLeaf T γ j)
        (cavityGeneratedObservedRawFutureSecondLeaf T γ j)) = l := by
  unfold cavityGeneratedObservedRawFutureFirstLeaf cavityGeneratedObservedRawFutureSecondLeaf
    printedGeneratedRefinedFutureFirstLeaf printedGeneratedRefinedFutureSecondLeaf
  rw [finiteCascadeContinuationNewLeaf_commonLevel,observationPair_commonLevel,
    finiteCascadeFuturePairTree_split _ _
      (cavityGeneratedObservedRawFutureSplit_le_anchor q hq T γ j r l hc)]
  exact cavityGeneratedObservedRawFutureClock_split q T γ j r l hc.2.2.2

end QuantitativeFollowup
