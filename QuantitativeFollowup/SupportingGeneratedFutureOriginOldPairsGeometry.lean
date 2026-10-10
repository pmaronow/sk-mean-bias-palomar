module
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginSourceReceiverTerminal
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFutureEdgePatternsGeometry
public import QuantitativeFollowup.SupportingGeneratedSingleOriginNewPairs
public import FourPapersCommon.FiniteObservationRefinementTerminalLeaves

@[expose] public section

/-! Literal old and fresh leaves of a refined shared-future graft.  The
terminal projection preserves every old spin and extracts the two actual
fresh leaves.  No probability-law or clock identity is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n J : ℕ}

def printedGeneratedRefinedFutureOldLeaf (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ)
    (i : ObservationLeaf T) : ObservationLeaf (finiteCascadeFutureVertexGraft v p) :=
  finiteCascadeContinuationOldLeaf (fun j => (finiteCascadeFuturePairTree p j).tree) v
    (observationRefinementLeafEmbed d T i)

def printedGeneratedRefinedFutureFirstLeaf (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ) :
    ObservationLeaf (finiteCascadeFutureVertexGraft v p) :=
  finiteCascadeContinuationNewLeaf (fun j => (finiteCascadeFuturePairTree p j).tree) v
    (observationPairFirstLeaf (finiteCascadeFuturePairTree p v.depth))

def printedGeneratedRefinedFutureSecondLeaf (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ) :
    ObservationLeaf (finiteCascadeFutureVertexGraft v p) :=
  finiteCascadeContinuationNewLeaf (fun j => (finiteCascadeFuturePairTree p j).tree) v
    (observationPairSecondLeaf (finiteCascadeFuturePairTree p v.depth))

theorem printedGeneratedRefinedFutureOldLeaf_injective
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ) :
    Function.Injective (printedGeneratedRefinedFutureOldLeaf d T v p) :=
  (finiteCascadeContinuationOldLeaf_injective _ v).comp
    (observationRefinementLeafEmbed_injective d T)

theorem printedGeneratedRefinedFutureFirstLeaf_ne_second
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ) :
    printedGeneratedRefinedFutureFirstLeaf d T v p ≠
      printedGeneratedRefinedFutureSecondLeaf d T v p := by
  intro he
  exact observationPair_first_ne_second _
    (finiteCascadeContinuationNewLeaf_injective _ v he)

theorem printedGeneratedRefinedFutureOldLeaf_ne_first
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ)
    (i : ObservationLeaf T) :
    printedGeneratedRefinedFutureOldLeaf d T v p i ≠
      printedGeneratedRefinedFutureFirstLeaf d T v p :=
  finiteCascadeContinuationOldNewLeaf_ne _ v _ _

theorem printedGeneratedRefinedFutureOldLeaf_ne_second
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ)
    (i : ObservationLeaf T) :
    printedGeneratedRefinedFutureOldLeaf d T v p i ≠
      printedGeneratedRefinedFutureSecondLeaf d T v p :=
  finiteCascadeContinuationOldNewLeaf_ne _ v _ _

theorem printedGeneratedRefinedFutureTerminalProject_old_leaf {S : Type}
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ)
    (i : ObservationLeaf T) (σ : TerminalSpins S (finiteCascadeFutureVertexGraft v p)) :
    observationTerminalSpin T i (printedGeneratedRefinedFutureTerminalProject d T v p σ).1 =
      observationTerminalSpin _ (printedGeneratedRefinedFutureOldLeaf d T v p i) σ := by
  unfold printedGeneratedRefinedFutureTerminalProject
  rw [observationRefinementTerminalProject_leaf]
  exact nativeStreamingGeneratedContinuationTerminalMap_old_leaf _ v
    (observationRefinementLeafEmbed d T i) σ

theorem printedGeneratedRefinedFutureTerminalProject_pair {S : Type}
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ)
    (σ : TerminalSpins S (finiteCascadeFutureVertexGraft v p)) :
    (printedGeneratedRefinedFutureTerminalProject d T v p σ).2 =
      (observationTerminalSpin _ (printedGeneratedRefinedFutureFirstLeaf d T v p) σ,
        observationTerminalSpin _ (printedGeneratedRefinedFutureSecondLeaf d T v p) σ) := by
  exact congrArg₂ Prod.mk
    (nativeStreamingGeneratedContinuationTerminalMap_new_leaf
      (fun j => (finiteCascadeFuturePairTree p j).tree) v
      (observationPairFirstLeaf (finiteCascadeFuturePairTree p v.depth)) σ)
    (nativeStreamingGeneratedContinuationTerminalMap_new_leaf
      (fun j => (finiteCascadeFuturePairTree p j).tree) v
      (observationPairSecondLeaf (finiteCascadeFuturePairTree p v.depth)) σ)

theorem printedGeneratedRefinedFutureOldLeaves_commonLevel
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ)
    (i k : ObservationLeaf T) :
    observationCommonLevel (finiteCascadeFutureVertexGraft v p)
      (printedGeneratedRefinedFutureOldLeaf d T v p i)
      (printedGeneratedRefinedFutureOldLeaf d T v p k) =
      observationRefinementDepth d (observationCommonLevel T i k) := by
  unfold printedGeneratedRefinedFutureOldLeaf
  rw [finiteCascadeContinuationOldLeaf_commonLevel,observationRefinementLeafEmbed_commonLevel]

def printedGeneratedFutureVertexOldLeaf (U : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (j : ℕ) (hj : j < v.depth) (i : ObservationLeaf U.tree) :
    ObservationLeaf (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj).tree :=
  let B := printedGeneratedFutureVertexBase U v hv0 hvJ
  let e := printedGeneratedFutureCellEdge B j (hj.trans hvJ)
  printedGeneratedRefinedFutureOldLeaf (nativeStreamingEdgeSubdivision e.depth) B.tree
    (nativeStreamingGeneratedSharedFutureAnchor B v e) (e.depth+1) i

def printedGeneratedFutureVertexFirstLeaf (U : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (j : ℕ) (hj : j < v.depth) :
    ObservationLeaf (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj).tree :=
  let B := printedGeneratedFutureVertexBase U v hv0 hvJ
  let e := printedGeneratedFutureCellEdge B j (hj.trans hvJ)
  printedGeneratedRefinedFutureFirstLeaf (nativeStreamingEdgeSubdivision e.depth) B.tree
    (nativeStreamingGeneratedSharedFutureAnchor B v e) (e.depth+1)

def printedGeneratedFutureVertexSecondLeaf (U : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (j : ℕ) (hj : j < v.depth) :
    ObservationLeaf (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj).tree :=
  let B := printedGeneratedFutureVertexBase U v hv0 hvJ
  let e := printedGeneratedFutureCellEdge B j (hj.trans hvJ)
  printedGeneratedRefinedFutureSecondLeaf (nativeStreamingEdgeSubdivision e.depth) B.tree
    (nativeStreamingGeneratedSharedFutureAnchor B v e) (e.depth+1)

theorem printedGeneratedFutureVertexTerminalProject_old_leaf
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth)
    (i : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj)) :
    observationTerminalSpin U.tree i (printedGeneratedFutureVertexTerminalProject U v hv0 hvJ j hj σ).1 =
      observationTerminalSpin _ (printedGeneratedFutureVertexOldLeaf U v hv0 hvJ j hj i) σ :=
  printedGeneratedRefinedFutureTerminalProject_old_leaf _ _ _ _ i σ

theorem printedGeneratedFutureVertexTerminalProject_pair
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj)) :
    (printedGeneratedFutureVertexTerminalProject U v hv0 hvJ j hj σ).2 =
      (observationTerminalSpin _ (printedGeneratedFutureVertexFirstLeaf U v hv0 hvJ j hj) σ,
        observationTerminalSpin _ (printedGeneratedFutureVertexSecondLeaf U v hv0 hvJ j hj) σ) :=
  printedGeneratedRefinedFutureTerminalProject_pair _ _ _ _ σ

theorem printedGeneratedFutureVertexOldLeaves_commonClock
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hl : nativeStreamingGeneratedComponentClock U h (j+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j) (i k : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj)
      (nativeStreamingGeneratedCrossEdgeAppend h (nativeStreamingGeneratedComponentClock U h v.depth) l)
      (observationCommonLevel _ (printedGeneratedFutureVertexOldLeaf U v hv0 hvJ j hj i)
        (printedGeneratedFutureVertexOldLeaf U v hv0 hvJ j hj k)) =
      nativeStreamingGeneratedComponentClock U h (observationCommonLevel U.tree i k) := by
  let B := printedGeneratedFutureVertexBase U v hv0 hvJ
  let e := printedGeneratedFutureCellEdge B j (hj.trans hvJ)
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth)
  have hb : nativeStreamingGeneratedComponentClock B H = nativeStreamingGeneratedComponentClock U h :=
    printedGeneratedFutureVertexBase_clock_snoc U v hv0 hvJ h hh
  have he : e.depth = j := printedGeneratedFutureCellEdge_depth B j (hj.trans hvJ)
  have hH := printedGeneratedFutureVertexBase_snoc_order U v hv0 hvJ h hh
  have hlB : nativeStreamingGeneratedComponentClock B H (e.depth+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock B H e.depth := by rw [hb,he]; exact hl
  have hc := nativeStreamingGeneratedSharedFutureComponent_clock_snoc B v (Fin.last m)
    (printedGeneratedFutureVertexBase_label U v hv0 hvJ) e
    (by rw [he]; exact hj) H l hH hlB
  change nativeStreamingGeneratedComponentClock
    (nativeStreamingGeneratedSharedFutureComponent B v (Fin.last m)
      (printedGeneratedFutureVertexBase_label U v hv0 hvJ) e _) (Fin.snoc H l)
    (observationCommonLevel _
      (printedGeneratedRefinedFutureOldLeaf (nativeStreamingEdgeSubdivision e.depth) B.tree
        (nativeStreamingGeneratedSharedFutureAnchor B v e) (e.depth+1) i)
      (printedGeneratedRefinedFutureOldLeaf (nativeStreamingEdgeSubdivision e.depth) B.tree
        (nativeStreamingGeneratedSharedFutureAnchor B v e) (e.depth+1) k)) = _
  rw [hc,printedGeneratedRefinedFutureOldLeaves_commonLevel,hb,nativeStreamingEdgeSchedule_refinement]
  rfl

theorem printedGeneratedFutureVertexFreshLeaves_commonClock
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hl : nativeStreamingGeneratedComponentClock U h (j+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j) :
    nativeStreamingGeneratedComponentClock (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj)
      (nativeStreamingGeneratedCrossEdgeAppend h (nativeStreamingGeneratedComponentClock U h v.depth) l)
      (observationCommonLevel _ (printedGeneratedFutureVertexFirstLeaf U v hv0 hvJ j hj)
        (printedGeneratedFutureVertexSecondLeaf U v hv0 hvJ j hj)) = l := by
  let B := printedGeneratedFutureVertexBase U v hv0 hvJ
  let e := printedGeneratedFutureCellEdge B j (hj.trans hvJ)
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth)
  have hb : nativeStreamingGeneratedComponentClock B H = nativeStreamingGeneratedComponentClock U h :=
    printedGeneratedFutureVertexBase_clock_snoc U v hv0 hvJ h hh
  have he : e.depth = j := printedGeneratedFutureCellEdge_depth B j (hj.trans hvJ)
  have hlB : nativeStreamingGeneratedComponentClock B H (e.depth+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock B H e.depth := by rw [hb,he]; exact hl
  exact nativeStreamingGeneratedSharedFutureLeaves_commonClock B v (Fin.last m)
    (printedGeneratedFutureVertexBase_label U v hv0 hvJ) e (by rw [he]; exact hj) H l
    (printedGeneratedFutureVertexBase_snoc_order U v hv0 hvJ h hh) hlB

end QuantitativeFollowup
