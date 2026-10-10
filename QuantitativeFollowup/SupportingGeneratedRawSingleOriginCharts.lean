module
public import QuantitativeFollowup.SupportingGeneratedRawEdgeObservedComponent

@[expose] public section

/-! Raw single/current origin charts construct the actual observed
successor trees. Existing unary observations are retained, endpoint
vertices are allowed, and support follows from the original support and
the real selected cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedObservedRawChartFork (U : CavityGeneratedObservedRawComponent m)
    (i : Fin (cavityGeneratedOriginForkVertices U.tree).length) : FiniteCascadeRecordVertex U.tree :=
  (cavityGeneratedOriginForkVertices U.tree).get i

def cavityGeneratedObservedRawChartEdge (U : CavityGeneratedObservedRawComponent m)
    (i : Fin (cavityGeneratedOriginEdges U.tree).length) : NativeStreamingEdge U.tree :=
  (cavityGeneratedOriginEdges U.tree).get i

def cavityGeneratedObservedRawChartOrigin (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (r : Paper.Overlap) : NativeStreamingOrigin U.tree :=
  match γ with
  | .inl i => .vertex (cavityGeneratedObservedRawChartFork U i)
  | .inr (.inl i) => .edge (cavityGeneratedObservedRawChartEdge U i) r
  | .inr (.inr _) => .vertex (.root U.tree)

def cavityGeneratedObservedRawChartClock (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) : Paper.Overlap :=
  match γ with
  | .inl i => U.clock h (cavityGeneratedObservedRawChartFork U i).depth
  | .inr (.inl _) => r
  | .inr (.inr _) => U.clock h U.depth

def cavityGeneratedObservedRawChartCell (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) : Prop :=
  match γ with
  | .inl _ => True
  | .inr (.inl i) => U.clock h ((cavityGeneratedObservedRawChartEdge U i).depth+1)≤r ∧
      r≤U.clock h (cavityGeneratedObservedRawChartEdge U i).depth
  | .inr (.inr _) => True

def cavityGeneratedObservedRawChartComponent (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (k : NativeStreamingGeneratedVertexKind) :
    CavityGeneratedObservedRawComponent (m+1) :=
  match γ with
  | .inl i => cavityGeneratedObservedRawVertexGraftComponent (U.reindex Fin.castSucc)
      (cavityGeneratedObservedRawChartFork U i) (Fin.last m) k
  | .inr (.inl i) => cavityGeneratedObservedRawEdgeGraftComponent U
      (cavityGeneratedObservedRawChartEdge U i) k
  | .inr (.inr _) => cavityGeneratedObservedRawVertexGraftComponent (U.reindex Fin.castSucc)
      (.root U.tree) (Fin.last m) k

/-- Actual support at the literal appended selected clock. -/
theorem cavityGeneratedObservedRawChartComponent_support
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h∈U.supportSet) (hr : cavityGeneratedObservedRawChartCell U γ h r) :
    Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r)∈
      (cavityGeneratedObservedRawChartComponent U γ k).supportSet := by
  have hprefix (r : Paper.Overlap) : cavityGeneratedHistoryPrefix (Fin.snoc h r)=h :=
    cavityGeneratedHistoryPrefix_snoc h r
  have hsupport (r : Paper.Overlap) : Fin.snoc h r∈(U.reindex Fin.castSucc).supportSet := by
    rw [U.reindex_support]
    simpa only [Fin.snoc_castSucc] using hh
  rcases γ with i | (i | u)
  · apply cavityGeneratedObservedRawVertexGraftComponent_support _ _ _ k _ (hsupport _)
    simp only [CavityGeneratedObservedRawComponent.reindex_clock,Fin.snoc_castSucc,Fin.snoc_last]
    rfl
  · apply cavityGeneratedObservedRawEdgeGraftComponent_support U _ k _
    · simpa only [hprefix] using hh
    · simpa only [cavityGeneratedObservedRawChartClock,cavityGeneratedObservedRawChartCell,hprefix,Fin.snoc_last] using hr
  · apply cavityGeneratedObservedRawVertexGraftComponent_support _ _ _ k _ (hsupport _)
    simp only [CavityGeneratedObservedRawComponent.reindex_clock,Fin.snoc_castSucc,Fin.snoc_last]
    rfl

/-- The actual output physical schedule is the original one, or its true edge insertion. -/
theorem cavityGeneratedObservedRawChartComponent_clock
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hr : cavityGeneratedObservedRawChartCell U γ h r) :
    (cavityGeneratedObservedRawChartComponent U γ k).clock
      (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r)) =
      match γ with
      | .inl _ => U.clock h
      | .inr (.inl i) => nativeStreamingEdgeSchedule (U.clock h)
          (cavityGeneratedObservedRawChartEdge U i).depth r
      | .inr (.inr _) => U.clock h := by
  rcases γ with i | (i | u)
  · change (U.reindex Fin.castSucc).clock (Fin.snoc h _) = _
    rw [U.reindex_clock]
    simp only [Fin.snoc_castSucc]
  · have H := cavityGeneratedObservedRawEdgeGraftComponent_clock U
      (cavityGeneratedObservedRawChartEdge U i) k (Fin.snoc h r)
      (by simpa only [cavityGeneratedObservedRawChartCell,cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last] using hr)
    simpa only [cavityGeneratedObservedRawChartComponent,cavityGeneratedObservedRawChartClock,
      cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last] using H
  · change (U.reindex Fin.castSucc).clock (Fin.snoc h _) = _
    rw [U.reindex_clock]
    simp only [Fin.snoc_castSucc]

theorem cavityGeneratedObservedRawChartComponent_leafCount
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (cavityGeneratedObservedRawChartComponent U γ k).tree) =
      FiniteCascadeGenealogy.leafCount (asGenealogy U.tree)+k.newLeafCount := by
  rcases γ with i | (i | u)
  · exact cavityGeneratedObservedRawVertexGraftComponent_leafCount _ _ _ k
  · change FiniteCascadeGenealogy.leafCount (asGenealogy
      (cavityGeneratedObservedRawVertexGraftComponent (cavityGeneratedObservedRawEdgeObservedComponent U
        (cavityGeneratedObservedRawChartEdge U i)) _ _ k).tree) = _
    rw [cavityGeneratedObservedRawVertexGraftComponent_leafCount]
    exact congrArg (fun x : ℕ=>x+k.newLeafCount) (printedGeneratedRefinement_leafCount _ U.tree)
  · exact cavityGeneratedObservedRawVertexGraftComponent_leafCount _ _ _ k

end QuantitativeFollowup
