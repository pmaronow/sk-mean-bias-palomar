module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverProjection
public import QuantitativeFollowup.FollowupCavityGeneratedForestComponentReplacement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsMoments

@[expose] public section

/-! The concrete cross chart has an actual finite terminal projection,
retaining all original spins and its two ordered fresh spins. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def printedGeneratedMixedCrossTerminalProjection {S : Type}
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0<v.depth) (hvJ : v.depth<U.depth)
    (σ : TerminalSpins S (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ).tree) :
    TerminalSpins S U.tree × (S×S) :=
  let y := nativeStreamingGeneratedCrossVertexTerminalProjection
    (nativeStreamingGeneratedEdgeVertex U e) (nativeStreamingGeneratedMixedRefinedVertex U e v) σ
  (observationRefinementTerminalProject (nativeStreamingEdgeSubdivision e.depth) U.tree rfl y.1,y.2)

theorem printedGeneratedMixedCrossTerminalProjection_record {E S : Type}
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0<v.depth) (hvJ : v.depth<U.depth)
    (z : E × Records E S (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ).tree) :
    printedGeneratedMixedCrossTerminalProjection U e v hv0 hvJ (finiteCascadeRecordTerminalSpins _ z.2) =
      (finiteCascadeRecordTerminalSpins U.tree
        (nativeStreamingGeneratedMixedCrossRecordProjection U e v hv0 hvJ z).1.2,
        (nativeStreamingGeneratedMixedCrossRecordProjection U e v hv0 hvJ z).2) := by
  let t := nativeStreamingGeneratedEdgeVertex U e
  let w := nativeStreamingGeneratedMixedRefinedVertex U e v
  let y := finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin t w z.2
  have H := nativeStreamingGeneratedCrossVertexTerminalProjection_record t w z.2
  have H' := congrArg (fun p=>
    (observationRefinementTerminalProject (nativeStreamingEdgeSubdivision e.depth) U.tree rfl p.1,p.2)) H
  apply H'.trans
  exact congrArg (fun σ=>(σ,y.2))
    (observationRefinementTerminalProject_record (nativeStreamingEdgeSubdivision e.depth) U.tree rfl y.1)

def printedGeneratedEndpointCrossTerminalProject {S : Type}
    (U : CavityGeneratedConstructedComponent m) :
    (TerminalSpins S (nativeStreamingGeneratedEndpointComponent U).tree × (S×S)) →
      TerminalSpins S U.tree × (S×S) :=
  Prod.map (nativeStreamingGeneratedEndpointTerminalProject U) id

theorem printedGeneratedEndpointCrossTerminalProject_record {E S : Type}
    (U : CavityGeneratedConstructedComponent m)
    (z : CavityGeneratedCrossOriginalRecordPair E S (nativeStreamingGeneratedEndpointComponent U)) :
    printedGeneratedEndpointCrossTerminalProject U (finiteCascadeRecordTerminalSpins _ z.1.2,z.2) =
      (finiteCascadeRecordTerminalSpins U.tree (printedGeneratedEndpointCrossRecordProject U z).1.2,
        (printedGeneratedEndpointCrossRecordProject U z).2) := by
  exact Prod.ext (nativeStreamingGeneratedEndpointTerminalProject_record U z.1.2) rfl

def printedGeneratedOriginCrossChartTerminalProjection {S : Type}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    TerminalSpins S (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree →
      TerminalSpins S U.tree × (S×S) :=
  match γ₁,γ₂ with
  | .inl i,.inl j => nativeStreamingGeneratedCrossVertexTerminalProjection
      (printedGeneratedOriginChartFork U i) (printedGeneratedOriginChartFork U j)
  | .inr (.inl i),.inl j => printedGeneratedMixedCrossTerminalProjection U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartFork U j)
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2
  | .inl i,.inr (.inl j) => Prod.map id Prod.swap ∘ printedGeneratedMixedCrossTerminalProjection U
      (printedGeneratedOriginChartEdge U j) (printedGeneratedOriginChartFork U i)
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
  | .inr (.inl i),.inr (.inl j) => nativeStreamingGeneratedCrossEdgeTerminalProjection U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartEdge U j) k
  | .inr (.inr _),.inl j => printedGeneratedEndpointCrossTerminalProject U ∘
      nativeStreamingGeneratedCrossVertexTerminalProjection
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U j))
  | .inl i,.inr (.inr _) => printedGeneratedEndpointCrossTerminalProject U ∘
      nativeStreamingGeneratedCrossVertexTerminalProjection
        (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U i))
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
  | .inr (.inl i),.inr (.inr _) => printedGeneratedEndpointCrossTerminalProject U ∘
      printedGeneratedMixedCrossTerminalProjection (nativeStreamingGeneratedEndpointComponent U)
        (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U i))
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
  | .inr (.inr _),.inr (.inl j) => Prod.map id Prod.swap ∘
      printedGeneratedEndpointCrossTerminalProject U ∘
        printedGeneratedMixedCrossTerminalProjection (nativeStreamingGeneratedEndpointComponent U)
          (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U j))
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
  | .inr (.inr _),.inr (.inr _) => printedGeneratedEndpointCrossTerminalProject U ∘
      nativeStreamingGeneratedCrossVertexTerminalProjection
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))

theorem printedGeneratedOriginCrossChartTerminalProjection_record {E S : Type}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (z : E × Records E S (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) :
    printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k (finiteCascadeRecordTerminalSpins _ z.2) =
      (finiteCascadeRecordTerminalSpins U.tree
        (printedGeneratedOriginCrossChartRecordProjection U γ₁ γ₂ k z).1.2,
        (printedGeneratedOriginCrossChartRecordProjection U γ₁ γ₂ k z).2) := by
  rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
  · exact nativeStreamingGeneratedCrossVertexTerminalProjection_record _ _ z.2
  · exact congrArg (Prod.map id Prod.swap)
      (printedGeneratedMixedCrossTerminalProjection_record U _ _ _ _ z)
  · exact (congrArg (printedGeneratedEndpointCrossTerminalProject U)
      (nativeStreamingGeneratedCrossVertexTerminalProjection_record _ _ z.2)).trans
      (printedGeneratedEndpointCrossTerminalProject_record U
        (printedGeneratedCrossVertexRecordProjection (nativeStreamingGeneratedEndpointComponent U)
          (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U i))
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex_interior U _).1
          (nativeStreamingGeneratedEndpointVertex_interior U _).2
          (nativeStreamingGeneratedEndpointVertex_interior U _).1
          (nativeStreamingGeneratedEndpointVertex_interior U _).2 z))
  · exact printedGeneratedMixedCrossTerminalProjection_record _ _ _ _ _ z
  · exact nativeStreamingGeneratedCrossEdgeTerminalProjection_record _ _ _ _ z
  · exact (congrArg (printedGeneratedEndpointCrossTerminalProject U)
      (printedGeneratedMixedCrossTerminalProjection_record _ _ _ _ _ z)).trans
      (printedGeneratedEndpointCrossTerminalProject_record U
        (nativeStreamingGeneratedMixedCrossRecordProjection (nativeStreamingGeneratedEndpointComponent U)
          (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U i))
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex_interior U _).1
          (nativeStreamingGeneratedEndpointVertex_interior U _).2 z))
  · exact (congrArg (printedGeneratedEndpointCrossTerminalProject U)
      (nativeStreamingGeneratedCrossVertexTerminalProjection_record _ _ z.2)).trans
      (printedGeneratedEndpointCrossTerminalProject_record U
        (printedGeneratedCrossVertexRecordProjection (nativeStreamingGeneratedEndpointComponent U)
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U j))
          (nativeStreamingGeneratedEndpointVertex_interior U _).1
          (nativeStreamingGeneratedEndpointVertex_interior U _).2
          (nativeStreamingGeneratedEndpointVertex_interior U _).1
          (nativeStreamingGeneratedEndpointVertex_interior U _).2 z))
  · exact congrArg (Prod.map id Prod.swap)
      ((congrArg (printedGeneratedEndpointCrossTerminalProject U)
        (printedGeneratedMixedCrossTerminalProjection_record _ _ _ _ _ z)).trans
        (printedGeneratedEndpointCrossTerminalProject_record U
          (nativeStreamingGeneratedMixedCrossRecordProjection (nativeStreamingGeneratedEndpointComponent U)
            (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U j))
            (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
            (nativeStreamingGeneratedEndpointVertex_interior U _).1
            (nativeStreamingGeneratedEndpointVertex_interior U _).2 z)))
  · exact (congrArg (printedGeneratedEndpointCrossTerminalProject U)
      (nativeStreamingGeneratedCrossVertexTerminalProjection_record _ _ z.2)).trans
      (printedGeneratedEndpointCrossTerminalProject_record U
        (printedGeneratedCrossVertexRecordProjection (nativeStreamingGeneratedEndpointComponent U)
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex_interior U _).1
          (nativeStreamingGeneratedEndpointVertex_interior U _).2
          (nativeStreamingGeneratedEndpointVertex_interior U _).1
          (nativeStreamingGeneratedEndpointVertex_interior U _).2 z))

end QuantitativeFollowup
