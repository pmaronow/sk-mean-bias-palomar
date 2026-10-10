module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverClocks

@[expose] public section

/-! Every canonical cross chart projects its actual constructed record to
all original records and the two ordered fresh marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

abbrev CavityGeneratedCrossOriginalRecordPair (E S : Type)
    (U : CavityGeneratedConstructedComponent m) :=
  (E × Records E S U.tree) × (S × S)

def printedGeneratedCrossVertexRecordProjection {E S : Type}
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (hw0 : 0 < w.depth) (hwJ : w.depth < U.depth)
    (z : E × Records E S (nativeStreamingGeneratedCrossVertexComponent U v w hv0 hvJ hw0 hwJ).tree) :
    CavityGeneratedCrossOriginalRecordPair E S U :=
  let y := finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2
  ((z.1,y.1),y.2)

theorem measurable_printedGeneratedCrossVertexRecordProjection {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S]
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (hw0 : 0 < w.depth) (hwJ : w.depth < U.depth) :
    Measurable (printedGeneratedCrossVertexRecordProjection (E:=E) (S:=S) U v w hv0 hvJ hw0 hwJ) := by
  have hy := measurable_finiteCascadeCrossContinuationExtract (E:=E) (S:=S)
    observationLinearTree observationLinearSpin (fun j=>measurable_observationLinearSpin j) v w
  exact (measurable_fst.prodMk (hy.fst.comp measurable_snd)).prodMk (hy.snd.comp measurable_snd)

theorem measurable_printedGeneratedCrossEdgeRecordProjection {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S]
    (U : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    Measurable (nativeStreamingGeneratedCrossEdgeRecordProjection (E:=E) (S:=S) U e f k) := by
  have hy := measurable_finiteCascadeCrossContinuationExtract (E:=E) (S:=S)
    observationLinearTree observationLinearSpin (fun j=>measurable_observationLinearSpin j)
    (nativeStreamingGeneratedCrossEdgeFirstVertex U e f k)
    (nativeStreamingGeneratedCrossEdgeSecondVertex U e f k)
  exact (measurable_fst.prodMk
    ((measurable_observationRefinementProject nativeStreamingPairObservationSubdivision U.tree).comp
      (hy.fst.comp measurable_snd))).prodMk (hy.snd.comp measurable_snd)

def printedGeneratedEndpointCrossRecordProject {E S : Type}
    (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedCrossOriginalRecordPair E S (nativeStreamingGeneratedEndpointComponent U) →
      CavityGeneratedCrossOriginalRecordPair E S U :=
  Prod.map (Prod.map id (nativeStreamingGeneratedEndpointRecordProject U)) id

theorem measurable_printedGeneratedEndpointCrossRecordProject {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S] (U : CavityGeneratedConstructedComponent m) :
    Measurable (printedGeneratedEndpointCrossRecordProject (E:=E) (S:=S) U) :=
  (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject U)).prodMap measurable_id

def printedGeneratedOriginCrossChartRecordProjection {E S : Type}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    (E × Records E S (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) →
      CavityGeneratedCrossOriginalRecordPair E S U :=
  match γ₁, γ₂ with
  | .inl i, .inl j => printedGeneratedCrossVertexRecordProjection U
      (printedGeneratedOriginChartFork U i) (printedGeneratedOriginChartFork U j)
      (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2
  | .inr (.inl i), .inl j => nativeStreamingGeneratedMixedCrossRecordProjection U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartFork U j)
      (printedGeneratedOriginChartFork_interior U j).1 (printedGeneratedOriginChartFork_interior U j).2
  | .inl i, .inr (.inl j) => Prod.map id Prod.swap ∘
      nativeStreamingGeneratedMixedCrossRecordProjection U (printedGeneratedOriginChartEdge U j)
        (printedGeneratedOriginChartFork U i)
        (printedGeneratedOriginChartFork_interior U i).1 (printedGeneratedOriginChartFork_interior U i).2
  | .inr (.inl i), .inr (.inl j) => nativeStreamingGeneratedCrossEdgeRecordProjection U
      (printedGeneratedOriginChartEdge U i) (printedGeneratedOriginChartEdge U j) k
  | .inr (.inr _), .inl j => printedGeneratedEndpointCrossRecordProject U ∘
      printedGeneratedCrossVertexRecordProjection (nativeStreamingGeneratedEndpointComponent U)
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U j))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
        (nativeStreamingGeneratedEndpointVertex_interior U (printedGeneratedOriginChartFork U j)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (printedGeneratedOriginChartFork U j)).2
  | .inl i, .inr (.inr _) => printedGeneratedEndpointCrossRecordProject U ∘
      printedGeneratedCrossVertexRecordProjection (nativeStreamingGeneratedEndpointComponent U)
        (nativeStreamingGeneratedEndpointVertex U (printedGeneratedOriginChartFork U i))
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (printedGeneratedOriginChartFork U i)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (printedGeneratedOriginChartFork U i)).2
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
  | .inr (.inl i), .inr (.inr _) => printedGeneratedEndpointCrossRecordProject U ∘
      nativeStreamingGeneratedMixedCrossRecordProjection (nativeStreamingGeneratedEndpointComponent U)
        (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U i))
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
  | .inr (.inr _), .inr (.inl j) => Prod.map id Prod.swap ∘
      printedGeneratedEndpointCrossRecordProject U ∘
        nativeStreamingGeneratedMixedCrossRecordProjection (nativeStreamingGeneratedEndpointComponent U)
          (printedGeneratedEndpointEdge U (printedGeneratedOriginChartEdge U j))
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
          (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
  | .inr (.inr _), .inr (.inr _) => printedGeneratedEndpointCrossRecordProject U ∘
      printedGeneratedCrossVertexRecordProjection (nativeStreamingGeneratedEndpointComponent U)
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2

theorem measurable_printedGeneratedOriginCrossChartRecordProjection {n : ℕ}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    Measurable (printedGeneratedOriginCrossChartRecordProjection
      (E:=AnisotropicObservationState n) (S:=Configuration n) U γ₁ γ₂ k) := by
  rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
  · exact measurable_printedGeneratedCrossVertexRecordProjection _ _ _ _ _ _ _
  · exact (measurable_id.prodMap measurable_swap).comp
      (measurable_nativeStreamingGeneratedMixedCrossRecordProjection _ _ _ _ _)
  · exact (measurable_printedGeneratedEndpointCrossRecordProject U).comp
      (measurable_printedGeneratedCrossVertexRecordProjection _ _ _ _ _ _ _)
  · exact measurable_nativeStreamingGeneratedMixedCrossRecordProjection _ _ _ _ _
  · exact measurable_printedGeneratedCrossEdgeRecordProjection _ _ _ _
  · exact (measurable_printedGeneratedEndpointCrossRecordProject U).comp
      (measurable_nativeStreamingGeneratedMixedCrossRecordProjection _ _ _ _ _)
  · exact (measurable_printedGeneratedEndpointCrossRecordProject U).comp
      (measurable_printedGeneratedCrossVertexRecordProjection _ _ _ _ _ _ _)
  · exact (measurable_id.prodMap measurable_swap).comp
      ((measurable_printedGeneratedEndpointCrossRecordProject U).comp
        (measurable_nativeStreamingGeneratedMixedCrossRecordProjection _ _ _ _ _))
  · exact (measurable_printedGeneratedEndpointCrossRecordProject U).comp
      (measurable_printedGeneratedCrossVertexRecordProjection _ _ _ _ _ _ _)

end QuantitativeFollowup
