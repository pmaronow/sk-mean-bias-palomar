module
public import QuantitativeFollowup.SupportingGeneratedOriginComponentCharts
public import QuantitativeFollowup.FollowupCavityGeneratedForestComponentReplacementRetained
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsMoments

@[expose] public section

/-! The finite origin charts have explicit full-record projections.  The
selected clock is attached to the actual continuation genealogy; every
old field and terminal spin is retained by the corresponding projection. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m J : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def printedGeneratedOriginChartOrigin (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (r : Paper.Overlap) : NativeStreamingOrigin U.tree :=
  match γ with
  | .inl i => .vertex (printedGeneratedOriginChartFork U i)
  | .inr (.inl i) => .edge (printedGeneratedOriginChartEdge U i) r
  | .inr (.inr _) => .vertex (.root U.tree)

def printedGeneratedOriginKindProbability (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (o : NativeStreamingOrigin T)
    (k : NativeStreamingGeneratedVertexKind) :
    ProbabilityMeasure ((AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
        k.Mark (Configuration (n+1))) := match k with
  | .single => nativeStreamingOriginSingleProbability D μ a q T o
  | .current => nativeStreamingOriginCurrentProbability D μ a q T o

def printedGeneratedVertexMarkedRecordProject (k : NativeStreamingGeneratedVertexKind)
    {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T)
    (z : AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
        (finiteCascadeContinuationGraft k.continuation v)) :
    (AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
        k.Mark (Configuration (n+1)) :=
  ((z.1,(finiteCascadeContinuationExtract k.continuation k.recordMark v z.2).1),
    (finiteCascadeContinuationExtract k.continuation k.recordMark v z.2).2)

theorem measurable_printedGeneratedVertexMarkedRecordProject
    (k : NativeStreamingGeneratedVertexKind) {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) :
    Measurable (printedGeneratedVertexMarkedRecordProject (n:=n) k v) := by
  have he := measurable_finiteCascadeContinuationExtract
    (E:=AnisotropicObservationState (n+1)) (S:=Configuration (n+1))
    k.continuation k.recordMark (fun j => k.recordMark_measurable j) v
  exact (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk
    (he.snd.comp measurable_snd)

def printedGeneratedOriginChartRecordProject (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (k : NativeStreamingGeneratedVertexKind) :
    PrintedGeneratedComponentRecord n (printedGeneratedOriginChartComponent U γ k) →
      PrintedGeneratedComponentRecord n U × k.Mark (Configuration (n+1)) :=
  match γ with
  | .inl i => printedGeneratedVertexMarkedRecordProject k (printedGeneratedOriginChartFork U i)
  | .inr (.inl i) => fun z =>
      let x := printedGeneratedVertexMarkedRecordProject k
        (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i)) z
      ((x.1.1,observationRefinementProject
        (nativeStreamingEdgeSubdivision (printedGeneratedOriginChartEdge U i).depth) U.tree x.1.2),x.2)
  | .inr (.inr _) => fun z =>
      let x := printedGeneratedVertexMarkedRecordProject k
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree)) z
      ((x.1.1,nativeStreamingGeneratedEndpointRecordProject U x.1.2),x.2)

theorem measurable_printedGeneratedOriginChartRecordProject
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) :
    Measurable (printedGeneratedOriginChartRecordProject (n:=n) U γ k) := by
  rcases γ with i | (i | u)
  · exact measurable_printedGeneratedVertexMarkedRecordProject k _
  · have hp := measurable_printedGeneratedVertexMarkedRecordProject (n:=n) k
      (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i))
    have hr := measurable_observationRefinementProject
      (E:=AnisotropicObservationState (n+1)) (S:=Configuration (n+1))
      (nativeStreamingEdgeSubdivision (printedGeneratedOriginChartEdge U i).depth) U.tree
    exact (hp.fst.fst.prodMk (hr.comp hp.fst.snd)).prodMk hp.snd
  · have hp := measurable_printedGeneratedVertexMarkedRecordProject (n:=n) k
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
    have hr := measurable_nativeStreamingGeneratedEndpointRecordProject
      (E:=AnisotropicObservationState (n+1)) (S:=Configuration (n+1)) U
    exact (hp.fst.fst.prodMk (hr.comp hp.fst.snd)).prodMk hp.snd

theorem printedGeneratedVertexComponent_snoc_clock
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (k : NativeStreamingGeneratedVertexKind)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent U v hv0 hvJ k)
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth)) =
        nativeStreamingGeneratedComponentClock U h := by
  funext j
  change cavityGeneratedClippedClock
    (fun p => (cavityGeneratedFiniteClockLabels
      (nativeStreamingGeneratedVertexComponent U v hv0 hvJ k).label p).value
        (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth))) j = _
  have he := funext (printedGeneratedVertexComponent_snoc_raw U v hv0 hvJ k h hh)
  rw [he]
  exact cavityGeneratedClippedClock_eq _ j
    (fun p _ => nativeStreamingGeneratedComponentClock_antitone U h (Nat.le_succ p)) j le_rfl

theorem printedGeneratedVertexMarkedRecordProject_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (k : NativeStreamingGeneratedVertexKind) :
    (anisotropicRecordedProfileTreeLaw D μ a q (finiteCascadeContinuationGraft k.continuation v)).map
      (printedGeneratedVertexMarkedRecordProject k v) =
      (printedGeneratedOriginKindProbability D μ a q T (.vertex v) k :
        Measure ((AnisotropicObservationState (n+1) ×
          Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
            k.Mark (Configuration (n+1)))) := by
  cases k <;> rfl

end QuantitativeFollowup
