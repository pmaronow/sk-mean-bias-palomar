module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternTerminalRepresentation
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossOriginMoments
public import FourPapersCommon.FiniteObservationRefinementTerminalLeaves

@[expose] public section

/-! A genuine refinement map retains every old terminal coordinate.
Combining it with the actual continuation laws realizes each edge-mark
pattern as a finite terminal test on a concrete enlarged native tree.
Canonical two-slot indices are kept, including coincident clocks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingPatternRefinementTerminalProject_record {E S : Type}
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (z : Records E S (observationRefineTree d T)) :
    observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z) =
        finiteCascadeRecordTerminalSpins T (observationRefinementProject d T z) := by
  simpa only [observationTreeDepthCast, observationRefinementDepthProject,
    observationRecordDepthCast, Function.comp_apply, id_eq] using
    observationRefinementTerminalProject_record d T rfl z

def nativeStreamingPatternRefinedMarkedTest {A : Type}
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (G : TerminalSpins (Configuration n) T × A → ℝ) :
    TerminalSpins (Configuration n) (observationRefineTree d T) × A → ℝ :=
  fun z => G (observationRefinementTerminalProject d T rfl z.1,z.2)

theorem nativeStreamingPatternTerminalMarkMoment_refinement_map {A : Type}
    [Fintype A] [MeasurableSpace A] [TopologicalSpace A] [DiscreteTopology A]
    [BorelSpace A] [SecondCountableTopology A]
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (P : ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) × A))
    (G : TerminalSpins (Configuration n) T × A → ℝ) :
    nativeStreamingTerminalMarkMoment
      (P.map (fun z => ((z.1.1,observationRefinementProject d T z.1.2),z.2))) G =
      nativeStreamingTerminalMarkMoment P (nativeStreamingPatternRefinedMarkedTest d T G) := by
  have hm : Measurable (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) × A) =>
      ((z.1.1,observationRefinementProject d T z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk ((measurable_observationRefinementProject d T).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hc : Continuous (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × A) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f:=G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk continuous_snd)
  unfold nativeStreamingTerminalMarkMoment
  rw [ProbabilityMeasure.toMeasure_map,integral_map hm.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G
    (Prod.ext (nativeStreamingPatternRefinementTerminalProject_record d T z.1.2).symm rfl)

def nativeStreamingPatternRefinedVertexTerminalTest
    (k : NativeStreamingGeneratedVertexKind) (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T))
    (G : TerminalSpins (Configuration n) T × k.Mark (Configuration n) → ℝ) :=
  nativeStreamingPatternVertexTerminalTest k (observationRefineTree d T) v
    (nativeStreamingPatternRefinedMarkedTest d T G)

def nativeStreamingPatternRefinedCrossTerminalTest
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex (observationRefineTree d T))
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :=
  nativeStreamingPatternCrossTerminalTest (observationRefineTree d T) v w
    (nativeStreamingPatternRefinedMarkedTest d T G)

theorem nativeStreamingRefinedContinuationMoment_eq_oldTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T))
    (k : NativeStreamingGeneratedVertexKind)
    (G : TerminalSpins (Configuration (n+1)) T × k.Mark (Configuration (n+1)) → ℝ) :
    nativeStreamingTerminalMarkMoment
      ((nativeStreamingActualContinuationProbability D μ a Q k.continuation k.recordMark
        (observationRefineTree d T) v).map
          (fun z => ((z.1.1,observationRefinementProject d T z.1.2),z.2))) G =
      nativeStreamingOldTerminalExpectation D μ a Q
        (finiteCascadeContinuationGraft k.continuation v)
        (nativeStreamingPatternRefinedVertexTerminalTest k d T v G) := by
  rw [nativeStreamingPatternTerminalMarkMoment_refinement_map]
  exact nativeStreamingActualContinuationTerminalMoment_eq_oldTerminalExpectation
    D μ a Q (observationRefineTree d T) v k _

theorem nativeStreamingRefinedCrossMoment_eq_oldTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex (observationRefineTree d T))
    (G : TerminalSpins (Configuration (n+1)) T ×
      (Configuration (n+1) × Configuration (n+1)) → ℝ) :
    nativeStreamingTerminalMarkMoment
      ((nativeStreamingCrossVertexProbability D μ a Q (observationRefineTree d T) v w).map
        (fun z => ((z.1.1,observationRefinementProject d T z.1.2),z.2))) G =
      nativeStreamingOldTerminalExpectation D μ a Q
        (finiteCascadeCrossContinuationGraft observationLinearTree v w)
        (nativeStreamingPatternRefinedCrossTerminalTest d T v w G) := by
  rw [nativeStreamingPatternTerminalMarkMoment_refinement_map]
  exact nativeStreamingCrossVertexTerminalMoment_eq_oldTerminalExpectation
    D μ a Q (observationRefineTree d T) v w _

theorem nativeStreamingPatternMoment_originalFresh_edge_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (e : NativeStreamingEdge T) (r : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.edge e r)) =
      nativeStreamingOldTerminalExpectation D μ a (nativeStreamingEdgeSchedule q e.depth r)
        (finiteCascadeContinuationGraft observationLinearTree
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e))
        (nativeStreamingPatternRefinedVertexTerminalTest .single (nativeStreamingEdgeSubdivision e.depth)
          T (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingOriginalFreshSpinTest T F i
            (nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i)) (.edge e r)))) := by
  exact nativeStreamingRefinedContinuationMoment_eq_oldTerminalExpectation D μ a
    (nativeStreamingEdgeSchedule q e.depth r) (nativeStreamingEdgeSubdivision e.depth) T
    (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e) .single _

theorem nativeStreamingPatternMoment_current_edge_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (r : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.current (.edge e r)) =
      nativeStreamingOldTerminalExpectation D μ a (nativeStreamingEdgeSchedule q e.depth r)
        (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e))
        (nativeStreamingPatternRefinedVertexTerminalTest .current (nativeStreamingEdgeSubdivision e.depth)
          T (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingDefectSpinTest T F r)) := by
  exact nativeStreamingRefinedContinuationMoment_eq_oldTerminalExpectation D μ a
    (nativeStreamingEdgeSchedule q e.depth r) (nativeStreamingEdgeSubdivision e.depth) T
    (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e) .current _

theorem nativeStreamingPatternMoment_cross_edge_vertex_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.vertex v)) =
      nativeStreamingOldTerminalExpectation D μ a (nativeStreamingEdgeSchedule q e.depth r)
        (finiteCascadeCrossContinuationGraft observationLinearTree
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v))
        (nativeStreamingPatternRefinedCrossTerminalTest (nativeStreamingEdgeSubdivision e.depth) T
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v)
          (nativeStreamingDefectSpinTest T F
            (nativeStreamingOriginCommonClock q T (.edge e r) (.vertex v)))) := by
  exact nativeStreamingRefinedCrossMoment_eq_oldTerminalExpectation D μ a
    (nativeStreamingEdgeSchedule q e.depth r) (nativeStreamingEdgeSubdivision e.depth) T _ _ _

theorem nativeStreamingPatternMoment_cross_vertex_edge_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T) (r : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.edge e r)) =
      nativeStreamingOldTerminalExpectation D μ a (nativeStreamingEdgeSchedule q e.depth r)
        (finiteCascadeCrossContinuationGraft observationLinearTree
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v))
        (nativeStreamingPatternRefinedCrossTerminalTest (nativeStreamingEdgeSubdivision e.depth) T
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v)
          (nativeStreamingDefectSpinTest T F
            (nativeStreamingOriginCommonClock q T (.edge e r) (.vertex v)))) := by
  rw [nativeStreamingPatternMoment_cross_vertex_edge]
  exact nativeStreamingPatternMoment_cross_edge_vertex_terminalRepresentation D μ a q T F e v r

theorem nativeStreamingPatternMoment_cross_edges_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e f : NativeStreamingEdge T) (r l : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.edge f l)) =
      nativeStreamingOldTerminalExpectation D μ a
        (nativeStreamingPairObservationSchedule q e.depth f.depth r l)
        (finiteCascadeCrossContinuationGraft observationLinearTree
          (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
            (nativeStreamingPairObservationIndex e.depth f.depth r l))
          (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f
            (nativeStreamingPairObservationIndex f.depth e.depth l r)))
        (nativeStreamingPatternRefinedCrossTerminalTest nativeStreamingPairObservationSubdivision T
          (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
            (nativeStreamingPairObservationIndex e.depth f.depth r l))
          (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f
            (nativeStreamingPairObservationIndex f.depth e.depth l r))
          (nativeStreamingDefectSpinTest T F
            (nativeStreamingOriginCommonClock q T (.edge e r) (.edge f l)))) := by
  exact nativeStreamingRefinedCrossMoment_eq_oldTerminalExpectation D μ a
    (nativeStreamingPairObservationSchedule q e.depth f.depth r l)
    nativeStreamingPairObservationSubdivision T _ _ _

end QuantitativeFollowup
