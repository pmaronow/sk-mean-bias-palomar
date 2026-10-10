module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsClocks
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsMoments

@[expose] public section

/-! The continuation at a free inserted mark is an actual constructed
genealogy. It uses the coordinate already drawn by the free program, without
another atom draw. All original terminal spins and records are projected by
the genuine unary refinement map. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedEdgeComponent
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (k : NativeStreamingGeneratedVertexKind) : CavityGeneratedConstructedComponent (m+1) where
  depth := (nativeStreamingGeneratedEdgeObservedComponent W e).depth
  tree := finiteCascadeContinuationGraft k.continuation (nativeStreamingGeneratedEdgeVertex W e)
  label := (nativeStreamingGeneratedEdgeObservedComponent W e).label
  terminal_label := (nativeStreamingGeneratedEdgeObservedComponent W e).terminal_label
  initial_label := (nativeStreamingGeneratedEdgeObservedComponent W e).initial_label
  construction := by
    let U := nativeStreamingGeneratedEdgeObservedComponent W e
    let v := nativeStreamingGeneratedEdgeVertex W e
    have hat : cavityGeneratedFiniteClockLabels U.label v.depth=.mark (Fin.last m) :=
      nativeStreamingGeneratedEdgeVertex_label W e
    exact .graft k.continuation v (Fin.last m) hat U.construction
      (k.continuation_constructed (cavityGeneratedFiniteClockLabels U.label) v.depth (Fin.last m) hat)

theorem nativeStreamingGeneratedEdgeComponent_clock
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (k : NativeStreamingGeneratedVertexKind) (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeComponent W e k) H =
      nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e) H := rfl

def nativeStreamingGeneratedEdgeTerminalProject {S : Type}
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) :
    TerminalSpins S (nativeStreamingGeneratedEdgeObservedComponent W e).tree →
      TerminalSpins S W.tree :=
  observationRefinementTerminalProject (nativeStreamingEdgeSubdivision e.depth) W.tree rfl

def nativeStreamingGeneratedEdgeLeaf
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (i : ObservationLeaf W.tree) :
    ObservationLeaf (nativeStreamingGeneratedEdgeObservedComponent W e).tree :=
  observationRefinementLeafEmbed (nativeStreamingEdgeSubdivision e.depth) W.tree i

theorem nativeStreamingGeneratedEdgeTerminalProject_record {E S : Type}
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (z : Records E S (nativeStreamingGeneratedEdgeObservedComponent W e).tree) :
    nativeStreamingGeneratedEdgeTerminalProject W e (finiteCascadeRecordTerminalSpins _ z) =
      finiteCascadeRecordTerminalSpins W.tree
        (observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) W.tree z) :=
  observationRefinementTerminalProject_record _ W.tree rfl z

theorem nativeStreamingGeneratedEdgeTerminalProject_leaf {S : Type}
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (i : ObservationLeaf W.tree)
    (σ : TerminalSpins S (nativeStreamingGeneratedEdgeObservedComponent W e).tree) :
    observationTerminalSpin W.tree i (nativeStreamingGeneratedEdgeTerminalProject W e σ)=
      observationTerminalSpin _ (nativeStreamingGeneratedEdgeLeaf W e i) σ :=
  observationRefinementTerminalProject_leaf _ W.tree rfl i σ

theorem nativeStreamingGeneratedEdgeObserved_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e)
        (Fin.snoc h r)) (nativeStreamingGeneratedEdgeObservedComponent W e).tree).map
          (Prod.map id (observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) W.tree)) =
      anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedComponentClock W h) W.tree := by
  rw [nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr]
  exact anisotropicRecordedProfileTreeLaw_native_edge_insertion D μ a _
    (nativeStreamingGeneratedComponentClock_antitone W h) e.depth r hr W.tree

theorem nativeStreamingGeneratedEdge_selected_clock
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e)
      (Fin.snoc h r) (nativeStreamingGeneratedEdgeVertex W e).depth=r := by
  rw [nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr,
    nativeStreamingGeneratedEdgeVertex_depth,nativeStreamingEdgeSchedule_inserted]

theorem nativeStreamingGeneratedEdge_graft_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (k : NativeStreamingGeneratedVertexKind) (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeComponent W e k) H)
      (nativeStreamingGeneratedEdgeComponent W e k).tree).map
        (fun z => ((z.1,(finiteCascadeContinuationExtract k.continuation k.recordMark
          (nativeStreamingGeneratedEdgeVertex W e) z.2).1),
          (finiteCascadeContinuationExtract k.continuation k.recordMark
            (nativeStreamingGeneratedEdgeVertex W e) z.2).2)) =
      nativeStreamingActualContinuationLaw D μ a
        (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e) H)
        k.continuation k.recordMark (nativeStreamingGeneratedEdgeObservedComponent W e).tree
          (nativeStreamingGeneratedEdgeVertex W e) :=
  nativeStreamingGeneratedVertex_record_law D μ a _ _ _ k

end QuantitativeFollowup
