module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossEdgePatternsClocks
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossVertexPatternsTerminal
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedCrossPatternMoments

@[expose] public section

/-! Actual double continuations at the two fixed chart slots. Both new spins
are retained even when the original edges and inserted physical times coincide. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedCrossEdgeFirstVertex
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) :
    FiniteCascadeRecordVertex (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c).tree :=
  nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e c.firstSlot

def nativeStreamingGeneratedCrossEdgeSecondVertex
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) :
    FiniteCascadeRecordVertex (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c).tree :=
  nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f c.secondSlot

theorem crossEdge_first_label_is_mark
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) :
    ∃i, cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c).label
      (nativeStreamingGeneratedCrossEdgeFirstVertex W e f c).depth=.mark i := by
  change ∃i, cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedCrossEdgeLabels W e f c) _=.mark i
  rw [nativeStreamingGeneratedCrossEdgeLabels_global]
  change ∃i, nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c
    (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e c.firstSlot).depth=.mark i
  rw [nativeStreamingEdgeSelectedVertex_depth _ e c.firstSlot c.firstSlot_lt,
    nativeStreamingPairObservationSubdivision_depth]
  cases c <;> simp only [NativeStreamingGeneratedCrossEdgeChart.firstSlot]
  all_goals
    have hdiv : (3*e.depth+1)/3=e.depth := by omega
    have hdiv2 : (3*e.depth+2)/3=e.depth := by omega
    have hmod : (3*e.depth+1)%3=1 := by omega
    have hmod2 : (3*e.depth+2)%3=2 := by omega
    simp [nativeStreamingGeneratedCrossEdgeGlobalLabels,hdiv,hdiv2,hmod,hmod2,Nat.add_assoc]

theorem crossEdge_second_label_is_mark
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) :
    ∃i, cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c).label
      (nativeStreamingGeneratedCrossEdgeSecondVertex W e f c).depth=.mark i := by
  change ∃i, cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedCrossEdgeLabels W e f c) _=.mark i
  rw [nativeStreamingGeneratedCrossEdgeLabels_global]
  change ∃i, nativeStreamingGeneratedCrossEdgeGlobalLabels W e f c
    (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f c.secondSlot).depth=.mark i
  rw [nativeStreamingEdgeSelectedVertex_depth _ f c.secondSlot c.secondSlot_lt,
    nativeStreamingPairObservationSubdivision_depth]
  cases c <;> simp only [NativeStreamingGeneratedCrossEdgeChart.secondSlot]
  all_goals
    have hdiv : (3*f.depth+1)/3=f.depth := by omega
    have hdiv2 : (3*f.depth+2)/3=f.depth := by omega
    have hmod : (3*f.depth+1)%3=1 := by omega
    have hmod2 : (3*f.depth+2)%3=2 := by omega
    simp only [nativeStreamingGeneratedCrossEdgeGlobalLabels,Nat.add_zero,Nat.zero_add,
      hdiv,hdiv2,hmod,hmod2,Nat.add_assoc]
    split_ifs <;> first | exact ⟨_,rfl⟩ | simp_all

def nativeStreamingGeneratedCrossEdgeComponent
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) : CavityGeneratedConstructedComponent (m+2) where
  depth := (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c).depth
  tree := finiteCascadeCrossContinuationGraft observationLinearTree
    (nativeStreamingGeneratedCrossEdgeFirstVertex W e f c)
    (nativeStreamingGeneratedCrossEdgeSecondVertex W e f c)
  label := (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c).label
  terminal_label := (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c).terminal_label
  initial_label := (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c).initial_label
  construction := by
    let U := nativeStreamingGeneratedCrossEdgeObservedComponent W e f c
    let v := nativeStreamingGeneratedCrossEdgeFirstVertex W e f c
    let w := nativeStreamingGeneratedCrossEdgeSecondVertex W e f c
    obtain ⟨i,hi⟩ := crossEdge_first_label_is_mark W e f c
    obtain ⟨k,hk⟩ := crossEdge_second_label_is_mark W e f c
    have hv : CavityGeneratedGenealogyConstruction (cavityGeneratedFiniteClockLabels U.label)
        (finiteCascadeContinuationGraft observationLinearTree v) :=
      .graft observationLinearTree v i hi U.construction
        (NativeStreamingGeneratedVertexKind.single.continuation_constructed _ _ _ hi)
    exact .graft observationLinearTree
      (finiteCascadeContinuationVertexEmbed observationLinearTree v w) k
      (by simpa only [finiteCascadeContinuationVertexEmbed_depth] using hk) hv
      (NativeStreamingGeneratedVertexKind.single.continuation_constructed _ _ _
        (by simpa only [finiteCascadeContinuationVertexEmbed_depth] using hk))

theorem nativeStreamingGeneratedCrossEdgeComponent_clock
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart) (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedCrossEdgeComponent W e f c) H=
      nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedCrossEdgeObservedComponent W e f c) H := rfl

def nativeStreamingGeneratedCrossEdgeRecordProjection {E S : Type}
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (z : E × Records E S (nativeStreamingGeneratedCrossEdgeComponent W e f c).tree) :
    (E × Records E S W.tree) × (S×S) :=
  let y := finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin
    (nativeStreamingGeneratedCrossEdgeFirstVertex W e f c)
    (nativeStreamingGeneratedCrossEdgeSecondVertex W e f c) z.2
  ((z.1,observationRefinementProject nativeStreamingPairObservationSubdivision W.tree y.1),y.2)

def nativeStreamingGeneratedCrossEdgeTerminalProjection {S : Type}
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (σ : TerminalSpins S (nativeStreamingGeneratedCrossEdgeComponent W e f c).tree) :
    TerminalSpins S W.tree × (S×S) :=
  let y := nativeStreamingGeneratedCrossVertexTerminalProjection
    (nativeStreamingGeneratedCrossEdgeFirstVertex W e f c)
    (nativeStreamingGeneratedCrossEdgeSecondVertex W e f c) σ
  (observationRefinementTerminalProject nativeStreamingPairObservationSubdivision W.tree rfl y.1,y.2)

theorem nativeStreamingGeneratedCrossEdgeTerminalProjection_record {E S : Type}
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (z : E × Records E S (nativeStreamingGeneratedCrossEdgeComponent W e f c).tree) :
    nativeStreamingGeneratedCrossEdgeTerminalProjection W e f c (finiteCascadeRecordTerminalSpins _ z.2)=
      (finiteCascadeRecordTerminalSpins W.tree (nativeStreamingGeneratedCrossEdgeRecordProjection W e f c z).1.2,
        (nativeStreamingGeneratedCrossEdgeRecordProjection W e f c z).2) := by
  let v := nativeStreamingGeneratedCrossEdgeFirstVertex W e f c
  let w := nativeStreamingGeneratedCrossEdgeSecondVertex W e f c
  let y := finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2
  have H := nativeStreamingGeneratedCrossVertexTerminalProjection_record v w z.2
  have H' := congrArg (fun t =>
    (observationRefinementTerminalProject nativeStreamingPairObservationSubdivision W.tree rfl t.1,t.2)) H
  apply H'.trans
  exact congrArg (fun σ => (σ,y.2))
    (observationRefinementTerminalProject_record nativeStreamingPairObservationSubdivision W.tree rfl y.1)

end QuantitativeFollowup
