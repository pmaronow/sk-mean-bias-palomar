module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexSourceDerivatives
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternTerminalRepresentationFuture

@[expose] public section

/-! Genuine first parameter derivatives of edge and shared-future
integrands. The concrete refined tree and its terminal test are held
fixed while only the actual cavity model varies. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J K : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem hasDerivWithinAt_nativeStreamingPattern_of_refined_terminalRepresentation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q Q : ℕ → Paper.Overlap) (hQ : Antitone Q) (hK : 0<K)
    (hzero : (Q 0:ℝ)=1) (htop : (Q K:ℝ)=0)
    (T : FiniteTerminalGenealogy J) (U : FiniteTerminalGenealogy K)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (P : NativeStreamingAttachmentPattern T)
    (G : TerminalSpins (Configuration (n+1)) U → ℝ)
    (hrep : ∀D : AnisotropicSpinModel (n+1),
      nativeStreamingPatternMoment D μ a q T F P =
        nativeStreamingOldTerminalExpectation D μ a Q U G)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F P)
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a Q U G) (Icc (0:ℝ) 1) u := by
  apply (hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
    Q hQ hK hzero htop U G u hu).congr_of_mem ?_ hu
  intro v hv
  simp only [nativeStreamingPatternParameterMoment,dif_pos hv]
  exact (hrep _).trans (followupCavityNativeTerminalExpectation_eq_old_terminal
    (n:=n) β ρ hβ hρ μ a Q U G v hv).symm

theorem hasDerivWithinAt_nativeStreamingPattern_originalFresh_edge_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (e : NativeStreamingEdge T) (r : Paper.Overlap)    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.originalFresh i (.edge e r)))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a (nativeStreamingEdgeSchedule q e.depth r)
        (finiteCascadeContinuationGraft observationLinearTree
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e))
        (nativeStreamingPatternRefinedVertexTerminalTest .single (nativeStreamingEdgeSubdivision e.depth)
          T (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingOriginalFreshSpinTest T F i
            (nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i)) (.edge e r))))) (Icc (0:ℝ) 1) u := by
  let d := nativeStreamingEdgeSubdivision e.depth
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hK : 0<observationRefinementDepth d J := by
    simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
  have hQzero : (Q 0:ℝ)=1 := by
    simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
  have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
    simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
  exact hasDerivWithinAt_nativeStreamingPattern_of_refined_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q Q hQ hK hQzero hQtop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_originalFresh_edge_terminalRepresentation D μ a q T F i e r) u hu

theorem hasDerivWithinAt_nativeStreamingPattern_current_edge_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (r : Paper.Overlap)    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.current (.edge e r)))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a (nativeStreamingEdgeSchedule q e.depth r)
        (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e))
        (nativeStreamingPatternRefinedVertexTerminalTest .current (nativeStreamingEdgeSubdivision e.depth)
          T (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingDefectSpinTest T F r))) (Icc (0:ℝ) 1) u := by
  let d := nativeStreamingEdgeSubdivision e.depth
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hK : 0<observationRefinementDepth d J := by
    simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
  have hQzero : (Q 0:ℝ)=1 := by
    simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
  have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
    simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
  exact hasDerivWithinAt_nativeStreamingPattern_of_refined_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q Q hQ hK hQzero hQtop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_current_edge_terminalRepresentation D μ a q T F e r) u hu

theorem hasDerivWithinAt_nativeStreamingPattern_cross_edge_vertex_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap)    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.edge e r) (.vertex v)))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a (nativeStreamingEdgeSchedule q e.depth r)
        (finiteCascadeCrossContinuationGraft observationLinearTree
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v))
        (nativeStreamingPatternRefinedCrossTerminalTest (nativeStreamingEdgeSubdivision e.depth) T
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v)
          (nativeStreamingDefectSpinTest T F
            (nativeStreamingOriginCommonClock q T (.edge e r) (.vertex v))))) (Icc (0:ℝ) 1) u := by
  let d := nativeStreamingEdgeSubdivision e.depth
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hK : 0<observationRefinementDepth d J := by
    simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
  have hQzero : (Q 0:ℝ)=1 := by
    simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
  have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
    simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
  exact hasDerivWithinAt_nativeStreamingPattern_of_refined_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q Q hQ hK hQzero hQtop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_cross_edge_vertex_terminalRepresentation D μ a q T F e v r) u hu

theorem hasDerivWithinAt_nativeStreamingPattern_cross_vertex_edge_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T) (r : Paper.Overlap)    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.vertex v) (.edge e r)))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a (nativeStreamingEdgeSchedule q e.depth r)
        (finiteCascadeCrossContinuationGraft observationLinearTree
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v))
        (nativeStreamingPatternRefinedCrossTerminalTest (nativeStreamingEdgeSubdivision e.depth) T
          (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v)
          (nativeStreamingDefectSpinTest T F
            (nativeStreamingOriginCommonClock q T (.edge e r) (.vertex v))))) (Icc (0:ℝ) 1) u := by
  let d := nativeStreamingEdgeSubdivision e.depth
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hK : 0<observationRefinementDepth d J := by
    simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
  have hQzero : (Q 0:ℝ)=1 := by
    simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
  have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
    simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
  exact hasDerivWithinAt_nativeStreamingPattern_of_refined_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q Q hQ hK hQzero hQtop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_cross_vertex_edge_terminalRepresentation D μ a q T F v e r) u hu

theorem hasDerivWithinAt_nativeStreamingPattern_cross_edges_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e f : NativeStreamingEdge T) (r l : Paper.Overlap)    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hl : q (f.depth+1)≤l ∧ l≤q f.depth)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.edge e r) (.edge f l)))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a
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
            (nativeStreamingOriginCommonClock q T (.edge e r) (.edge f l))))) (Icc (0:ℝ) 1) u := by
  let d := nativeStreamingPairObservationSubdivision
  let Q := nativeStreamingPairObservationSchedule q e.depth f.depth r l
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq e.depth f.depth r l hr hl
  have hK : 0<observationRefinementDepth d J := by
    simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
  have hQzero : (Q 0:ℝ)=1 := by
    simpa only [Q,nativeStreamingPairObservationSchedule,Nat.zero_mod,Nat.zero_div,ite_true] using hzero
  have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
    simpa only [Q,d,nativeStreamingPairObservationSchedule_refinement] using htop
  exact hasDerivWithinAt_nativeStreamingPattern_of_refined_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q Q hQ hK hQzero hQtop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_cross_edges_terminalRepresentation D μ a q T F e f r l) u hu

theorem hasDerivWithinAt_nativeStreamingPattern_future_vertex_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) (j : ℕ) (l : Paper.Overlap)    (hl : q (j+1)≤l ∧ l≤q j)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.future (.vertex v) j l))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a (nativeStreamingEdgeSchedule q j l)
        (finiteCascadeFutureVertexGraft
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T v) (j+1))
        (nativeStreamingPatternRefinedPairTerminalTest (nativeStreamingEdgeSubdivision j) T
          (finiteCascadeFuturePairTree (j+1))
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T v)
          (nativeStreamingDefectSpinTest T F l))) (Icc (0:ℝ) 1) u := by
  let d := nativeStreamingEdgeSubdivision j
  let Q := nativeStreamingEdgeSchedule q j l
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq j l hl
  have hK : 0<observationRefinementDepth d J := by
    simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
  have hQzero : (Q 0:ℝ)=1 := by
    simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
  have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
    simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
  exact hasDerivWithinAt_nativeStreamingPattern_of_refined_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q Q hQ hK hQzero hQtop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_future_vertex_terminalRepresentation D μ a q T F v j l) u hu

theorem hasDerivWithinAt_nativeStreamingPattern_future_edge_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (r : Paper.Overlap) (j : ℕ) (l : Paper.Overlap)    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hl : q (j+1)≤l ∧ l≤q j)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.future (.edge e r) j l))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a
        (nativeStreamingPairObservationSchedule q e.depth j r l)
        (finiteCascadeFutureVertexGraft
          (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
            (nativeStreamingPairObservationIndex e.depth j r l))
          (observationRefinementDepth nativeStreamingPairObservationSubdivision j +
            nativeStreamingPairObservationIndex j e.depth l r + 1))
        (nativeStreamingPatternRefinedPairTerminalTest nativeStreamingPairObservationSubdivision T
          (finiteCascadeFuturePairTree (observationRefinementDepth nativeStreamingPairObservationSubdivision j +
            nativeStreamingPairObservationIndex j e.depth l r + 1))
          (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e
            (nativeStreamingPairObservationIndex e.depth j r l)) (nativeStreamingDefectSpinTest T F l))) (Icc (0:ℝ) 1) u := by
  let d := nativeStreamingPairObservationSubdivision
  let Q := nativeStreamingPairObservationSchedule q e.depth j r l
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq e.depth j r l hr hl
  have hK : 0<observationRefinementDepth d J := by
    simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
  have hQzero : (Q 0:ℝ)=1 := by
    simpa only [Q,nativeStreamingPairObservationSchedule,Nat.zero_mod,Nat.zero_div,ite_true] using hzero
  have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
    simpa only [Q,d,nativeStreamingPairObservationSchedule_refinement] using htop
  exact hasDerivWithinAt_nativeStreamingPattern_of_refined_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q Q hQ hK hQzero hQtop T _ F _ _
    (fun D=>nativeStreamingPatternMoment_future_edge_terminalRepresentation D μ a q T F e r j l) u hu

end QuantitativeFollowup
