module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossEdgePatternsConstruction

@[expose] public section

/-! The whole double-graft record law is the genuine chronological two-edge
law. Actual chart membership supplies chronology; no order law is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

private theorem crossEdge_map_comp {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure A) (f : A→B) (g : B→C) (hf : Measurable f) (hg : Measurable g) :
    P.map (g∘f)=(P.map f).map g := (Measure.map_map hg hf).symm

theorem nativeStreamingGeneratedCrossEdge_full_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h e.depth)
    (hl : nativeStreamingGeneratedComponentClock W h (f.depth+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h f.depth)
    (hc : c.Holds e.depth f.depth r l) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedCrossEdgeComponent W e f c)
        (nativeStreamingGeneratedCrossEdgeAppend h r l))
      (nativeStreamingGeneratedCrossEdgeComponent W e f c).tree).map
        (nativeStreamingGeneratedCrossEdgeRecordProjection W e f c)=
      (nativeStreamingEdgePairProbability D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree e f r l : Measure _) := by
  let q := nativeStreamingGeneratedComponentClock W h
  let Q := nativeStreamingPairObservationSchedule q e.depth f.depth r l
  let d := nativeStreamingPairObservationSubdivision
  let v := nativeStreamingGeneratedCrossEdgeFirstVertex W e f c
  let w := nativeStreamingGeneratedCrossEdgeSecondVertex W e f c
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q
    (nativeStreamingGeneratedComponentClock_antitone W h) e.depth f.depth r l hr hl
  have hlevels : ∀j,Q (observationRefinementDepth d j)=q j :=
    nativeStreamingPairObservationSchedule_refinement q e.depth f.depth r l
  have hq0 : q 0=1 := nativeStreamingGeneratedComponentClock_terminal W h
  have hQ0 : Q 0=1 := (hlevels 0).trans hq0
  have hi := c.indices e.depth f.depth r l hc
  have hv : Q (observationRefinementDepth d e.depth+c.firstSlot+1)=r := by
    rw [hi.1]
    exact nativeStreamingPairObservationIndex_level q e.depth f.depth r l
  have hw : Q (observationRefinementDepth d f.depth+c.secondSlot+1)=l := by
    rw [hi.2]
    exact nativeStreamingPairObservationIndex_second_level q e.depth f.depth r l
  let π := fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d W.tree)) ×
        (Configuration n×Configuration n) =>
      ((z.1.1,observationRefinementProject d W.tree z.1.2),z.2)
  let ψ := fun z : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (finiteCascadeCrossContinuationGraft observationLinearTree v w) =>
      ((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).1),
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).2)
  have hπ : Measurable π :=
    (measurable_fst.fst.prodMk ((measurable_observationRefinementProject d W.tree).comp
      measurable_fst.snd)).prodMk measurable_snd
  have he := measurable_finiteCascadeCrossContinuationExtract (E:=AnisotropicObservationState n)
    (S:=Configuration n) observationLinearTree observationLinearSpin
    (fun j => measurable_observationLinearSpin j) v w
  have hψ : Measurable ψ :=
    (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  rw [nativeStreamingGeneratedCrossEdgeComponent_clock,
    nativeStreamingGeneratedCrossEdgeObservedComponent_clock_append W e f c h r l hh hr hl hc]
  change (anisotropicRecordedProfileTreeLaw D μ a Q _).map (π∘ψ)=_
  rw [crossEdge_map_comp _ ψ π hψ hπ,
    nativeStreamingCrossVertexLaw_eq_graft D μ a Q hQ hQ0]
  rw [←nativeStreamingCrossVertexProbability_eq_law D μ a Q hQ hQ0]
  have H := nativeStreamingEdgePairProbability_refinement_physical D μ a q Q d
    (nativeStreamingGeneratedComponentClock_antitone W h) hq0 hQ hlevels W.tree e f
    c.firstSlot c.secondSlot c.firstSlot_lt c.secondSlot_lt r l hr hl hv hw
  exact congrArg (fun P : ProbabilityMeasure ((AnisotropicObservationState n ×
    Records (AnisotropicObservationState n) (Configuration n) W.tree) × (Configuration n×Configuration n)) =>
      P.toMeasure) H

theorem nativeStreamingGeneratedCrossEdge_common_clock
    (W : CavityGeneratedConstructedComponent m) (e f : NativeStreamingEdge W.tree)
    (c : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h e.depth)
    (hl : nativeStreamingGeneratedComponentClock W h (f.depth+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h f.depth)
    (hc : c.Holds e.depth f.depth r l) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedCrossEdgeComponent W e f c)
      (nativeStreamingGeneratedCrossEdgeAppend h r l)
      (observationCommonLevel _
        (finiteCascadeLinearCrossFirstLeaf (nativeStreamingGeneratedCrossEdgeFirstVertex W e f c)
          (nativeStreamingGeneratedCrossEdgeSecondVertex W e f c))
        (finiteCascadeLinearCrossSecondLeaf (nativeStreamingGeneratedCrossEdgeFirstVertex W e f c)
          (nativeStreamingGeneratedCrossEdgeSecondVertex W e f c)))=
      nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock W h) W.tree (.edge e r) (.edge f l) := by
  rw [finiteCascadeLinearCrossFresh_commonLevel,nativeStreamingGeneratedCrossEdgeComponent_clock,
    nativeStreamingGeneratedCrossEdgeObservedComponent_clock_append W e f c h r l hh hr hl hc]
  let q := nativeStreamingGeneratedComponentClock W h
  let Q := nativeStreamingPairObservationSchedule q e.depth f.depth r l
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q
    (nativeStreamingGeneratedComponentClock_antitone W h) e.depth f.depth r l hr hl
  have hi := c.indices e.depth f.depth r l hc
  have H := nativeStreamingEdgeSelectedVertex_commonPathClock nativeStreamingPairObservationSubdivision q Q
    hQ W.tree (fun j _ => nativeStreamingPairObservationSchedule_refinement q e.depth f.depth r l j)
    e f c.firstSlot c.secondSlot c.firstSlot_lt c.secondSlot_lt
  change Q (finiteCascadeCommonPathDepth (observationRefineTree nativeStreamingPairObservationSubdivision W.tree)
    (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e c.firstSlot)
    (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f c.secondSlot))=
      nativeStreamingOriginCommonClock q W.tree (.edge e r) (.edge f l)
  have hv : Q (observationRefinementDepth nativeStreamingPairObservationSubdivision e.depth+c.firstSlot+1)=r := by
    rw [hi.1]
    exact nativeStreamingPairObservationIndex_level q e.depth f.depth r l
  have hw : Q (observationRefinementDepth nativeStreamingPairObservationSubdivision f.depth+c.secondSlot+1)=l := by
    rw [hi.2]
    exact nativeStreamingPairObservationIndex_second_level q e.depth f.depth r l
  simpa only [nativeStreamingGeneratedCrossEdgeFirstVertex,nativeStreamingGeneratedCrossEdgeSecondVertex,
    nativeStreamingOriginCommonClock,hv,hw] using H

end QuantitativeFollowup
