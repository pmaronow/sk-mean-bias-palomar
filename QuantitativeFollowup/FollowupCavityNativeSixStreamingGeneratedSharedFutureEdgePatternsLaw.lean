module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFutureEdgePatternsClocks
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginFuture

@[expose] public section

/-! The actual edge-origin future genealogy retains the complete original
record and two descendants of its sampled shared split. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

private theorem sharedFutureEdge_map_graft_project {E S B : Type}
    [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace B]
    {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) (p : ℕ)
    (f : Records E S T → B) (hf : Measurable f)
    (Q : Measure (E × Records E S (finiteCascadeFutureVertexGraft v p))) :
    Q.map (fun z => ((z.1,f (finiteCascadeFutureGraftExtract v p z.2).1),
      (finiteCascadeFutureGraftExtract v p z.2).2)) =
      (Q.map (fun z => ((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
        (finiteCascadeFutureGraftExtract v p z.2).2))).map
          (fun z => ((z.1.1,f z.1.2),z.2)) := by
  have hx : Measurable (fun z : E × Records E S (finiteCascadeFutureVertexGraft v p) =>
      ((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
        (finiteCascadeFutureGraftExtract v p z.2).2)) :=
    (measurable_fst.prodMk ((measurable_finiteCascadeFutureGraftExtract v p).fst.comp
      measurable_snd)).prodMk ((measurable_finiteCascadeFutureGraftExtract v p).snd.comp measurable_snd)
  have hp : Measurable (fun z : (E × Records E S T) × (S × S) =>
      ((z.1.1,f z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk (hf.comp measurable_fst.snd)).prodMk measurable_snd
  simpa only [Function.comp_def] using (Measure.map_map (μ:=Q) hp hx).symm

def nativeStreamingGeneratedSharedFutureEdgeRecordProject
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    (AnisotropicObservationState n × Records (AnisotropicObservationState n) (Configuration n)
      (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree) →
      ((AnisotropicObservationState n × Records (AnisotropicObservationState n) (Configuration n) W.tree) ×
        (Configuration n × Configuration n)) :=
  fun z => ((z.1,observationRefinementProject nativeStreamingPairObservationSubdivision W.tree
    (finiteCascadeFutureGraftExtract (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
      (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) z.2).1),
    (finiteCascadeFutureGraftExtract (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
      (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) z.2).2)

theorem measurable_nativeStreamingGeneratedSharedFutureEdgeRecordProject
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    Measurable (nativeStreamingGeneratedSharedFutureEdgeRecordProject (n:=n) W e j hj) := by
  exact (measurable_fst.prodMk
    ((measurable_observationRefinementProject nativeStreamingPairObservationSubdivision W.tree).comp
      ((measurable_finiteCascadeFutureGraftExtract
        (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
        (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)).fst.comp measurable_snd))).prodMk
    ((measurable_finiteCascadeFutureGraftExtract
      (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
      (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)).snd.comp measurable_snd)

def nativeStreamingGeneratedSharedFutureEdgeProbability
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) W.tree) ×
        (Configuration n × Configuration n)) :=
  (nativeStreamingActualContinuationProbability D μ a
    (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj) H)
    (fun d => (finiteCascadeFuturePairTree (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) d).tree)
    (fun d => (finiteCascadeFuturePairTree (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j) d).spins)
    (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj).tree
    (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)).map
      (fun z => ((z.1.1,observationRefinementProject nativeStreamingPairObservationSubdivision W.tree z.1.2),z.2))

theorem nativeStreamingGeneratedSharedFutureEdgeComponent_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj) H)
      (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree).map
        (nativeStreamingGeneratedSharedFutureEdgeRecordProject W e j hj) =
      (nativeStreamingGeneratedSharedFutureEdgeProbability D μ a W e j hj H : Measure
        ((AnisotropicObservationState n × Records (AnisotropicObservationState n) (Configuration n) W.tree) ×
          (Configuration n × Configuration n))) := by
  let V := nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj
  let p := nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j
  let f : Records (AnisotropicObservationState n) (Configuration n)
      (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj).tree →
        Records (AnisotropicObservationState n) (Configuration n) W.tree :=
    observationRefinementProject nativeStreamingPairObservationSubdivision W.tree
  let M : Measure (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (finiteCascadeFutureVertexGraft V p)) :=
    anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj) H)
      (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree
  have hx := sharedFutureEdge_map_graft_project V p f
    (measurable_observationRefinementProject nativeStreamingPairObservationSubdivision W.tree) M
  change M.map (fun z => ((z.1,f (finiteCascadeFutureGraftExtract V p z.2).1),
    (finiteCascadeFutureGraftExtract V p z.2).2)) =
    (M.map (fun z => ((z.1,(finiteCascadeFutureGraftExtract V p z.2).1),
      (finiteCascadeFutureGraftExtract V p z.2).2))).map (fun z => ((z.1.1,f z.1.2),z.2))
  exact hx

theorem nativeStreamingGeneratedSharedFutureEdgeProbability_append
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h e.depth)
    (hl : nativeStreamingGeneratedComponentClock W h (j+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h j)
    (hrl : r<l) :
    nativeStreamingGeneratedSharedFutureEdgeProbability D μ a W e j hj
      (nativeStreamingGeneratedCrossEdgeAppend h r l)=
      nativeStreamingOriginFutureProbability D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (.edge e r) j l := by
  unfold nativeStreamingGeneratedSharedFutureEdgeProbability
  rw [nativeStreamingGeneratedSharedFutureEdgeObserved_clock_append W e j hj h r l hh hr hl hrl]
  have hi := NativeStreamingGeneratedCrossEdgeChart.indices _ e.depth j r l
    (nativeStreamingGeneratedSharedFutureEdgeChart_holds e.depth j r l hrl)
  change nativeStreamingEdgeFutureProbabilityFixed D μ a (nativeStreamingGeneratedComponentClock W h)
    W.tree e j (nativeStreamingGeneratedSharedFutureEdgeChart e.depth j).firstSlot
      (nativeStreamingGeneratedSharedFutureEdgeChart e.depth j).secondSlot r l =
    nativeStreamingEdgeFutureProbabilityFixed D μ a (nativeStreamingGeneratedComponentClock W h)
      W.tree e j (nativeStreamingPairObservationIndex e.depth j r l)
        (nativeStreamingPairObservationIndex j e.depth l r) r l
  rw [hi.1,hi.2]

theorem nativeStreamingGeneratedSharedFutureEdgeComponent_record_law_append
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h e.depth)
    (hl : nativeStreamingGeneratedComponentClock W h (j+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h j)
    (hrl : r<l) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj)
        (nativeStreamingGeneratedCrossEdgeAppend h r l))
      (nativeStreamingGeneratedSharedFutureEdgeComponent W e j hj).tree).map
        (nativeStreamingGeneratedSharedFutureEdgeRecordProject W e j hj) =
      (nativeStreamingOriginFutureProbability D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (.edge e r) j l : Measure ((AnisotropicObservationState n ×
          Records (AnisotropicObservationState n) (Configuration n) W.tree) ×
            (Configuration n × Configuration n))) := by
  rw [nativeStreamingGeneratedSharedFutureEdgeComponent_record_law,
    nativeStreamingGeneratedSharedFutureEdgeProbability_append D μ a W e j hj h r l hh hr hl hrl]

end QuantitativeFollowup
