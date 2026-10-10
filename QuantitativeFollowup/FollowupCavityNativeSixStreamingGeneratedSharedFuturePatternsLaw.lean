module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFuturePatternsClocks
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginFuture

@[expose] public section

/-! The actual shared-future graft retains every original observation and
both fresh spins. Its complete projected law is the original vertex-origin
future probability, with the sampled future coordinate used exactly once. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

private theorem sharedFuture_map_graft_project {E S B : Type}
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
      measurable_snd)).prodMk ((measurable_finiteCascadeFutureGraftExtract v p).snd.comp
        measurable_snd)
  have hp : Measurable (fun z : (E × Records E S T) × (S × S) =>
      ((z.1.1,f z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk (hf.comp measurable_fst.snd)).prodMk measurable_snd
  simpa only [Function.comp_def] using (Measure.map_map (μ:=Q) hp hx).symm

def nativeStreamingGeneratedSharedFutureRecordProject
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth) :
    (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj).tree) →
      ((AnisotropicObservationState n ×
        Records (AnisotropicObservationState n) (Configuration n) W.tree) ×
          (Configuration n × Configuration n)) :=
  fun z => ((z.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) W.tree
    (finiteCascadeFutureGraftExtract (nativeStreamingGeneratedSharedFutureAnchor W v e)
      (e.depth+1) z.2).1),
    (finiteCascadeFutureGraftExtract (nativeStreamingGeneratedSharedFutureAnchor W v e)
      (e.depth+1) z.2).2)

theorem measurable_nativeStreamingGeneratedSharedFutureRecordProject
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth) :
    Measurable (nativeStreamingGeneratedSharedFutureRecordProject (n:=n) W v b hb e hj) := by
  exact (measurable_fst.prodMk
    ((measurable_observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) W.tree).comp
      ((measurable_finiteCascadeFutureGraftExtract
        (nativeStreamingGeneratedSharedFutureAnchor W v e) (e.depth+1)).fst.comp
          measurable_snd))).prodMk
    ((measurable_finiteCascadeFutureGraftExtract
      (nativeStreamingGeneratedSharedFutureAnchor W v e) (e.depth+1)).snd.comp measurable_snd)

theorem nativeStreamingGeneratedSharedFutureComponent_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock W h e.depth) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock
        (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj) (Fin.snoc h r))
      (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj).tree).map
        (nativeStreamingGeneratedSharedFutureRecordProject W v b hb e hj) =
      (nativeStreamingOriginFutureProbability D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (.vertex v) e.depth r : Measure _) := by
  let U := nativeStreamingGeneratedEdgeObservedComponent W e
  let V := nativeStreamingGeneratedSharedFutureAnchor W v e
  let q := nativeStreamingGeneratedComponentClock W h
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hx := nativeStreamingGeneratedRetainedFutureComponent_record_law D μ a U V
    b.castSucc (nativeStreamingGeneratedSharedFutureAnchor_label W v b hb e)
    (e.depth+1) (nativeStreamingGeneratedSharedFuture_split_le_anchor W v e hj)
    (Fin.last m) (nativeStreamingGeneratedSharedFuture_split_label W e) (Fin.snoc h r)
  let M : Measure (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (finiteCascadeFutureVertexGraft V (e.depth+1))) :=
    anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock
        (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj) (Fin.snoc h r))
      (nativeStreamingGeneratedSharedFutureComponent W v b hb e hj).tree
  let f : Records (AnisotropicObservationState n) (Configuration n) U.tree →
      Records (AnisotropicObservationState n) (Configuration n) W.tree :=
    observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) W.tree
  have hg := sharedFuture_map_graft_project V (e.depth+1) f
    (measurable_observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) W.tree) M
  have hp := congrArg (fun (L : Measure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) U.tree) ×
        (Configuration n × Configuration n))) =>
      L.map (fun z => ((z.1.1,f z.1.2),z.2))) hx
  have hclock : nativeStreamingGeneratedComponentClock U (Fin.snoc h r) = Q :=
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr
  have hq : Antitone q := nativeStreamingGeneratedComponentClock_antitone W h
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hf : (nativeStreamingFuturePairLaw D μ a
      (nativeStreamingGeneratedComponentClock U (Fin.snoc h r)) U.tree V
      (nativeStreamingGeneratedComponentClock U (Fin.snoc h r) (e.depth+1))).map
        (fun z => ((z.1.1,f z.1.2),z.2)) =
      (nativeStreamingOriginFutureProbability D μ a q W.tree (.vertex v) e.depth r : Measure _) := by
    rw [hclock]
    rw [show Q (e.depth+1) = r from nativeStreamingEdgeSchedule_inserted q e.depth r]
    exact (nativeStreamingFuturePairLaw_refinement D μ a q Q
      (nativeStreamingEdgeSubdivision e.depth) hQ
      (nativeStreamingEdgeSchedule_refinement q e.depth r) W.tree v r).trans
        (nativeStreamingOriginFutureProbability_vertex_eq_law D μ a q hq
          (nativeStreamingGeneratedComponentClock_terminal W h) W.tree v e.depth hj r hr).symm
  exact hg.trans (hp.trans hf)


end QuantitativeFollowup
