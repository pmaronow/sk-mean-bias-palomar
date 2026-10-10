module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsHistory
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossMarkedLaw

@[expose] public section

/-! Two actual single-continuation grafts retain all old records and use
two atom clocks chosen from the original component. Coincident vertices
and equal physical clocks are included without a distinctness premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedCrossVertexPrefix
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    CavityGeneratedHistory Paper.Overlap m :=
  cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)

theorem measurable_nativeStreamingGeneratedCrossVertexPrefix :
    Measurable (nativeStreamingGeneratedCrossVertexPrefix (m:=m)) :=
  cavityGeneratedHistoryPrefix_measurable.comp cavityGeneratedHistoryPrefix_measurable

theorem continuous_nativeStreamingGeneratedCrossVertexPrefix :
    Continuous (nativeStreamingGeneratedCrossVertexPrefix (m:=m)) := by
  exact continuous_pi (fun i => continuous_apply i.castSucc.castSucc)

def nativeStreamingGeneratedCrossVertexAtomProgram
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m)
    (v w : FiniteCascadeRecordVertex W.tree) :
    CavityGeneratedMarkProgram Paper.Overlap (m+2) :=
  .atom (nativeStreamingGeneratedVertexAtomProgram P W v)
    (fun H => (cavityGeneratedFiniteClockLabels W.label w.depth).value
      (cavityGeneratedHistoryPrefix H))
    ((cavityGeneratedFiniteClockLabels W.label w.depth).continuous_value.measurable.comp
      cavityGeneratedHistoryPrefix_measurable)

def nativeStreamingGeneratedCrossVertexAppend
    (W : CavityGeneratedConstructedComponent m)
    (v w : FiniteCascadeRecordVertex W.tree) (h : CavityGeneratedHistory Paper.Overlap m) :
    CavityGeneratedHistory Paper.Overlap (m+2) :=
  Fin.snoc (Fin.snoc h ((cavityGeneratedFiniteClockLabels W.label v.depth).value h))
    ((cavityGeneratedFiniteClockLabels W.label w.depth).value h)

theorem measurable_nativeStreamingGeneratedCrossVertexAppend
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree) :
    Measurable (nativeStreamingGeneratedCrossVertexAppend W v w) := by
  have hm := (cavityGeneratedHistorySnoc_measurable _
    (cavityGeneratedFiniteClockLabels W.label v.depth).continuous_value.measurable).prodMk
      (cavityGeneratedFiniteClockLabels W.label w.depth).continuous_value.measurable
  unfold nativeStreamingGeneratedCrossVertexAppend
  exact (cavityGeneratedHistoryAppend_measurable (Q:=Paper.Overlap) (m:=m+1)).comp hm

theorem nativeStreamingGeneratedCrossVertexPrefix_append
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedCrossVertexPrefix (nativeStreamingGeneratedCrossVertexAppend W v w h)=h := by
  simp only [nativeStreamingGeneratedCrossVertexPrefix,nativeStreamingGeneratedCrossVertexAppend,
    cavityGeneratedHistoryPrefix_snoc]

def nativeStreamingGeneratedCrossVertexComponent
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (hw0 : 0<w.depth) (hwJ : w.depth<W.depth) :
    CavityGeneratedConstructedComponent (m+2) :=
  nativeStreamingGeneratedVertexComponent
    (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .single)
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w)
    (by simpa only [finiteCascadeContinuationVertexEmbed_depth] using hw0)
    (by simpa only [finiteCascadeContinuationVertexEmbed_depth,nativeStreamingGeneratedVertexComponent] using hwJ) .single

theorem nativeStreamingGeneratedCrossVertexComponent_tree
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (hw0 : 0<w.depth) (hwJ : w.depth<W.depth) :
    (nativeStreamingGeneratedCrossVertexComponent W v w hv0 hvJ hw0 hwJ).tree=
      finiteCascadeCrossContinuationGraft observationLinearTree v w := rfl

private theorem generated_vertex_raw_clock_at_atom
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (p : ℕ) :
    (cavityGeneratedFiniteClockLabels
      (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .single).label p).value
        (Fin.snoc h ((cavityGeneratedFiniteClockLabels W.label v.depth).value h))=
      (cavityGeneratedFiniteClockLabels W.label p).value h := by
  change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedVertexLabels W v.depth) p).value
    (Fin.snoc h ((cavityGeneratedFiniteClockLabels W.label v.depth).value h))=_
  rw [nativeStreamingGeneratedVertexLabels_global W v.depth hvJ.le]
  by_cases hp : p=v.depth
  · subst p
    simp only [cavityGeneratedAttachedClockLabels_at_depth,CavityGeneratedClockLabel.value,
      Fin.snoc_last]
  · rw [cavityGeneratedAttachedClockLabels,if_neg hp,
      CavityGeneratedClockLabel.append_reindex_value,cavityGeneratedHistoryPrefix_snoc]

theorem nativeStreamingGeneratedVertexComponent_clock_at_atom
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .single)
      (Fin.snoc h ((cavityGeneratedFiniteClockLabels W.label v.depth).value h))=
        nativeStreamingGeneratedComponentClock W h := by
  apply congrArg cavityGeneratedClippedClock
  exact funext (generated_vertex_raw_clock_at_atom W v hv0 hvJ h)

theorem nativeStreamingGeneratedCrossVertexComponent_clock_append
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (hw0 : 0<w.depth) (hwJ : w.depth<W.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedCrossVertexComponent W v w hv0 hvJ hw0 hwJ)
        (nativeStreamingGeneratedCrossVertexAppend W v w h)=
      nativeStreamingGeneratedComponentClock W h := by
  let U : CavityGeneratedConstructedComponent (m+1) := nativeStreamingGeneratedVertexComponent W v hv0 hvJ .single
  let t := finiteCascadeContinuationVertexEmbed observationLinearTree v w
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h ((cavityGeneratedFiniteClockLabels W.label v.depth).value h)
  have ht0 : 0<t.depth := by simpa only [t,finiteCascadeContinuationVertexEmbed_depth] using hw0
  have htJ : t.depth<U.depth := by
    simpa only [t,U,finiteCascadeContinuationVertexEmbed_depth,nativeStreamingGeneratedVertexComponent] using hwJ
  have hraw : (cavityGeneratedFiniteClockLabels U.label t.depth).value H=
      (cavityGeneratedFiniteClockLabels W.label w.depth).value h := by
    simpa only [U,t,H,finiteCascadeContinuationVertexEmbed_depth] using
      generated_vertex_raw_clock_at_atom W v hv0 hvJ h w.depth
  change nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent U t ht0 htJ .single)
    (Fin.snoc H ((cavityGeneratedFiniteClockLabels W.label w.depth).value h))=_
  rw [←hraw,nativeStreamingGeneratedVertexComponent_clock_at_atom U t ht0 htJ H]
  exact nativeStreamingGeneratedVertexComponent_clock_at_atom W v hv0 hvJ h

theorem nativeStreamingGeneratedCrossVertex_full_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (hw0 : 0<w.depth) (hwJ : w.depth<W.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock
        (nativeStreamingGeneratedCrossVertexComponent W v w hv0 hvJ hw0 hwJ)
          (nativeStreamingGeneratedCrossVertexAppend W v w h))
      (nativeStreamingGeneratedCrossVertexComponent W v w hv0 hvJ hw0 hwJ).tree).map
        (fun z => ((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree
          observationLinearSpin v w z.2).1),
          (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).2))=
      nativeStreamingCrossVertexLaw D μ a (nativeStreamingGeneratedComponentClock W h) W.tree v w := by
  rw [nativeStreamingGeneratedCrossVertexComponent_clock_append]
  exact nativeStreamingCrossVertexLaw_eq_graft D μ a _
    (nativeStreamingGeneratedComponentClock_antitone W h)
    (nativeStreamingGeneratedComponentClock_terminal W h) W.tree v w

end QuantitativeFollowup
