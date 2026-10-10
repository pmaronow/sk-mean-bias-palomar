module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossVertexPatternsMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexBranchPatternsConstruction
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternTerminalRepresentationRefinement

@[expose] public section

/-! A free edge mark is drawn once. The second continuation is grafted at
an original retained interior vertex. Its genuine inherited branch weight
copies an original history coordinate, including coincident physical times. -/
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

def nativeStreamingGeneratedMixedRefinedVertex
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) :
    FiniteCascadeRecordVertex (nativeStreamingGeneratedEdgeObservedComponent W e).tree :=
  nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) W.tree v

theorem nativeStreamingGeneratedMixedRefinedVertex_depth
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) :
    (nativeStreamingGeneratedMixedRefinedVertex W e v).depth =
      observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) v.depth := by
  exact nativeStreamingRefinementVertexEmbed_depth _ W.tree v

theorem nativeStreamingGeneratedMixedRefinedVertex_interior
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth) :
    0<(nativeStreamingGeneratedMixedRefinedVertex W e v).depth ∧
      (nativeStreamingGeneratedMixedRefinedVertex W e v).depth<
        (nativeStreamingGeneratedEdgeObservedComponent W e).depth := by
  rw [nativeStreamingGeneratedMixedRefinedVertex_depth,
    nativeStreamingGeneratedEdgeObservedComponent_depth,nativeStreamingEdgeSubdivision_depth]
  split_ifs <;> omega

theorem nativeStreamingGeneratedMixedRefinedVertex_label
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth=.mark b) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeObservedComponent W e).label
      (nativeStreamingGeneratedMixedRefinedVertex W e v).depth=.mark b.castSucc := by
  change cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels W e) _ = _
  rw [nativeStreamingGeneratedEdgeLabels_global,nativeStreamingGeneratedMixedRefinedVertex_depth,
    nativeStreamingGeneratedEdgeGlobalLabels_refinement,hb]
  rfl

def nativeStreamingGeneratedMixedAttachedVertex
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) :
    FiniteCascadeRecordVertex (nativeStreamingGeneratedEdgeComponent W e .single).tree :=
  finiteCascadeContinuationVertexEmbed observationLinearTree
    (nativeStreamingGeneratedEdgeVertex W e) (nativeStreamingGeneratedMixedRefinedVertex W e v)

theorem nativeStreamingGeneratedMixedAttachedVertex_interior
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth) :
    0<(nativeStreamingGeneratedMixedAttachedVertex W e v).depth ∧
      (nativeStreamingGeneratedMixedAttachedVertex W e v).depth<
        (nativeStreamingGeneratedEdgeComponent W e .single).depth := by
  simpa only [nativeStreamingGeneratedMixedAttachedVertex,finiteCascadeContinuationVertexEmbed_depth,
    nativeStreamingGeneratedEdgeComponent] using
      nativeStreamingGeneratedMixedRefinedVertex_interior W e v hv0 hvJ

theorem nativeStreamingGeneratedMixedAttachedVertex_label
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth=.mark b) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeComponent W e .single).label
      (nativeStreamingGeneratedMixedAttachedVertex W e v).depth=.mark b.castSucc := by
  simpa only [nativeStreamingGeneratedMixedAttachedVertex,finiteCascadeContinuationVertexEmbed_depth,
    nativeStreamingGeneratedEdgeComponent] using
      nativeStreamingGeneratedMixedRefinedVertex_label W e v b hb

def nativeStreamingGeneratedMixedCrossComponent
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth) :
    CavityGeneratedConstructedComponent (m+2) :=
  nativeStreamingGeneratedVertexComponent (nativeStreamingGeneratedEdgeComponent W e .single)
    (nativeStreamingGeneratedMixedAttachedVertex W e v)
    (nativeStreamingGeneratedMixedAttachedVertex_interior W e v hv0 hvJ).1
    (nativeStreamingGeneratedMixedAttachedVertex_interior W e v hv0 hvJ).2 .single

theorem nativeStreamingGeneratedMixedCrossComponent_tree
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth) :
    (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ).tree=
      finiteCascadeCrossContinuationGraft observationLinearTree
        (nativeStreamingGeneratedEdgeVertex W e) (nativeStreamingGeneratedMixedRefinedVertex W e v) := rfl

def nativeStreamingGeneratedMixedCrossAppend (b : Fin m)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) :
    CavityGeneratedHistory Paper.Overlap (m+2) := Fin.snoc (Fin.snoc h r) (h b)

theorem nativeStreamingGeneratedMixedCrossComponent_clock_append
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels W.label v.depth=.mark b)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ)
      (nativeStreamingGeneratedMixedCrossAppend b h r)=
        nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock W h) e.depth r := by
  let U := nativeStreamingGeneratedEdgeComponent W e .single
  let w := nativeStreamingGeneratedMixedAttachedVertex W e v
  have ht := nativeStreamingGeneratedMixedAttachedVertex_interior W e v hv0 hvJ
  have hraw : (cavityGeneratedFiniteClockLabels U.label w.depth).value (Fin.snoc h r)=h b := by
    rw [nativeStreamingGeneratedMixedAttachedVertex_label W e v b hb]
    simp only [CavityGeneratedClockLabel.value,Fin.snoc_castSucc]
  change nativeStreamingGeneratedComponentClock
    (nativeStreamingGeneratedVertexComponent U w ht.1 ht.2 .single)
      (Fin.snoc (Fin.snoc h r) (h b))=_
  rw [←hraw,nativeStreamingGeneratedVertexComponent_clock_at_atom U w ht.1 ht.2,
    nativeStreamingGeneratedEdgeComponent_clock,
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr]

theorem nativeStreamingGeneratedMixedCross_full_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels W.label v.depth=.mark b)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    (nativeStreamingCrossVertexProbability D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ)
        (nativeStreamingGeneratedMixedCrossAppend b h r))
      (nativeStreamingGeneratedEdgeObservedComponent W e).tree
      (nativeStreamingGeneratedEdgeVertex W e) (nativeStreamingGeneratedMixedRefinedVertex W e v)).map
        (fun z=>((z.1.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth)
          W.tree z.1.2),z.2))=
      nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (.edge e r) (.vertex v) := by
  rw [nativeStreamingGeneratedMixedCrossComponent_clock_append W e v hv0 hvJ b hb h r hh hr]
  rfl

end QuantitativeFollowup
