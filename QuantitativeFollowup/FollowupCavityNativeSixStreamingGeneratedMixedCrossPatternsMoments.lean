module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedMixedCrossPatternsGeometry

@[expose] public section

/-! The mixed terminal test is evaluated on the actual enlarged tree.
Every original terminal spin is projected back to the original tree;
the fresh pair uses its genuine common physical clock. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem nativeStreamingGeneratedMixedCross_common_clock
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (q : ℕ→Paper.Overlap) (r : Paper.Overlap) :
    nativeStreamingEdgeSchedule q e.depth r
      (finiteCascadeCommonPathDepth (nativeStreamingGeneratedEdgeObservedComponent W e).tree
        (nativeStreamingGeneratedEdgeVertex W e) (nativeStreamingGeneratedMixedRefinedVertex W e v))=
      nativeStreamingOriginCommonClock q W.tree (.edge e r) (.vertex v) := by
  let d := nativeStreamingEdgeSubdivision e.depth
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hp : 0<d e.depth := by simp [d,nativeStreamingEdgeSubdivision]
  have hv := nativeStreamingSelected_one_slot_vertex W.tree e
  have hemark : Q (observationRefinementDepth d e.depth+0+1)=r := by
    simp [Q,d,nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
  have he := nativeStreamingEdgeOldVertex_commonPathClock_eq_mark d q Q W.tree
    (fun i _ => nativeStreamingEdgeSchedule_refinement q e.depth r i) v e 0 hp r hemark
  rw [hv] at he
  change Q (finiteCascadeCommonPathDepth (observationRefineTree d W.tree)
    (nativeStreamingGeneratedEdgeVertex W e) (nativeStreamingGeneratedMixedRefinedVertex W e v))=_
  rw [nativeStreamingSelectedGeometry_commonPathDepth_symm]
  exact he

def nativeStreamingGeneratedMixedCrossPatternMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m→TerminalSpins (Configuration (n+1)) W.tree→ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : ℝ :=
  let U := nativeStreamingGeneratedEdgeObservedComponent W e
  let t := nativeStreamingGeneratedEdgeVertex W e
  let w := nativeStreamingGeneratedMixedRefinedVertex W e v
  let q := nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ) H
  nativeStreamingGeneratedCrossVertexMoment D μ a q U.tree t w
    (nativeStreamingPatternRefinedMarkedTest (nativeStreamingEdgeSubdivision e.depth) W.tree
      (nativeStreamingDefectSpinTest W.tree (F (nativeStreamingGeneratedCrossVertexPrefix H))
        (q (finiteCascadeCommonPathDepth U.tree t w))))

theorem nativeStreamingGeneratedMixedCrossPatternMoment_append
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels W.label v.depth=.mark b)
    (F : CavityGeneratedHistory Paper.Overlap m→TerminalSpins (Configuration (n+1)) W.tree→ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedMixedCrossPatternMoment D μ a W e v hv0 hvJ F
      (nativeStreamingGeneratedMixedCrossAppend b h r)=
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.cross (.edge e r) (.vertex v)) := by
  unfold nativeStreamingGeneratedMixedCrossPatternMoment
  dsimp only
  rw [nativeStreamingGeneratedMixedCrossComponent_clock_append W e v hv0 hvJ b hb h r hh hr]
  have hp : nativeStreamingGeneratedCrossVertexPrefix (nativeStreamingGeneratedMixedCrossAppend b h r)=h := by
    simp only [nativeStreamingGeneratedCrossVertexPrefix,nativeStreamingGeneratedMixedCrossAppend,
      cavityGeneratedHistoryPrefix_snoc]
  rw [hp,nativeStreamingGeneratedMixedCross_common_clock,
    nativeStreamingGeneratedCrossVertexMoment_eq_terminalMarkMoment]
  rw [←nativeStreamingPatternTerminalMarkMoment_refinement_map]
  rfl

theorem nativeStreamingGeneratedMixedCrossPatternMoment_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m→TerminalSpins (Configuration (n+1)) W.tree→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀h σ,|F h σ|≤C)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    |nativeStreamingGeneratedMixedCrossPatternMoment D μ a W e v hv0 hvJ F H|≤2*C := by
  apply nativeStreamingGeneratedCrossVertexMoment_abs_le
  intro σ
  exact nativeStreamingDefectSpinTest_abs_le W.tree _ C hC (hF _) _
    (observationRefinementTerminalProject (nativeStreamingEdgeSubdivision e.depth) W.tree rfl σ.1,σ.2)

theorem continuous_nativeStreamingGeneratedMixedCrossPatternMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m→TerminalSpins (Configuration (n+1)) W.tree→ℝ)
    (hF : ∀σ,Continuous (fun h=>F h σ)) :
    Continuous (nativeStreamingGeneratedMixedCrossPatternMoment D μ a W e v hv0 hvJ F) := by
  unfold nativeStreamingGeneratedMixedCrossPatternMoment
  dsimp only
  apply continuous_nativeStreamingGeneratedCrossVertexMoment D μ a
    (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ)
    (nativeStreamingGeneratedEdgeObservedComponent W e).tree
    (nativeStreamingGeneratedEdgeVertex W e) (nativeStreamingGeneratedMixedRefinedVertex W e v)
  intro σ
  exact ((hF (observationRefinementTerminalProject (nativeStreamingEdgeSubdivision e.depth) W.tree rfl σ.1)).comp
    continuous_nativeStreamingGeneratedCrossVertexPrefix).mul
      (continuous_cavitySpinOverlapDefect_clock _
        (nativeStreamingGeneratedComponentClock_continuous
          (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ) _) _ _)

end QuantitativeFollowup
