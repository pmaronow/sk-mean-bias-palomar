module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedRefinement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedContinuity

@[expose] public section

/-! A fresh mark at a variable point inside a specified original edge.
The inserted observation is the true native state at that point; the
complete original genealogy is projected back after drawing its genuine
conditional terminal spin. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

inductive NativeStreamingEdge : {j:ℕ}→FiniteTerminalGenealogy j→Type
  | here {j:ℕ} (T:FiniteTerminalGenealogy j) : NativeStreamingEdge (.advance T)
  | child {j:ℕ} {T:FiniteTerminalGenealogy j} : NativeStreamingEdge T→NativeStreamingEdge (.advance T)
  | left {j:ℕ} {T U:FiniteTerminalGenealogy j} : NativeStreamingEdge T→NativeStreamingEdge (.fork T U)
  | right {j:ℕ} {T U:FiniteTerminalGenealogy j} : NativeStreamingEdge U→NativeStreamingEdge (.fork T U)

@[reducible] def NativeStreamingEdge.depth : {j:ℕ}→{T:FiniteTerminalGenealogy j}→
    NativeStreamingEdge T→ℕ
  | _, _, @NativeStreamingEdge.here j _ => j
  | _, _, .child e => e.depth
  | _, _, .left e => e.depth
  | _, _, .right e => e.depth

theorem NativeStreamingEdge.depth_lt {j:ℕ} {T:FiniteTerminalGenealogy j}
    (e:NativeStreamingEdge T) : e.depth<j := by
  induction e with
  | here T => exact Nat.lt_succ_self _
  | child e ih => exact ih.trans (Nat.lt_succ_self _)
  | left e ih => exact ih
  | right e ih => exact ih

@[reducible] def nativeStreamingEdgeRefinedVertex (d:ℕ→ℕ) :
    {j:ℕ}→{T:FiniteTerminalGenealogy j}→NativeStreamingEdge T→
      FiniteCascadeRecordVertex (observationRefineTree d T)
  | _, _, @NativeStreamingEdge.here j T =>
      .child (.root (observationTreePad (observationRefineTree d T) (d j)))
  | _, _, @NativeStreamingEdge.child j T e =>
      .child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j)
        (nativeStreamingEdgeRefinedVertex d e))
  | _, _, .left e => .left (nativeStreamingEdgeRefinedVertex d e)
  | _, _, .right e => .right (nativeStreamingEdgeRefinedVertex d e)

theorem nativeStreamingEdgeRefinedVertex_depth (d:ℕ→ℕ)
    {j:ℕ} {T:FiniteTerminalGenealogy j} (e:NativeStreamingEdge T) :
    (nativeStreamingEdgeRefinedVertex d e).depth=observationRefinementDepth d e.depth+d e.depth := by
  induction e with
  | here T => rfl
  | child e ih =>
      change (nativeStreamingPadVertexEmbed _ _ _).depth=_
      rw [nativeStreamingPadVertexEmbed_depth]
      exact ih
  | left e ih => exact ih
  | right e ih => exact ih

theorem nativeStreamingEdgeRefinedVertex_inserted_depth
    {j:ℕ} {T:FiniteTerminalGenealogy j} (e:NativeStreamingEdge T) :
    (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e).depth=e.depth+1 := by
  rw [nativeStreamingEdgeRefinedVertex_depth,nativeStreamingEdgeSubdivision_depth]
  simp [nativeStreamingEdgeSubdivision]

theorem nativeStreamingEdgeRefinedVertex_inserted_level (q:ℕ→Paper.Overlap)
    {j:ℕ} {T:FiniteTerminalGenealogy j} (e:NativeStreamingEdge T) (r:Paper.Overlap) :
    nativeStreamingEdgeSchedule q e.depth r
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e).depth=r := by
  rw [nativeStreamingEdgeRefinedVertex_inserted_depth,nativeStreamingEdgeSchedule_inserted]

def nativeStreamingEdgeSingleMarkProbability (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (T:FiniteTerminalGenealogy J)
    (e:NativeStreamingEdge T) (r:Paper.Overlap) :
    ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×Configuration n) :=
  (nativeStreamingSingleVertexProbability D μ a (nativeStreamingEdgeSchedule q e.depth r)
    (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) T)
    (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)).map
      (fun z=>((z.1.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) T z.1.2),z.2))

theorem tendsto_nativeStreamingEdgeSingleMarkProbability
    {L:Type*} {l:Filter L} [l.IsCountablyGenerated] (D:AnisotropicSpinModel n)
    {μj:L→Paper.ParisiMeasure} {μ:Paper.ParisiMeasure} (hμ:Tendsto μj l (𝓝 μ))
    (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q) (T:FiniteTerminalGenealogy J)
    (e:NativeStreamingEdge T) {rj:L→Paper.Overlap} {r:Paper.Overlap}
    (hr:Tendsto rj l (𝓝 r))
    (hrj:∀N,q (e.depth+1)≤rj N ∧ rj N≤q e.depth)
    (hrr:q (e.depth+1)≤r ∧ r≤q e.depth) :
    Tendsto (fun N=>nativeStreamingEdgeSingleMarkProbability D (μj N) a q T e (rj N)) l
      (𝓝 (nativeStreamingEdgeSingleMarkProbability D μ a q T e r)) := by
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_nativeStreamingSingleVertexProbability_edge D hμ a q hq e.depth hr hrj hrr T
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e))
  exact (continuous_fst.fst.prodMk
    ((continuous_observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) T).comp
      continuous_fst.snd)).prodMk continuous_snd

end QuantitativeFollowup
