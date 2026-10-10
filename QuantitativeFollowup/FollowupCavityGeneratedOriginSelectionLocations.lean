module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginExpanded
public import QuantitativeFollowup.FollowupCavityGeneratedOriginForkLabels

@[expose] public section

/-! Actual attachment locations, before forgetting the selected edge or
fork. The edge list may depend on observation depth; its total weight is
the genuine origin integral, rather than a count of grid cells. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

@[reducible] def cavityGeneratedOriginForkVertices :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → List (FiniteCascadeRecordVertex T)
  | _, .leaf => []
  | _, .advance T => (cavityGeneratedOriginForkVertices T).map .child
  | _, .fork T U => (cavityGeneratedOriginForkVertices T).map .left ++
      (cavityGeneratedOriginForkVertices U).map .right ++ [.root (.fork T U)]

@[reducible] def cavityGeneratedOriginEdges :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → List (NativeStreamingEdge T)
  | _, .leaf => []
  | _, .advance T => (cavityGeneratedOriginEdges T).map .child ++ [.here T]
  | _, .fork T U => (cavityGeneratedOriginEdges T).map .left ++
      (cavityGeneratedOriginEdges U).map .right

theorem cavityGeneratedOriginForkVertices_depths
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (cavityGeneratedOriginForkVertices T).map FiniteCascadeRecordVertex.depth =
      printedGeneratedOriginForkDepths T := by
  induction T with
  | leaf => rfl
  | advance T ih =>
      simpa only [cavityGeneratedOriginForkVertices, printedGeneratedOriginForkDepths,
        List.map_map, Function.comp_def, FiniteCascadeRecordVertex.depth] using ih
  | fork T U ihT ihU =>
      simp only [cavityGeneratedOriginForkVertices, printedGeneratedOriginForkDepths,
        List.map_append, List.map_map, Function.comp_def, List.map_singleton,
        FiniteCascadeRecordVertex.depth, ihT, ihU]

theorem cavityGeneratedOriginForkVertices_count
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (cavityGeneratedOriginForkVertices T).length+1 =
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  have hd := congrArg List.length (cavityGeneratedOriginForkVertices_depths T)
  rw [List.length_map] at hd
  rw [hd]
  exact printedGeneratedOriginForkDepths_count T

theorem cavityGeneratedOriginForkVertex_mark
    {m : ℕ} (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (v : FiniteCascadeRecordVertex (W.tree c))
    (hv : v ∈ cavityGeneratedOriginForkVertices (W.tree c)) :
    ∃i : Fin m, cavityGeneratedFiniteClockLabels (W.label c) v.depth = .mark i := by
  have hd : v.depth ∈ printedGeneratedOriginForkDepths (W.tree c) := by
    rw [←cavityGeneratedOriginForkVertices_depths]
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
  exact cavityGeneratedOriginForkDepth_mark W c v.depth hd

theorem cavityGeneratedOriginBranchWeightSum_eq_vertices
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (Φ : NativeStreamingOrigin T → ℝ) :
    nativeStreamingOriginBranchWeightSum μ q T Φ =
      ((cavityGeneratedOriginForkVertices T).map
        (fun v => Paper.parisiCDF μ (q v.depth)*Φ (.vertex v))).sum := by
  induction T with
  | leaf => rfl
  | advance T ih =>
      simpa only [nativeStreamingOriginBranchWeightSum, cavityGeneratedOriginForkVertices,
        List.map_map, Function.comp_def, nativeStreamingOriginChild, FiniteCascadeRecordVertex.depth] using
        ih (fun o => Φ (nativeStreamingOriginChild o))
  | fork T U ihT ihU =>
      simp only [nativeStreamingOriginBranchWeightSum, cavityGeneratedOriginForkVertices,
        List.map_append, List.sum_append, List.map_map, Function.comp_def, List.map_singleton,
        List.sum_singleton, nativeStreamingOriginLeft, nativeStreamingOriginRight,
        FiniteCascadeRecordVertex.depth,
        ihT (fun o => Φ (nativeStreamingOriginLeft o)),
        ihU (fun o => Φ (nativeStreamingOriginRight o))]

theorem cavityGeneratedOriginEdgeWeightIntegral_eq_edges
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq0 : q 0 = 1)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (Φ : NativeStreamingOrigin T → ℝ) :
    nativeStreamingOriginEdgeWeightIntegral μ a q T Φ =
      ((cavityGeneratedOriginEdges T).map
        (fun e => ∫r in Ioc (q (e.depth+1)) (q e.depth),
          Φ (.edge e r) ∂parisiFreeMeasure μ a)).sum := by
  induction T with
  | leaf =>
      have hc : Paper.parisiCDF μ ((1 : Paper.Overlap) : ℝ) = 1 :=
        Paper.parisiCDF_eq_one_of_one_le μ (by norm_num)
      simp only [nativeStreamingOriginEdgeWeightIntegral, cavityGeneratedOriginEdges,
        List.map_nil, List.sum_nil, hq0, hc, sub_self, zero_mul]
  | @advance j T ih =>
      simpa only [nativeStreamingOriginEdgeWeightIntegral, cavityGeneratedOriginEdges,
        List.map_append, List.sum_append, List.map_map, Function.comp_def, List.map_singleton,
        List.sum_singleton, nativeStreamingOriginChild, NativeStreamingEdge.depth] using
        congrArg (fun x => x+(∫r in Ioc (q (j+1)) (q j),
          Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a))
          (ih (fun o => Φ (nativeStreamingOriginChild o)))
  | fork T U ihT ihU =>
      simp only [nativeStreamingOriginEdgeWeightIntegral, cavityGeneratedOriginEdges,
        List.map_append, List.sum_append, List.map_map, Function.comp_def,
        nativeStreamingOriginLeft, nativeStreamingOriginRight, NativeStreamingEdge.depth,
        ihT (fun o => Φ (nativeStreamingOriginLeft o)),
        ihU (fun o => Φ (nativeStreamingOriginRight o))]

theorem cavityGeneratedOriginWeightIntegral_eq_selected_locations
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq0 : q 0 = 1)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ) (Φ : NativeStreamingOrigin T → ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T s Φ =
      ((cavityGeneratedOriginEdges T).map
        (fun e => ∫r in Ioc (q (e.depth+1)) (q e.depth),
          Φ (.edge e r) ∂parisiFreeMeasure μ a)).sum +
      ((cavityGeneratedOriginForkVertices T).map
        (fun v => Paper.parisiCDF μ (q v.depth)*Φ (.vertex v))).sum +
      (Paper.parisiCDF μ (q j)-s)*Φ (.vertex (.root T)) := by
  rw [nativeStreamingOriginWeightIntegral_eq_edges_branches_root,
    cavityGeneratedOriginEdgeWeightIntegral_eq_edges μ a q hq0,
    cavityGeneratedOriginBranchWeightSum_eq_vertices]

end QuantitativeFollowup
