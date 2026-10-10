module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsGeometry

@[expose] public section

/-! Actual enlarged-tree moments for free original/fresh and current
patterns. The old observable is evaluated at the retained original prefix;
its continuous finite-spin coordinates may contain all previous defects. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem continuous_cavityGeneratedHistoryPrefix :
    Continuous (cavityGeneratedHistoryPrefix (Q:=Paper.Overlap) (m:=m)) := by
  exact continuous_pi (fun i => continuous_apply i.castSucc)

def nativeStreamingGeneratedEdgeOriginalFreshMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (i : ObservationLeaf W.tree) (H : CavityGeneratedHistory Paper.Overlap (m+1)) : ℝ :=
  let U := nativeStreamingGeneratedEdgeObservedComponent W e
  let v := nativeStreamingGeneratedEdgeVertex W e
  let q := nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeComponent W e .single) H
  nativeStreamingGeneratedVertexMoment D μ a q U.tree v .single
    (nativeStreamingOriginalFreshSpinTest U.tree
      (F (cavityGeneratedHistoryPrefix H) ∘ nativeStreamingGeneratedEdgeTerminalProject W e)
      (nativeStreamingGeneratedEdgeLeaf W e i)
      (q (finiteCascadeCommonPathDepth U.tree
        (observationLeafVertex U.tree (nativeStreamingGeneratedEdgeLeaf W e i)) v)))

def nativeStreamingGeneratedEdgeCurrentMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) : ℝ :=
  let U := nativeStreamingGeneratedEdgeObservedComponent W e
  let v := nativeStreamingGeneratedEdgeVertex W e
  let q := nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeComponent W e .current) H
  nativeStreamingGeneratedVertexMoment D μ a q U.tree v .current
    (nativeStreamingDefectSpinTest U.tree
      (F (cavityGeneratedHistoryPrefix H) ∘ nativeStreamingGeneratedEdgeTerminalProject W e) (q v.depth))

theorem nativeStreamingGeneratedEdgeOriginalFreshMoment_snoc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (i : ObservationLeaf W.tree) (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedEdgeOriginalFreshMoment D μ a W e F i (Fin.snoc h r) =
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.originalFresh i (.edge e r)) := by
  unfold nativeStreamingGeneratedEdgeOriginalFreshMoment
  dsimp only
  rw [nativeStreamingGeneratedEdgeComponent_clock,
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr,
    cavityGeneratedHistoryPrefix_snoc,nativeStreamingGeneratedVertexMoment_originalFresh]
  let d := nativeStreamingEdgeSubdivision e.depth
  let q := nativeStreamingGeneratedComponentClock W h
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hp : 0<d e.depth := by simp [d,nativeStreamingEdgeSubdivision]
  have hv := nativeStreamingSelected_one_slot_vertex W.tree e
  have hemark : Q (observationRefinementDepth d e.depth+0+1)=r := by
    simp [Q,d,nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
  have he := nativeStreamingPatternMoment_originalFresh_selected_refinement D μ a q Q d
    (nativeStreamingEdgeSchedule_antitone q (nativeStreamingGeneratedComponentClock_antitone W h) e.depth r hr)
    (nativeStreamingEdgeSchedule_refinement q e.depth r)
    (nativeStreamingGeneratedComponentClock_terminal W h) W.tree (F h) i e 0 hp
  rw [hv,hemark] at he
  exact he

theorem nativeStreamingGeneratedEdgeCurrentMoment_snoc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedEdgeCurrentMoment D μ a W e F (Fin.snoc h r) =
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.current (.edge e r)) := by
  unfold nativeStreamingGeneratedEdgeCurrentMoment
  dsimp only
  rw [nativeStreamingGeneratedEdgeComponent_clock,
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr,
    cavityGeneratedHistoryPrefix_snoc,nativeStreamingGeneratedVertexMoment_current]
  let d := nativeStreamingEdgeSubdivision e.depth
  let q := nativeStreamingGeneratedComponentClock W h
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hp : 0<d e.depth := by simp [d,nativeStreamingEdgeSubdivision]
  have hv := nativeStreamingSelected_one_slot_vertex W.tree e
  have hemark : Q (observationRefinementDepth d e.depth+0+1)=r := by
    simp [Q,d,nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
  have he := nativeStreamingPatternMoment_current_selected_refinement D μ a q Q d
    (nativeStreamingEdgeSchedule_antitone q (nativeStreamingGeneratedComponentClock_antitone W h) e.depth r hr)
    (nativeStreamingEdgeSchedule_refinement q e.depth r)
    (nativeStreamingGeneratedComponentClock_terminal W h) W.tree (F h) e 0 hp
  rw [hv,hemark] at he
  exact he

theorem nativeStreamingGeneratedEdgeOriginalFreshMoment_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (i : ObservationLeaf W.tree) (C : ℝ) (hC : 0≤C) (hF : ∀h σ, |F h σ|≤C)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    |nativeStreamingGeneratedEdgeOriginalFreshMoment D μ a W e F i H|≤2*C := by
  apply nativeStreamingGeneratedVertexMoment_abs_le
  intro σ
  exact nativeStreamingOriginalFreshSpinTest_abs_le _ _ C hC
    (fun τ => hF _ (nativeStreamingGeneratedEdgeTerminalProject W e τ)) _ _ σ

theorem nativeStreamingGeneratedEdgeCurrentMoment_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀h σ, |F h σ|≤C)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    |nativeStreamingGeneratedEdgeCurrentMoment D μ a W e F H|≤2*C := by
  apply nativeStreamingGeneratedVertexMoment_abs_le
  intro σ
  exact nativeStreamingDefectSpinTest_abs_le _ _ C hC
    (fun τ => hF _ (nativeStreamingGeneratedEdgeTerminalProject W e τ)) _ σ

theorem continuous_nativeStreamingGeneratedEdgeOriginalFreshMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ, Continuous (fun h => F h σ)) (i : ObservationLeaf W.tree) :
    Continuous (nativeStreamingGeneratedEdgeOriginalFreshMoment D μ a W e F i) := by
  unfold nativeStreamingGeneratedEdgeOriginalFreshMoment
  dsimp only
  simp_rw [nativeStreamingGeneratedEdgeComponent_clock]
  apply continuous_nativeStreamingGeneratedVertexMoment D μ a
    (nativeStreamingGeneratedEdgeObservedComponent W e) (nativeStreamingGeneratedEdgeVertex W e) .single
  intro σ
  exact ((hF (nativeStreamingGeneratedEdgeTerminalProject W e σ.1)).comp
    continuous_cavityGeneratedHistoryPrefix).mul
      (continuous_cavitySpinOverlapDefect_clock _
        (nativeStreamingGeneratedComponentClock_continuous (nativeStreamingGeneratedEdgeObservedComponent W e) _)
        _ _)

theorem continuous_nativeStreamingGeneratedEdgeCurrentMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ, Continuous (fun h => F h σ)) :
    Continuous (nativeStreamingGeneratedEdgeCurrentMoment D μ a W e F) := by
  unfold nativeStreamingGeneratedEdgeCurrentMoment
  dsimp only
  simp_rw [nativeStreamingGeneratedEdgeComponent_clock]
  apply continuous_nativeStreamingGeneratedVertexMoment D μ a
    (nativeStreamingGeneratedEdgeObservedComponent W e) (nativeStreamingGeneratedEdgeVertex W e) .current
  intro σ
  exact ((hF (nativeStreamingGeneratedEdgeTerminalProject W e σ.1)).comp
    continuous_cavityGeneratedHistoryPrefix).mul
      (continuous_cavitySpinOverlapDefect_clock _
        (nativeStreamingGeneratedComponentClock_continuous (nativeStreamingGeneratedEdgeObservedComponent W e) _)
        _ _)

end QuantitativeFollowup
