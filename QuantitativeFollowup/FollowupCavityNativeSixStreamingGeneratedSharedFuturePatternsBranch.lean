module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFuturePatternsMoments
public import QuantitativeFollowup.FollowupCavityGeneratedForestReindex
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexBranchPatternsConstruction

@[expose] public section

/-! The branch instruction copies the already retained anchor. Reindexing
keeps the original component and every old label, before the one fresh
future coordinate is appended. No new atom is drawn at the future split. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedSharedFutureBranchBase
    (W : CavityGeneratedConstructedComponent m) : CavityGeneratedConstructedComponent (m+1) :=
  ((nativeStreamingGeneratedComponentForest W).reindex Fin.castSucc).component (0 : Fin 1)

theorem nativeStreamingGeneratedSharedFutureBranchBase_label_value
    (W : CavityGeneratedConstructedComponent m) (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (j : ℕ) :
    (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedSharedFutureBranchBase W).label j).value H =
      (cavityGeneratedFiniteClockLabels W.label j).value (cavityGeneratedHistoryPrefix H) := by
  change (cavityGeneratedFiniteClockLabels (fun t => (W.label t).reindex Fin.castSucc) j).value H = _
  by_cases hj : j ≤ W.depth
  · simp only [cavityGeneratedFiniteClockLabels,dif_pos hj]
    exact CavityGeneratedClockLabel.reindex_value Fin.castSucc _
      (cavityGeneratedHistoryPrefix H) H (fun _ => rfl)
  · simp only [cavityGeneratedFiniteClockLabels,dif_neg hj,CavityGeneratedClockLabel.value]

theorem nativeStreamingGeneratedSharedFutureBranchBase_clock
    (W : CavityGeneratedConstructedComponent m) (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureBranchBase W) H =
      nativeStreamingGeneratedComponentClock W (cavityGeneratedHistoryPrefix H) := by
  apply congrArg cavityGeneratedClippedClock
  funext j
  exact nativeStreamingGeneratedSharedFutureBranchBase_label_value W H j

theorem nativeStreamingGeneratedSharedFutureBranchBase_order
    (W : CavityGeneratedConstructedComponent m) (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    H ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedSharedFutureBranchBase W) ↔
      cavityGeneratedHistoryPrefix H ∈ nativeStreamingGeneratedComponentOrderSet W := by
  change (∀j : Fin W.depth, _ ≤ _) ↔ (∀j : Fin W.depth, _ ≤ _)
  simp only [nativeStreamingGeneratedSharedFutureBranchBase_label_value]

theorem nativeStreamingGeneratedSharedFutureBranchBase_label
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b) :
    cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedSharedFutureBranchBase W).label
      v.depth = .mark b.castSucc := by
  change cavityGeneratedFiniteClockLabels (fun t => (W.label t).reindex Fin.castSucc) v.depth = _
  have hd := v.depth_le
  simp only [cavityGeneratedFiniteClockLabels,dif_pos hd] at hb ⊢
  rw [hb]
  rfl

def nativeStreamingGeneratedSharedFutureBranchComponent
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth) :
    CavityGeneratedConstructedComponent ((m+1)+1) :=
  nativeStreamingGeneratedSharedFutureComponent (nativeStreamingGeneratedSharedFutureBranchBase W)
    v b.castSucc (nativeStreamingGeneratedSharedFutureBranchBase_label W v b hb) e hj

def nativeStreamingGeneratedSharedFutureHistoryEraseBranch
    (H : CavityGeneratedHistory Paper.Overlap ((m+1)+1)) :
    CavityGeneratedHistory Paper.Overlap (m+1) :=
  Fin.snoc (cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H)) (H (Fin.last (m+1)))

theorem continuous_nativeStreamingGeneratedSharedFutureHistoryEraseBranch :
    Continuous (nativeStreamingGeneratedSharedFutureHistoryEraseBranch (m:=m)) := by
  apply continuous_pi
  intro i
  induction i using Fin.lastCases with
  | last =>
      simpa only [nativeStreamingGeneratedSharedFutureHistoryEraseBranch,Fin.snoc_last] using
        continuous_apply (Fin.last (m+1))
  | cast i =>
      simpa only [nativeStreamingGeneratedSharedFutureHistoryEraseBranch,Fin.snoc_castSucc,
        Function.comp_def] using
        (continuous_apply i).comp (continuous_cavityGeneratedHistoryPrefix.comp
          continuous_cavityGeneratedHistoryPrefix)

theorem nativeStreamingGeneratedSharedFutureHistoryEraseBranch_snoc
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) (r : Paper.Overlap) :
    nativeStreamingGeneratedSharedFutureHistoryEraseBranch (Fin.snoc H r) =
      Fin.snoc (cavityGeneratedHistoryPrefix H) r := by
  simp only [nativeStreamingGeneratedSharedFutureHistoryEraseBranch,
    cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last]

theorem nativeStreamingGeneratedSharedFutureHistoryEraseBranch_prefix
    (H : CavityGeneratedHistory Paper.Overlap ((m+1)+1)) :
    cavityGeneratedHistoryPrefix (nativeStreamingGeneratedSharedFutureHistoryEraseBranch H) =
      cavityGeneratedHistoryPrefix (cavityGeneratedHistoryPrefix H) :=
  cavityGeneratedHistoryPrefix_snoc _ _

theorem nativeStreamingGeneratedSharedFutureBranchComponent_clock
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (H : CavityGeneratedHistory Paper.Overlap ((m+1)+1)) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureBranchComponent W v b hb e hj) H =
      nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e)
        (nativeStreamingGeneratedSharedFutureHistoryEraseBranch H) := by
  rw [nativeStreamingGeneratedSharedFutureBranchComponent,
    nativeStreamingGeneratedSharedFutureComponent_clock]
  apply congrArg cavityGeneratedClippedClock
  funext j
  change (cavityGeneratedFiniteClockLabels
    (nativeStreamingGeneratedEdgeLabels (nativeStreamingGeneratedSharedFutureBranchBase W) e) j).value H =
      (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels W e) j).value
        (nativeStreamingGeneratedSharedFutureHistoryEraseBranch H)
  rw [nativeStreamingGeneratedEdgeLabels_global,nativeStreamingGeneratedEdgeLabels_global]
  unfold nativeStreamingGeneratedEdgeGlobalLabels
  split_ifs
  · rw [CavityGeneratedClockLabel.append_reindex_value,
      nativeStreamingGeneratedSharedFutureBranchBase_label_value,
      CavityGeneratedClockLabel.append_reindex_value,
      nativeStreamingGeneratedSharedFutureHistoryEraseBranch_prefix]
  · simp only [CavityGeneratedClockLabel.value,
      nativeStreamingGeneratedSharedFutureHistoryEraseBranch,Fin.snoc_last]
  · rw [CavityGeneratedClockLabel.append_reindex_value,
      nativeStreamingGeneratedSharedFutureBranchBase_label_value,
      CavityGeneratedClockLabel.append_reindex_value,
      nativeStreamingGeneratedSharedFutureHistoryEraseBranch_prefix]

def nativeStreamingGeneratedSharedFutureBranchMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap ((m+1)+1)) : ℝ :=
  nativeStreamingGeneratedSharedFutureMoment D μ a W v e F
    (nativeStreamingGeneratedSharedFutureHistoryEraseBranch H)

theorem nativeStreamingGeneratedSharedFutureBranchMoment_eq_constructed
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap ((m+1)+1)) :
    nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F H =
      nativeStreamingGeneratedSharedFutureMoment D μ a
        (nativeStreamingGeneratedSharedFutureBranchBase W) v e
        (fun h => F (cavityGeneratedHistoryPrefix h)) H := by
  have hc := nativeStreamingGeneratedSharedFutureBranchComponent_clock W v b hb e hj H
  change nativeStreamingGeneratedComponentClock
    (nativeStreamingGeneratedEdgeObservedComponent (nativeStreamingGeneratedSharedFutureBranchBase W) e) H = _ at hc
  unfold nativeStreamingGeneratedSharedFutureBranchMoment
    nativeStreamingGeneratedSharedFutureMoment nativeStreamingGeneratedSharedFutureProbability
  rw [hc,nativeStreamingGeneratedSharedFutureHistoryEraseBranch_prefix]
  rfl


theorem continuous_nativeStreamingGeneratedSharedFutureBranchMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ, Continuous (fun h => F h σ)) :
    Continuous (nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F) :=
  (continuous_nativeStreamingGeneratedSharedFutureMoment D μ a W v e F hF).comp
    continuous_nativeStreamingGeneratedSharedFutureHistoryEraseBranch

theorem nativeStreamingGeneratedSharedFutureBranchMoment_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀h σ, |F h σ| ≤ C)
    (H : CavityGeneratedHistory Paper.Overlap ((m+1)+1)) :
    |nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F H| ≤ 2*C :=
  nativeStreamingGeneratedSharedFutureMoment_abs_le D μ a W v e F C hC hF _

end QuantitativeFollowup
