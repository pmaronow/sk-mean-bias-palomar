module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFutureEdgePatternsHistory

@[expose] public section

/-! Literal strict-future two-cell source receivers. Both cells are evaluated
at the original prefix. Inclusive-cell receivers remain available for the
halfclosed atomic partition; the printed open-cell form is a corollary. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedSharedFutureEdgeSourceSet
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) (j : ℕ) :
    Set (CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap)) :=
  {z | z.2.1∈Ioo (nativeStreamingGeneratedComponentClock W z.1 (e.depth+1))
      (nativeStreamingGeneratedComponentClock W z.1 e.depth) ∧
    z.2.2∈Ioo (nativeStreamingGeneratedComponentClock W z.1 (j+1))
      (nativeStreamingGeneratedComponentClock W z.1 j) ∧ z.2.1<z.2.2}

theorem measurableSet_nativeStreamingGeneratedSharedFutureEdgeSourceSet
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) (j : ℕ) :
    MeasurableSet (nativeStreamingGeneratedSharedFutureEdgeSourceSet W e j) := by
  have hc (k : ℕ) : Continuous (fun z : CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap) =>
      nativeStreamingGeneratedComponentClock W z.1 k) :=
    (nativeStreamingGeneratedComponentClock_continuous W k).comp continuous_fst
  exact ((isOpen_lt (hc (e.depth+1)) continuous_snd.fst).measurableSet.inter
    (isOpen_lt continuous_snd.fst (hc e.depth)).measurableSet).inter
      (((isOpen_lt (hc (j+1)) continuous_snd.snd).measurableSet.inter
        (isOpen_lt continuous_snd.snd (hc j)).measurableSet).inter
          (isOpen_lt continuous_snd.fst continuous_snd.snd).measurableSet)

theorem nativeStreamingGeneratedSharedFutureEdge_later_cell_impossible
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : e.depth<j) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r)
    (hl : l≤nativeStreamingGeneratedComponentClock W h j) (hrl : r<l) : False := by
  have hq := nativeStreamingGeneratedComponentClock_antitone W h (show e.depth+1≤j by omega)
  exact (not_lt_of_ge (hl.trans (hq.trans hr))) hrl

theorem nativeStreamingGeneratedSharedFutureEdgeSourceSet_empty_of_later_cell
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : e.depth<j) : nativeStreamingGeneratedSharedFutureEdgeSourceSet W e j=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact nativeStreamingGeneratedSharedFutureEdge_later_cell_impossible W e j hj z.1 z.2.1 z.2.2
    hz.1.1.le hz.2.1.2.le hz.2.2

theorem nativeStreamingGeneratedSharedFutureEdgeSourceSet_empty_of_repeated
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree) (j : ℕ)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (he : nativeStreamingGeneratedComponentClock W h (e.depth+1)=nativeStreamingGeneratedComponentClock W h e.depth) :
    {z : Paper.Overlap×Paper.Overlap | (h,z)∈nativeStreamingGeneratedSharedFutureEdgeSourceSet W e j}=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hr := hz.1
  rw [he] at hr
  exact lt_asymm hr.1 hr.2

theorem nativeStreamingGeneratedSharedFutureEdge_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0≤a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (e : NativeStreamingEdge W.tree) (j : ℕ) (hj : j≤e.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ,Continuous (fun h => F h σ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀h σ,|F h σ|≤C) :
    (∫H,nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F H
      ∂(nativeStreamingGeneratedSharedFutureEdgeFreeProgram P W
        (nativeStreamingGeneratedSharedFutureEdgeSourceSet W e j)).measure (parisiFreeMeasure μ a))=
      ∫h,∫r,∫l,nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.future (.edge e r) j l)
        ∂(parisiFreeMeasure μ a).restrict (Ioo (nativeStreamingGeneratedComponentClock W h (j+1))
          (nativeStreamingGeneratedComponentClock W h j) ∩ Ioi r)
        ∂(parisiFreeMeasure μ a).restrict (Ioo (nativeStreamingGeneratedComponentClock W h (e.depth+1))
          (nativeStreamingGeneratedComponentClock W h e.depth))
        ∂(P.measure (parisiFreeMeasure μ a)).restrict (nativeStreamingGeneratedComponentOrderSet W) := by
  have H := nativeStreamingGeneratedSharedFutureEdge_actual_free_receiver D μ a ha P W e j hj
    (nativeStreamingGeneratedSharedFutureEdgeSourceSet W e j)
    (measurableSet_nativeStreamingGeneratedSharedFutureEdgeSourceSet W e j)
    (fun z hz => ⟨⟨hz.1.1.le,hz.1.2.le⟩,⟨hz.2.1.1.le,hz.2.1.2.le⟩,hz.2.2⟩) F hF C hC hbound
  apply H.trans
  apply integral_congr_ae
  exact .of_forall fun h => by
    let A := Ioo (nativeStreamingGeneratedComponentClock W h (e.depth+1))
      (nativeStreamingGeneratedComponentClock W h e.depth)
    let G : Paper.Overlap → Paper.Overlap → ℝ := fun r l =>
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.future (.edge e r) j l)
    change (∫r,∫l,G r l
        ∂(parisiFreeMeasure μ a).restrict {l | (h,(r,l))∈nativeStreamingGeneratedSharedFutureEdgeSourceSet W e j}
        ∂parisiFreeMeasure μ a)=
      ∫r,∫l,G r l
        ∂(parisiFreeMeasure μ a).restrict (Ioo (nativeStreamingGeneratedComponentClock W h (j+1))
          (nativeStreamingGeneratedComponentClock W h j) ∩ Ioi r)
        ∂(parisiFreeMeasure μ a).restrict A
    rw [←integral_indicator (s:=A) measurableSet_Ioo]
    apply integral_congr_ae
    exact .of_forall fun r => by
      dsimp only
      by_cases hr : r∈A
      · rw [Set.indicator_of_mem hr]
        have he : {l | (h,(r,l))∈nativeStreamingGeneratedSharedFutureEdgeSourceSet W e j}=
            Ioo (nativeStreamingGeneratedComponentClock W h (j+1))
              (nativeStreamingGeneratedComponentClock W h j) ∩ Ioi r := by
          ext l
          change (r∈A ∧ l∈Ioo (nativeStreamingGeneratedComponentClock W h (j+1))
            (nativeStreamingGeneratedComponentClock W h j) ∧ r<l) ↔ _
          simp only [hr,true_and,Set.mem_inter_iff,Set.mem_Ioi]
        rw [he]
      · rw [Set.indicator_of_notMem hr]
        have he : {l | (h,(r,l))∈nativeStreamingGeneratedSharedFutureEdgeSourceSet W e j}=∅ := by
          ext l
          change (r∈A ∧ l∈Ioo (nativeStreamingGeneratedComponentClock W h (j+1))
            (nativeStreamingGeneratedComponentClock W h j) ∧ r<l) ↔ False
          simp only [hr,false_and]
        rw [he,Measure.restrict_empty,integral_zero_measure]

end QuantitativeFollowup
