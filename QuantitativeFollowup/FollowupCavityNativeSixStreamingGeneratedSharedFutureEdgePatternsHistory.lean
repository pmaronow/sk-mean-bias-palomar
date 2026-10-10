module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFutureEdgePatternsMoments
public import QuantitativeFollowup.FollowupCavityGeneratedMarkCubic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Two genuine free draws use one final joint restriction in the original
prefix. The receiver retains both free measures, with no singleton or CDF
weight at either inserted coordinate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedSharedFutureEdgeSecondRestriction
    (E : Set (CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap))) :
    Set (CavityGeneratedHistory Paper.Overlap (m+1) × Paper.Overlap) :=
  {z | (cavityGeneratedHistoryPrefix z.1,(z.1 (Fin.last m),z.2))∈E}

def nativeStreamingGeneratedSharedFutureEdgeFreeProgram
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap))) :
    CavityGeneratedMarkProgram Paper.Overlap (m+2) :=
  .fresh (.fresh (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) univ)
    (nativeStreamingGeneratedSharedFutureEdgeSecondRestriction E)

theorem nativeStreamingGeneratedSharedFutureEdgeFreeProgram_budget
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap))) :
    (nativeStreamingGeneratedSharedFutureEdgeFreeProgram P W E).budget=P.budget := rfl

private theorem sharedFutureEdge_doubleAppend_measurable :
    Measurable (fun z : (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap) × Paper.Overlap =>
      nativeStreamingGeneratedCrossEdgeAppend z.1.1 z.1.2 z.2) := by
  exact cavityGeneratedHistoryAppend_measurable.comp
    (cavityGeneratedHistoryAppend_measurable.prodMap measurable_id)

private theorem sharedFutureEdge_doubleAppend_continuous :
    Continuous (fun z : (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap) × Paper.Overlap =>
      nativeStreamingGeneratedCrossEdgeAppend z.1.1 z.1.2 z.2) := by
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [nativeStreamingGeneratedCrossEdgeAppend,Fin.snoc_last] using continuous_snd
  | cast i =>
    cases i using Fin.lastCases with
    | last => simpa only [nativeStreamingGeneratedCrossEdgeAppend,Fin.snoc_castSucc,Fin.snoc_last] using continuous_fst.snd
    | cast i => simpa only [nativeStreamingGeneratedCrossEdgeAppend,Fin.snoc_castSucc,Function.comp_def] using
        (continuous_apply i).comp continuous_fst.fst

theorem nativeStreamingGeneratedSharedFutureEdgeFreeProgram_measure
    (ν : Measure Paper.Overlap) [IsFiniteMeasure ν] (hν : ν univ≤1)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap)))
    (hE : MeasurableSet E) :
    (nativeStreamingGeneratedSharedFutureEdgeFreeProgram P W E).measure ν=
      (((((P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W)).prod ν).prod ν).restrict
        {z | (z.1.1,(z.1.2,z.2))∈E}).map
          (fun z => nativeStreamingGeneratedCrossEdgeAppend z.1.1 z.1.2 z.2) := by
  haveI := P.isFiniteMeasure_measure ν hν
  have hs : MeasurableSet (nativeStreamingGeneratedSharedFutureEdgeSecondRestriction E) :=
    hE.preimage ((cavityGeneratedHistoryPrefix_measurable.comp measurable_fst).prodMk
      (((measurable_pi_apply (Fin.last m)).comp measurable_fst).prodMk measurable_snd))
  let M := (P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W)
  have hm : Measurable (Prod.map (cavityGeneratedHistoryAppend (Q:=Paper.Overlap) (m:=m))
      (id : Paper.Overlap → Paper.Overlap)) :=
    (cavityGeneratedHistoryAppend_measurable (Q:=Paper.Overlap) (m:=m)).prodMap
      (measurable_id : Measurable (id : Paper.Overlap → Paper.Overlap))
  change (((((M.prod ν).restrict univ).map cavityGeneratedHistoryAppend).prod ν).restrict
    (nativeStreamingGeneratedSharedFutureEdgeSecondRestriction E)).map cavityGeneratedHistoryAppend = _
  have hp : ((M.prod ν).map (cavityGeneratedHistoryAppend (Q:=Paper.Overlap) (m:=m))).prod ν=
      ((M.prod ν).prod ν).map (Prod.map cavityGeneratedHistoryAppend id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map (M.prod ν) ν
      cavityGeneratedHistoryAppend_measurable measurable_id
  rw [Measure.restrict_univ,hp,Measure.restrict_map hm hs,
    Measure.map_map cavityGeneratedHistoryAppend_measurable hm]
  have he :
      Prod.map (cavityGeneratedHistoryAppend (Q:=Paper.Overlap) (m:=m))
          (id : Paper.Overlap → Paper.Overlap) ⁻¹'
        nativeStreamingGeneratedSharedFutureEdgeSecondRestriction E =
      {z : (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap) × Paper.Overlap |
        (z.1.1,(z.1.2,z.2))∈E} := by
    ext z
    simp only [nativeStreamingGeneratedSharedFutureEdgeSecondRestriction,Set.mem_preimage,Set.mem_setOf_eq,
      Prod.map_fst,Prod.map_snd,id_eq,cavityGeneratedHistoryAppend,cavityGeneratedHistoryPrefix_snoc,Fin.snoc_last]
  rw [he]
  rfl

private theorem integral_sharedFutureEdge_two_fresh
    (ν : Measure Paper.Overlap) [IsFiniteMeasure ν] (hν : ν univ≤1)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap)))
    (hE : MeasurableSet E) (G : CavityGeneratedHistory Paper.Overlap (m+2) → ℝ)
    (hG : Continuous G) (C : ℝ) (hbound : ∀H, ‖G H‖≤C) :
    (∫H, G H ∂(nativeStreamingGeneratedSharedFutureEdgeFreeProgram P W E).measure ν)=
      ∫h, ∫r, ∫l, G (nativeStreamingGeneratedCrossEdgeAppend h r l)
        ∂ν.restrict {l | (h,(r,l))∈E} ∂ν
        ∂(P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W) := by
  haveI := P.isFiniteMeasure_measure ν hν
  let M := (P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W)
  let E' : Set ((CavityGeneratedHistory Paper.Overlap m × Paper.Overlap) × Paper.Overlap) :=
    {z | (z.1.1,(z.1.2,z.2))∈E}
  have hE' : MeasurableSet E' := hE.preimage
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  let g := fun z : (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap) × Paper.Overlap =>
    G (nativeStreamingGeneratedCrossEdgeAppend z.1.1 z.1.2 z.2)
  have hg : Integrable g ((M.prod ν).prod ν) :=
    (integrable_const C).mono' (hG.comp sharedFutureEdge_doubleAppend_continuous).aestronglyMeasurable
      (.of_forall fun z => hbound _)
  rw [nativeStreamingGeneratedSharedFutureEdgeFreeProgram_measure ν hν P W E hE,
    integral_map sharedFutureEdge_doubleAppend_measurable.aemeasurable hG.aestronglyMeasurable,
    ←integral_indicator hE',integral_prod _ (hg.indicator hE'),
    integral_prod _ (hg.indicator hE').integral_prod_left]
  apply integral_congr_ae
  exact .of_forall fun h => by
    apply integral_congr_ae
    exact .of_forall fun r => by
      dsimp only
      have hs : MeasurableSet {l : Paper.Overlap | (h,(r,l))∈E} :=
        hE.preimage (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      rw [←integral_indicator hs]
      rfl

theorem integrable_nativeStreamingGeneratedSharedFutureEdgeMoment
    (ν : Measure Paper.Overlap) [IsFiniteMeasure ν] (hν : ν univ≤1)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (e : NativeStreamingEdge W.tree) (j : ℕ) (hj : j≤e.depth)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap)))
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ,Continuous (fun h => F h σ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀h σ,|F h σ|≤C) :
    Integrable (nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F)
      ((nativeStreamingGeneratedSharedFutureEdgeFreeProgram P W E).measure ν) := by
  haveI := (nativeStreamingGeneratedSharedFutureEdgeFreeProgram P W E).isFiniteMeasure_measure ν hν
  apply (integrable_const (2*C)).mono'
    (continuous_nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F hF).aestronglyMeasurable
  exact .of_forall fun H => by
    simpa only [Real.norm_eq_abs] using
      nativeStreamingGeneratedSharedFutureEdgeMoment_abs_le D μ a W e j hj F C hC hbound H

theorem nativeStreamingGeneratedSharedFutureEdge_restricted_receiver
    (ν : Measure Paper.Overlap) [IsFiniteMeasure ν] (hν : ν univ≤1)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (e : NativeStreamingEdge W.tree) (j : ℕ) (hj : j≤e.depth)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap)))
    (hE : MeasurableSet E)
    (hcell : ∀z∈E,
      (nativeStreamingGeneratedComponentClock W z.1 (e.depth+1)≤z.2.1 ∧ z.2.1≤nativeStreamingGeneratedComponentClock W z.1 e.depth) ∧
      (nativeStreamingGeneratedComponentClock W z.1 (j+1)≤z.2.2 ∧ z.2.2≤nativeStreamingGeneratedComponentClock W z.1 j) ∧
      z.2.1<z.2.2)
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ,Continuous (fun h => F h σ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀h σ,|F h σ|≤C) :
    (∫H,nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F H
      ∂(nativeStreamingGeneratedSharedFutureEdgeFreeProgram P W E).measure ν)=
      ∫h,∫r,∫l,nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.future (.edge e r) j l)
        ∂ν.restrict {l | (h,(r,l))∈E} ∂ν
        ∂(P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W) := by
  have H := integral_sharedFutureEdge_two_fresh ν hν P W E hE
    (nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F)
    (continuous_nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F hF)
    (2*C) (fun H => by simpa only [Real.norm_eq_abs] using
      nativeStreamingGeneratedSharedFutureEdgeMoment_abs_le D μ a W e j hj F C hC hbound H)
  apply H.trans
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isClosed_nativeStreamingGeneratedComponentOrderSet W).measurableSet] with h hh
  apply integral_congr_ae
  exact .of_forall fun r => by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurable_prodMk_left hE |>.preimage
      (measurable_const.prodMk measurable_id))] with l hl
    have he := hcell (h,(r,l)) hl
    exact nativeStreamingGeneratedSharedFutureEdgeMoment_append D μ a W e j hj F h r l hh he.1 he.2.1 he.2.2

theorem nativeStreamingGeneratedSharedFutureEdge_actual_free_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0≤a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (W : CavityGeneratedConstructedComponent m)
    (e : NativeStreamingEdge W.tree) (j : ℕ) (hj : j≤e.depth)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × (Paper.Overlap×Paper.Overlap)))
    (hE : MeasurableSet E)
    (hcell : ∀z∈E,
      (nativeStreamingGeneratedComponentClock W z.1 (e.depth+1)≤z.2.1 ∧ z.2.1≤nativeStreamingGeneratedComponentClock W z.1 e.depth) ∧
      (nativeStreamingGeneratedComponentClock W z.1 (j+1)≤z.2.2 ∧ z.2.2≤nativeStreamingGeneratedComponentClock W z.1 j) ∧ z.2.1<z.2.2)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ,Continuous (fun h => F h σ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀h σ,|F h σ|≤C) :
    (∫H,nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F H
      ∂(nativeStreamingGeneratedSharedFutureEdgeFreeProgram P W E).measure (parisiFreeMeasure μ a))=
      ∫h,∫r,∫l,nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.future (.edge e r) j l)
        ∂(parisiFreeMeasure μ a).restrict {l | (h,(r,l))∈E} ∂(parisiFreeMeasure μ a)
        ∂(P.measure (parisiFreeMeasure μ a)).restrict (nativeStreamingGeneratedComponentOrderSet W) :=
  nativeStreamingGeneratedSharedFutureEdge_restricted_receiver _ (cavityGenerated_free_mass_le_one μ a ha)
    P W e j hj E hE hcell D μ a F hF C hC hbound

end QuantitativeFollowup
