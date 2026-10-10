module
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceStates
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeHalfClosedFamilyIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossOriginMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFutureOriginMoments

@[expose] public section

/-! Every physical edge section of the actual source callbacks is
integrable. Finite terminal-spin tests supply all bounds internally. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem integrableOn_nativeStreamingCoalescedOriginalFresh
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (i : ObservationLeaf T)
    (e : NativeStreamingEdge T) :
    IntegrableOn (fun r => nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.edge e r)))
      (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
  let c := finiteCascadeCommonPathDepth T (observationLeafVertex T i) (nativeStreamingEdgeChildVertex e)
  have hG : ∀ σ, Continuous (fun r : Paper.Overlap => nativeStreamingOriginalFreshSpinTest T F i
      (nativeStreamingOldSelectedCommonClock c e.depth r (q c)) σ) :=
    fun σ => continuous_nativeStreamingOriginalFreshSpinTest_clock T F i _
      (continuous_nativeStreamingOldSelectedCommonClock c e.depth (q c)) σ
  have hc := continuousOn_nativeStreamingEdgeSingleFamilyMoment D μ a q hq T e _ hG
  exact (hc.integrableOn_compact isCompact_Icc).mono_set (fun r hr => ⟨hr.1.le,hr.2⟩)

theorem integrableOn_nativeStreamingCoalescedCurrent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀ σ, |F σ| ≤ C) (e : NativeStreamingEdge T) :
    IntegrableOn (fun r : Paper.Overlap => Paper.parisiCDF μ r *
      nativeStreamingPatternMoment D μ a q T F (.current (.edge e r)))
        (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
  let G := fun r => nativeStreamingDefectSpinTest T F r
  let g := nativeStreamingEdgeCurrentFamilyHalfClosedMoment D μ a q T e G
  have hG : ∀ σ, Continuous (fun r => G r σ) :=
    fun σ => continuous_nativeStreamingDefectSpinTest_clock T F id continuous_id σ
  have hm := ((Paper.parisiCDF_measurable μ).comp measurable_subtype_coe).mul
    (measurable_nativeStreamingEdgeCurrentFamilyHalfClosedMoment D μ a q hq T e G hG)
  have hi : Integrable (fun r : Paper.Overlap => Paper.parisiCDF μ r * g r)
      (parisiFreeMeasure μ a) := by
    apply (integrable_const (2*C)).mono' hm.aestronglyMeasurable
    exact .of_forall fun r => by
      change |Paper.parisiCDF μ r * g r| ≤ 2*C
      rw [abs_mul,abs_of_nonneg (Paper.parisiCDF_nonneg μ r)]
      exact (mul_le_mul (Paper.parisiCDF_le_one μ r)
        (nativeStreamingEdgeCurrentFamilyHalfClosedMoment_abs_le D μ a q T e G (2*C)
          (by positivity) (fun r σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF r σ) r)
            (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  apply hi.restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [g,G,nativeStreamingEdgeCurrentFamilyHalfClosedMoment,mem_Ioc.mp hr,and_self,ite_true,
    nativeStreamingPatternMoment,nativeStreamingOriginCurrentProbability,nativeStreamingOriginLevel]

theorem integrableOn_nativeStreamingCoalescedCrossVertex
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) :
    IntegrableOn (fun r => nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.vertex v)))
      (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
  let c := finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)
  have hG : ∀ σ, Continuous (fun r : Paper.Overlap => nativeStreamingDefectSpinTest T F
      (nativeStreamingOldSelectedCommonClock c e.depth r (q c)) σ) :=
    fun σ => continuous_nativeStreamingDefectSpinTest_clock T F _
      (continuous_nativeStreamingOldSelectedCommonClock c e.depth (q c)) σ
  have hc := continuousOn_nativeStreamingEdgeVertexFamilyMoment D μ a q hq T e v _ hG
  exact (hc.integrableOn_compact isCompact_Icc).mono_set (fun r hr => ⟨hr.1.le,hr.2⟩)

private theorem coalesced_integrable_ite
    {X : Type*} [MeasurableSpace X] (P : Measure X) (f g : X → ℝ)
    (s : Set X) [DecidablePred (·∈s)] (hs : MeasurableSet s) (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun x => if x∈s then f x else g x) P := by
  exact Integrable.piecewise hs hf.integrableOn hg.integrableOn

private theorem coalesced_pair_left_integrable
    (P : Measure Paper.Overlap) [IsFiniteMeasure P]
    (lo hi lo' hi' : Paper.Overlap) (A : Paper.Overlap × Paper.Overlap → ℝ)
    (hA : ContinuousOn A (Icc lo hi ×ˢ Icc lo' hi')) (l : Paper.Overlap)
    (hl : l ∈ Icc lo' hi') :
    IntegrableOn (fun r => A (r,l)) (Ioc lo hi) P := by
  have hp : ContinuousOn (fun r : Paper.Overlap => (r,l)) (Icc lo hi) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hc := hA.comp hp (fun r hr => ⟨hr,hl⟩)
  exact (hc.integrableOn_compact isCompact_Icc).mono_set (fun r hr => ⟨hr.1.le,hr.2⟩)

private theorem coalesced_pair_right_integrable
    (P : Measure Paper.Overlap) [IsFiniteMeasure P]
    (lo hi lo' hi' : Paper.Overlap) (A : Paper.Overlap × Paper.Overlap → ℝ)
    (hA : ContinuousOn A (Icc lo hi ×ˢ Icc lo' hi')) (l : Paper.Overlap)
    (hl : l ∈ Icc lo hi) :
    IntegrableOn (fun r => A (l,r)) (Ioc lo' hi') P := by
  have hp : ContinuousOn (fun r : Paper.Overlap => (l,r)) (Icc lo' hi') :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hc := hA.comp hp (fun r hr => ⟨hl,hr⟩)
  exact (hc.integrableOn_compact isCompact_Icc).mono_set (fun r hr => ⟨hr.1.le,hr.2⟩)

theorem integrableOn_nativeStreamingCoalescedCrossEdge_closed
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e f : NativeStreamingEdge T) (l : Paper.Overlap)
    (hl : l ∈ Icc (q (f.depth+1)) (q f.depth)) :
    IntegrableOn (fun r => nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.edge f l)))
      (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
  classical
  let c := finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f)
  let G := fun z : Paper.Overlap × Paper.Overlap => nativeStreamingDefectSpinTest T F
    (nativeStreamingSelectedCommonClock c e.depth f.depth z.1 z.2 (q c))
  have hG : ∀ σ, Continuous (fun z => G z σ) := fun σ =>
    continuous_nativeStreamingDefectSpinTest_clock T F _
      (continuous_nativeStreamingSelectedCommonClock c e.depth f.depth (q c)) σ
  have hi (p k : ℕ) : IntegrableOn (fun r => nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k r l) (G (r,l)))
        (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
    exact coalesced_pair_left_integrable (parisiFreeMeasure μ a)
      (q (e.depth+1)) (q e.depth) (q (f.depth+1)) (q f.depth)
      (fun z => nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k z.1 z.2) (G z))
      (continuousOn_nativeStreamingEdgePairFixedFamilyMoment D μ a q hq T e f p k G hG) l hl
  by_cases he : e.depth=f.depth
  · let A := fun p k r => nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k r l) (G (r,l))
    have H : IntegrableOn (fun r => if r<l then A 1 0 r else
        if l<r then A 0 1 r else A 0 0 r)
        (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) :=
      coalesced_integrable_ite _ _ _ {r | r<l}
        (measurableSet_lt measurable_id measurable_const) (hi 1 0)
        (coalesced_integrable_ite _ _ _ {r | l<r}
          (measurableSet_lt measurable_const measurable_id) (hi 0 1) (hi 0 0))
    apply H.congr
    exact .of_forall fun r => by
      simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,nativeStreamingOriginCommonClock]
      by_cases hrl : r<l
      · simp only [nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
          if_pos he,if_pos he.symm,if_pos hrl,if_neg (not_lt_of_gt hrl),ite_true,ite_false,A,G,c]
      · by_cases hlr : l<r
        · simp only [nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
            if_pos he,if_pos he.symm,if_neg hrl,if_pos hlr,ite_true,ite_false,A,G,c]
        · simp only [nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
            if_pos he,if_pos he.symm,if_neg hrl,if_neg hlr,ite_true,ite_false,A,G,c]
  · apply (hi 0 0).congr
    exact .of_forall fun r => by
      simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,nativeStreamingOriginCommonClock,
        nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
        if_neg he,if_neg (Ne.symm he),G,c]
theorem integrableOn_nativeStreamingCoalescedCrossEdge_closed_right
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e f : NativeStreamingEdge T) (l : Paper.Overlap)
    (hl : l ∈ Icc (q (e.depth+1)) (q e.depth)) :
    IntegrableOn (fun r => nativeStreamingPatternMoment D μ a q T F (.cross (.edge e l) (.edge f r)))
      (Ioc (q (f.depth+1)) (q f.depth)) (parisiFreeMeasure μ a) := by
  classical
  let c := finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f)
  let G := fun z : Paper.Overlap × Paper.Overlap => nativeStreamingDefectSpinTest T F
    (nativeStreamingSelectedCommonClock c e.depth f.depth z.1 z.2 (q c))
  have hG : ∀ σ, Continuous (fun z => G z σ) := fun σ =>
    continuous_nativeStreamingDefectSpinTest_clock T F _
      (continuous_nativeStreamingSelectedCommonClock c e.depth f.depth (q c)) σ
  have hi (p k : ℕ) : IntegrableOn (fun r => nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k l r) (G (l,r)))
        (Ioc (q (f.depth+1)) (q f.depth)) (parisiFreeMeasure μ a) := by
    exact coalesced_pair_right_integrable (parisiFreeMeasure μ a)
      (q (e.depth+1)) (q e.depth) (q (f.depth+1)) (q f.depth)
      (fun z => nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k z.1 z.2) (G z))
      (continuousOn_nativeStreamingEdgePairFixedFamilyMoment D μ a q hq T e f p k G hG) l hl
  by_cases he : e.depth=f.depth
  · let A := fun p k r => nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k l r) (G (l,r))
    have H : IntegrableOn (fun r => if r<l then A 0 1 r else
        if l<r then A 1 0 r else A 0 0 r)
        (Ioc (q (f.depth+1)) (q f.depth)) (parisiFreeMeasure μ a) :=
      coalesced_integrable_ite _ _ _ {r | r<l}
        (measurableSet_lt measurable_id measurable_const) (hi 0 1)
        (coalesced_integrable_ite _ _ _ {r | l<r}
          (measurableSet_lt measurable_const measurable_id) (hi 1 0) (hi 0 0))
    apply H.congr
    exact .of_forall fun r => by
      simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,nativeStreamingOriginCommonClock]
      by_cases hrl : r<l
      · simp only [nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
          if_pos he,if_pos he.symm,if_pos hrl,if_neg (not_lt_of_gt hrl),ite_true,ite_false,A,G,c]
      · by_cases hlr : l<r
        · simp only [nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
            if_pos he,if_pos he.symm,if_neg hrl,if_pos hlr,ite_true,ite_false,A,G,c]
        · simp only [nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
            if_pos he,if_pos he.symm,if_neg hrl,if_neg hlr,ite_true,ite_false,A,G,c]
  · apply (hi 0 0).congr
    exact .of_forall fun r => by
      simp only [nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,nativeStreamingOriginCommonClock,
        nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
        if_neg he,if_neg (Ne.symm he),G,c]
theorem integrableOn_nativeStreamingCoalescedCross_left
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (o : NativeStreamingOrigin T)
    (ho : nativeCoalescedOriginValid q o) :
    IntegrableOn (fun r => nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) o))
      (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
  cases o with
  | vertex v => exact integrableOn_nativeStreamingCoalescedCrossVertex D μ a q hq T F e v
  | edge f l => exact integrableOn_nativeStreamingCoalescedCrossEdge_closed D μ a q hq T F e f l ho

theorem integrableOn_nativeStreamingCoalescedCross_right
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (o : NativeStreamingOrigin T)
    (ho : nativeCoalescedOriginValid q o) :
    IntegrableOn (fun r => nativeStreamingPatternMoment D μ a q T F (.cross o (.edge e r)))
      (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
  cases o with
  | vertex v =>
      apply (integrableOn_nativeStreamingCoalescedCrossVertex D μ a q hq T F e v).congr
      exact .of_forall fun r => (nativeStreamingPatternMoment_cross_vertex_edge D μ a q T F v e r).symm
  | edge f l => exact integrableOn_nativeStreamingCoalescedCrossEdge_closed_right D μ a q hq T F f e l ho

theorem integrableOn_nativeStreamingCoalescedFuture
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀ σ, |F σ| ≤ C) (e : NativeStreamingEdge T) :
    IntegrableOn (fun r => nativeStreamingPatternFutureIntegral D μ a q T F (.edge e r))
      (Ioc (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
  unfold nativeStreamingPatternFutureIntegral
  exact integrable_finset_sum (Finset.range J) (fun j _ =>
    integrable_nativeStreamingEdgeFuturePattern_row D μ a q hq T e j ∅ F C hC hF)

end QuantitativeFollowup
