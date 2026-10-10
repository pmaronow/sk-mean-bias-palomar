module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeHalfClosedFamilyIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossOriginMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFutureOriginMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexFutureHalfClosedFamilyIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingNormalizerDefectIntegral

@[expose] public section

/-! Measurability of literal actual pattern moments on their true mark
cells. Halfclosed cells retain upper endpoint atoms. The shared-future
functions keep their strict mask, and equal selections keep the genuine
two-spin law. No law or slice-measurability hypothesis is supplied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem aestronglyMeasurable_nativeStreamingPatternMoment_originalFresh_edge_Ioc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (e : NativeStreamingEdge T) :
    AEStronglyMeasurable
      (fun r => nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.edge e r)))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  let c := finiteCascadeCommonPathDepth T (observationLeafVertex T i)
    (nativeStreamingEdgeChildVertex e)
  let G := fun r => nativeStreamingOriginalFreshSpinTest T F i
    (nativeStreamingOldSelectedCommonClock c e.depth r (q c))
  have hG σ : Continuous (fun r => G r σ) :=
    continuous_nativeStreamingOriginalFreshSpinTest_clock T F i _
      (continuous_nativeStreamingOldSelectedCommonClock c e.depth (q c)) σ
  apply (measurable_nativeStreamingEdgeSingleFamilyHalfClosedMoment
    D μ a q hq T e G hG).stronglyMeasurable.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [nativeStreamingEdgeSingleFamilyHalfClosedMoment,mem_Ioc.mp hr,and_self,ite_true,
    nativeStreamingPatternMoment,nativeStreamingOriginSingleProbability,
    nativeStreamingOriginCommonClock,G,c]

theorem aestronglyMeasurable_nativeStreamingPatternMoment_current_edge_Ioc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (e : NativeStreamingEdge T) :
    AEStronglyMeasurable
      (fun r => nativeStreamingPatternMoment D μ a q T F (.current (.edge e r)))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  let G := fun r => nativeStreamingDefectSpinTest T F r
  have hG σ : Continuous (fun r => G r σ) :=
    continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_id σ
  apply (measurable_nativeStreamingEdgeCurrentFamilyHalfClosedMoment
    D μ a q hq T e G hG).stronglyMeasurable.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [nativeStreamingEdgeCurrentFamilyHalfClosedMoment,mem_Ioc.mp hr,and_self,ite_true,
    nativeStreamingPatternMoment,nativeStreamingOriginCurrentProbability,
    nativeStreamingOriginLevel,G]

theorem aestronglyMeasurable_nativeStreamingPatternMoment_cross_edge_vertex_Ioc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) :
    AEStronglyMeasurable
      (fun r => nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.vertex v)))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  let c := finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)
  let G := fun r => nativeStreamingDefectSpinTest T F
    (nativeStreamingOldSelectedCommonClock c e.depth r (q c))
  have hG σ : Continuous (fun r => G r σ) :=
    continuous_nativeStreamingDefectSpinTest_clock T F _
      (continuous_nativeStreamingOldSelectedCommonClock c e.depth (q c)) σ
  apply (measurable_nativeStreamingEdgeVertexFamilyHalfClosedMoment
    D μ a q hq T e v G hG).stronglyMeasurable.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [nativeStreamingEdgeVertexFamilyHalfClosedMoment,mem_Ioc.mp hr,and_self,ite_true,
    nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,
    nativeStreamingOriginCommonClock,G,c]

theorem aestronglyMeasurable_nativeStreamingPatternMoment_cross_vertex_edge_Ioc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T) :
    AEStronglyMeasurable
      (fun r => nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.edge e r)))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  apply (aestronglyMeasurable_nativeStreamingPatternMoment_cross_edge_vertex_Ioc
    D μ a q hq T F e v).congr
  exact .of_forall fun r => (nativeStreamingPatternMoment_cross_vertex_edge D μ a q T F v e r).symm

theorem aestronglyMeasurable_nativeStreamingPatternMoment_cross_edges_Ioc_prod
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (e f : NativeStreamingEdge T) :
    AEStronglyMeasurable (fun z : Paper.Overlap×Paper.Overlap =>
      nativeStreamingPatternMoment D μ a q T F (.cross (.edge e z.1) (.edge f z.2)))
      (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
        ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth)))) := by
  let c := finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e)
    (nativeStreamingEdgeChildVertex f)
  let G := fun z : Paper.Overlap×Paper.Overlap => nativeStreamingDefectSpinTest T F
    (nativeStreamingSelectedCommonClock c e.depth f.depth z.1 z.2 (q c))
  have hG σ : Continuous (fun z => G z σ) :=
    continuous_nativeStreamingEdgePairDefectSpinTest T F c e.depth f.depth (q c) σ
  rw [Measure.prod_restrict]
  apply (measurable_nativeStreamingEdgePairFamilyHalfClosedMoment
    D μ a q hq T e f ∅ G hG).stronglyMeasurable.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
  have hm : nativeStreamingEdgePairHalfClosedCondition q e f z := ⟨hz.1,hz.2⟩
  simp only [nativeStreamingEdgePairFamilyHalfClosedMoment,hm,ite_true,
    nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,
    nativeStreamingOriginCommonClock,G,c]

theorem aestronglyMeasurable_nativeStreamingPatternMoment_future_vertex_Ioc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) (j : ℕ) :
    AEStronglyMeasurable (fun l => if q v.depth<l then
      nativeStreamingPatternMoment D μ a q T F (.future (.vertex v) j l) else 0)
      ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))) := by
  let G := fun l => nativeStreamingDefectSpinTest T F l
  have hG σ : Continuous (fun l => G l σ) :=
    continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_id σ
  apply (measurable_nativeStreamingVertexFutureFamilyHalfClosedMoment
    D μ a q hq T v j ∅ G hG).stronglyMeasurable.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
  simp only [nativeStreamingVertexFutureFamilyHalfClosedMoment,
    nativeStreamingVertexFutureHalfClosedCondition,hl.1,hl.2,true_and,
    nativeStreamingPatternMoment,nativeStreamingOriginFutureProbability,G]

theorem aestronglyMeasurable_nativeStreamingPatternMoment_future_edge_Ioc_prod
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (e : NativeStreamingEdge T) (j : ℕ) :
    AEStronglyMeasurable (fun z : Paper.Overlap×Paper.Overlap => if z.1<z.2 then
      nativeStreamingPatternMoment D μ a q T F (.future (.edge e z.1) j z.2) else 0)
      (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
        ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))) := by
  let G := fun z : Paper.Overlap×Paper.Overlap => nativeStreamingDefectSpinTest T F z.2
  have hG σ : Continuous (fun z => G z σ) :=
    continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_snd σ
  rw [Measure.prod_restrict]
  apply (measurable_nativeStreamingEdgeFutureFamilyHalfClosedMoment
    D μ a q hq T e j ∅ G hG).stronglyMeasurable.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
  have he : q (e.depth+1)<z.1 ∧ z.1≤q e.depth := hz.1
  have hf : q (j+1)<z.2 ∧ z.2≤q j := hz.2
  simp only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,
    nativeStreamingEdgeFutureHalfClosedCondition,he,hf,true_and,
    nativeStreamingPatternMoment,nativeStreamingOriginFutureProbability,G]

theorem aestronglyMeasurable_nativeStreamingPatternMoment_normalizer
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    AEStronglyMeasurable
      (fun l => nativeStreamingPatternMoment D μ a q T F (.normalizer l))
      (parisiFreeMeasure μ a) := by
  have hm : AEStronglyMeasurable
      (fun l => nativeStreamingOldTerminalExpectation D μ a q T F *
        nativeStreamingFreshDefectMoment D μ a l) (parisiFreeMeasure μ a) :=
    (continuous_const.mul (continuous_nativeStreamingFreshDefectMoment D μ a)).stronglyMeasurable.aestronglyMeasurable
  apply hm.congr
  exact .of_forall fun l => by
    change nativeStreamingOldTerminalExpectation D μ a q T F *
      nativeStreamingFreshDefectMoment D μ a l =
        nativeStreamingPatternMoment D μ a q T F (.normalizer l)
    rw [nativeStreamingPatternMoment_normalizer_independent,nativeStreamingFreshDefectMoment_eq_fresh]

end QuantitativeFollowup
