module
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixPayload
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMarkMeasurable

@[expose] public section

/-! Ordinary global measurability of actual selected source payloads.
The equalities use genuine halfclosed family moments on every point,
including zero exterior sections, rather than arbitrary versions of AE slices. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem measurable_sum_left
    {A B X : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    (f : (A⊕B)×X→ℝ)
    (hA : Measurable (fun z : A×X=>f (Sum.inl z.1,z.2)))
    (hB : Measurable (fun z : B×X=>f (Sum.inr z.1,z.2))) : Measurable f := by
  convert (hA.sumElim hB).comp (MeasurableEquiv.sumProdDistrib A B X).measurable using 1
  funext z
  rcases z with ⟨a|b,x⟩ <;> rfl

private theorem measurable_selected_product
    {X : Type*} [MeasurableSpace X] (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (Φ : NativeStreamingOrigin T→X→ℝ)
    (hV : ∀v,Measurable (Φ (.vertex v)))
    (hE : ∀e,Measurable (fun z : Paper.Overlap×X=>
      if z.1∈Ioc (q (e.depth+1)) (q e.depth) then Φ (.edge e z.1) z.2 else 0)) :
    Measurable (fun z : CavityGeneratedOriginSelection T×X=>
      cavityGeneratedSelectedOriginPayload q T (fun o=>Φ o z.2) z.1) := by
  apply measurable_sum_left
  · apply measurable_from_prod_countable_right
    intro i
    simpa only [cavityGeneratedSelectedOriginPayload,cavityGeneratedOriginSelectionOrigin,
      cavityGeneratedOriginCellMask] using hV ((cavityGeneratedOriginForkVertices T).get i)
  · apply measurable_sum_left
    · have hm : Measurable (fun z : Fin (cavityGeneratedOriginEdges T).length×(Paper.Overlap×X)=>
          if z.2.1∈Ioc (q (((cavityGeneratedOriginEdges T).get z.1).depth+1))
            (q ((cavityGeneratedOriginEdges T).get z.1).depth) then
            Φ (.edge ((cavityGeneratedOriginEdges T).get z.1) z.2.1) z.2.2 else 0) :=
        measurable_from_prod_countable_right (fun i=>hE ((cavityGeneratedOriginEdges T).get i))
      have ht : Measurable (fun z : (Fin (cavityGeneratedOriginEdges T).length×Paper.Overlap)×X=>
          (z.1.1,(z.1.2,z.2))) :=
        measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
      simpa only [Function.comp_def,cavityGeneratedSelectedOriginPayload,
        cavityGeneratedOriginSelectionOrigin,cavityGeneratedOriginCellMask] using hm.comp ht
    · apply measurable_from_prod_countable_right
      intro u
      simpa only [cavityGeneratedSelectedOriginPayload,cavityGeneratedOriginSelectionOrigin,
        cavityGeneratedOriginCellMask] using hV (.root T)

private theorem selectedOriginPayload_ite
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (b : Prop) (Φ : NativeStreamingOrigin T→ℝ) (g : CavityGeneratedOriginSelection T) :
    cavityGeneratedSelectedOriginPayload q T (fun o=>if b then Φ o else 0) g =
      if b then cavityGeneratedSelectedOriginPayload q T Φ g else 0 := by
  by_cases hb : b
  · simp only [hb,ite_true]
  · simp only [hb,ite_false]
    unfold cavityGeneratedSelectedOriginPayload
    cases cavityGeneratedOriginSelectionOrigin T g <;>
      simp only [cavityGeneratedOriginCellMask,ite_self]

private theorem measurable_originalFresh_mask
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (i : ObservationLeaf T) (e : NativeStreamingEdge T) :
    Measurable (fun r=>if r∈Ioc (q (e.depth+1)) (q e.depth) then
      nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.edge e r)) else 0) := by
  let c := finiteCascadeCommonPathDepth T (observationLeafVertex T i) (nativeStreamingEdgeChildVertex e)
  let G := fun r=>nativeStreamingOriginalFreshSpinTest T F i
    (nativeStreamingOldSelectedCommonClock c e.depth r (q c))
  have hG σ : Continuous (fun r=>G r σ) :=
    continuous_nativeStreamingOriginalFreshSpinTest_clock T F i _
      (continuous_nativeStreamingOldSelectedCommonClock c e.depth (q c)) σ
  convert measurable_nativeStreamingEdgeSingleFamilyHalfClosedMoment D μ a q hq T e G hG using 1
  funext r
  by_cases hr : q (e.depth+1)<r ∧ r≤q e.depth <;>
    simp only [mem_Ioc,nativeStreamingEdgeSingleFamilyHalfClosedMoment,hr,ite_true,ite_false,
      nativeStreamingPatternMoment,nativeStreamingOriginSingleProbability,
      nativeStreamingOriginCommonClock,G,c]

private theorem measurable_current_mask
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (e : NativeStreamingEdge T) :
    Measurable (fun r=>if r∈Ioc (q (e.depth+1)) (q e.depth) then
      Paper.parisiCDF μ r*nativeStreamingPatternMoment D μ a q T F (.current (.edge e r)) else 0) := by
  let G := fun r=>nativeStreamingDefectSpinTest T F r
  have hG σ : Continuous (fun r=>G r σ) :=
    continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_id σ
  convert measurable_nativeStreamingEdgeCurrentCDFHalfClosedMoment D μ a q hq T e G hG using 1
  funext r
  by_cases hr : q (e.depth+1)<r ∧ r≤q e.depth <;>
    simp only [mem_Ioc,nativeStreamingEdgeCurrentCDFHalfClosedMoment,
      nativeStreamingEdgeCurrentFamilyHalfClosedMoment,hr,ite_true,ite_false,mul_zero,
      nativeStreamingPatternMoment,nativeStreamingOriginCurrentProbability,nativeStreamingOriginLevel,G,and_self]

private theorem measurable_cross_EV_mask
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (e : NativeStreamingEdge T)
    (v : FiniteCascadeRecordVertex T) :
    Measurable (fun r=>if r∈Ioc (q (e.depth+1)) (q e.depth) then
      nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.vertex v)) else 0) := by
  let c := finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)
  let G := fun r=>nativeStreamingDefectSpinTest T F
    (nativeStreamingOldSelectedCommonClock c e.depth r (q c))
  have hG σ : Continuous (fun r=>G r σ) :=
    continuous_nativeStreamingDefectSpinTest_clock T F _
      (continuous_nativeStreamingOldSelectedCommonClock c e.depth (q c)) σ
  convert measurable_nativeStreamingEdgeVertexFamilyHalfClosedMoment D μ a q hq T e v G hG using 1
  funext r
  by_cases hr : q (e.depth+1)<r ∧ r≤q e.depth <;>
    simp only [mem_Ioc,nativeStreamingEdgeVertexFamilyHalfClosedMoment,hr,ite_true,ite_false,
      nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,
      nativeStreamingOriginCommonClock,G,c]

private theorem measurable_cross_VE_mask
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (v : FiniteCascadeRecordVertex T)
    (e : NativeStreamingEdge T) :
    Measurable (fun r=>if r∈Ioc (q (e.depth+1)) (q e.depth) then
      nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.edge e r)) else 0) := by
  convert measurable_cross_EV_mask D μ a q hq T F e v using 1
  funext r
  rw [nativeStreamingPatternMoment_cross_vertex_edge]

private theorem measurable_cross_EE_mask
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (e f : NativeStreamingEdge T) :
    Measurable (fun z : Paper.Overlap×Paper.Overlap=>
      if z.1∈Ioc (q (e.depth+1)) (q e.depth) then
        if z.2∈Ioc (q (f.depth+1)) (q f.depth) then
          nativeStreamingPatternMoment D μ a q T F (.cross (.edge e z.1) (.edge f z.2)) else 0
      else 0) := by
  let c := finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f)
  let G := fun z : Paper.Overlap×Paper.Overlap=>nativeStreamingDefectSpinTest T F
    (nativeStreamingSelectedCommonClock c e.depth f.depth z.1 z.2 (q c))
  have hG σ : Continuous (fun z=>G z σ) :=
    continuous_nativeStreamingEdgePairDefectSpinTest T F c e.depth f.depth (q c) σ
  convert measurable_nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q hq T e f ∅ G hG using 1
  funext z
  by_cases he : q (e.depth+1)<z.1 ∧ z.1≤q e.depth <;>
    by_cases hf : q (f.depth+1)<z.2 ∧ z.2≤q f.depth <;>
    simp only [mem_Ioc,nativeStreamingEdgePairHalfClosedCondition,
      nativeStreamingEdgePairFamilyHalfClosedMoment,he,hf,and_self,true_and,false_and,
      and_true,and_false,ite_true,ite_false,nativeStreamingPatternMoment,
      nativeStreamingOriginCrossProbability,nativeStreamingOriginCommonClock,G,c]

private theorem measurable_future_V_mask
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (v : FiniteCascadeRecordVertex T) (j : ℕ) :
    Measurable (fun l=>if l∈Ioc (q (j+1)) (q j) ∧ q v.depth<l then
      nativeStreamingPatternMoment D μ a q T F (.future (.vertex v) j l) else 0) := by
  let G := fun l=>nativeStreamingDefectSpinTest T F l
  have hG σ : Continuous (fun l=>G l σ) :=
    continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_id σ
  convert measurable_nativeStreamingVertexFutureFamilyHalfClosedMoment D μ a q hq T v j ∅ G hG using 1
  funext l
  simp only [mem_Ioc,nativeStreamingVertexFutureHalfClosedCondition,and_assoc,
    nativeStreamingVertexFutureFamilyHalfClosedMoment,nativeStreamingPatternMoment,
    nativeStreamingOriginFutureProbability,G]

private theorem measurable_future_E_mask
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (e : NativeStreamingEdge T) (j : ℕ) :
    Measurable (fun z : Paper.Overlap×Paper.Overlap=>
      if z.1∈Ioc (q (e.depth+1)) (q e.depth) then
        if z.2∈Ioc (q (j+1)) (q j) ∧ z.1<z.2 then
          nativeStreamingPatternMoment D μ a q T F (.future (.edge e z.1) j z.2) else 0
      else 0) := by
  let G := fun z : Paper.Overlap×Paper.Overlap=>nativeStreamingDefectSpinTest T F z.2
  have hG σ : Continuous (fun z=>G z σ) :=
    continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_snd σ
  convert measurable_nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q hq T e j ∅ G hG using 1
  funext z
  by_cases he : q (e.depth+1)<z.1 ∧ z.1≤q e.depth <;>
    simp only [mem_Ioc,nativeStreamingEdgeFutureHalfClosedCondition,
      nativeStreamingEdgeFutureFamilyHalfClosedMoment,he,true_and,false_and,ite_true,ite_false,
      nativeStreamingPatternMoment,nativeStreamingOriginFutureProbability,G]

theorem measurable_cavityGeneratedSelectedOriginalFreshPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (i : ObservationLeaf T) :
    Measurable (cavityGeneratedSelectedOriginalFreshPayload D μ a q T F i) :=
  measurable_cavityGeneratedSelectedOriginPayload q T _
    (measurable_originalFresh_mask D μ a q hq T F i)

theorem measurable_cavityGeneratedSelectedCurrentPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    Measurable (cavityGeneratedSelectedCurrentPayload D μ a q T F) := by
  apply measurable_cavityGeneratedSelectedOriginPayload
  intro e
  simpa only [nativeStreamingOriginLevel] using measurable_current_mask D μ a q hq T F e

theorem measurable_cavityGeneratedSelectedCrossPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    Measurable (cavityGeneratedSelectedCrossPayload D μ a q T F) := by
  apply measurable_selected_product q T
    (fun o g=>cavityGeneratedSelectedOriginPayload q T
      (fun p=>nativeStreamingPatternMoment D μ a q T F (.cross o p)) g)
  · intro v
    exact measurable_cavityGeneratedSelectedOriginPayload q T _
      (fun f=>measurable_cross_VE_mask D μ a q hq T F v f)
  · intro e
    have hm : Measurable (fun z : CavityGeneratedOriginSelection T×Paper.Overlap=>
        cavityGeneratedSelectedOriginPayload q T (fun p=>
          if z.2∈Ioc (q (e.depth+1)) (q e.depth) then
            nativeStreamingPatternMoment D μ a q T F (.cross (.edge e z.2) p) else 0) z.1) := by
      apply measurable_selected_product q T (fun p r=>
        if r∈Ioc (q (e.depth+1)) (q e.depth) then
          nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) p) else 0)
      · intro v
        exact measurable_cross_EV_mask D μ a q hq T F e v
      · intro f
        convert (measurable_cross_EE_mask D μ a q hq T F e f).comp measurable_swap using 1
        funext z
        by_cases he : z.2∈Ioc (q (e.depth+1)) (q e.depth) <;>
          by_cases hf : z.1∈Ioc (q (f.depth+1)) (q f.depth) <;>
          simp only [Function.comp_def,Prod.swap,he,hf,ite_true,ite_false]
    convert hm.comp measurable_swap using 1
    funext z
    have hx := (selectedOriginPayload_ite q T
      (z.1∈Ioc (q (e.depth+1)) (q e.depth))
      (fun p=>nativeStreamingPatternMoment D μ a q T F (.cross (.edge e z.1) p)) z.2).symm
    by_cases he : z.1∈Ioc (q (e.depth+1)) (q e.depth)
    · simpa only [Function.comp_def,Prod.swap,he,ite_true] using hx
    · simpa only [Function.comp_def,Prod.swap,he,ite_false] using hx

theorem measurable_cavityGeneratedSelectedFutureCellPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (j : ℕ) :
    Measurable (cavityGeneratedSelectedFutureCellPayload D μ a q T F j) := by
  apply measurable_selected_product q T (fun o l=>
    if l∈Ioc (q (j+1)) (q j) ∧ nativeStreamingOriginLevel q o<l then
      nativeStreamingPatternMoment D μ a q T F (.future o j l) else 0)
  · intro v
    simpa only [nativeStreamingOriginLevel] using measurable_future_V_mask D μ a q hq T F v j
  · intro e
    simpa only [nativeStreamingOriginLevel] using measurable_future_E_mask D μ a q hq T F e j

theorem measurable_cavityGeneratedSelectedFutureOriginCell
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (o : NativeStreamingOrigin T) (j : ℕ)
    (ho : match o with
      | .vertex _ => True
      | .edge e r => r∈Ioc (q (e.depth+1)) (q e.depth)) :
    Measurable (fun l=>if l∈Ioc (q (j+1)) (q j) ∧ nativeStreamingOriginLevel q o<l then
      nativeStreamingPatternMoment D μ a q T F (.future o j l) else 0) := by
  cases o with
  | vertex v =>
      simpa only [nativeStreamingOriginLevel] using measurable_future_V_mask D μ a q hq T F v j
  | edge e r =>
      have hm := (measurable_future_E_mask D μ a q hq T F e j).comp
        (measurable_const.prodMk measurable_id : Measurable (fun l : Paper.Overlap=>(r,l)))
      simpa only [Function.comp_def,ho,ite_true,nativeStreamingOriginLevel] using hm

theorem measurable_cavityGeneratedSelectedFuturePayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    Measurable (cavityGeneratedSelectedFuturePayload D μ a q T F) :=
  Finset.measurable_sum _ (fun j _=>measurable_cavityGeneratedSelectedFutureCellPayload D μ a q hq T F j)

end QuantitativeFollowup
