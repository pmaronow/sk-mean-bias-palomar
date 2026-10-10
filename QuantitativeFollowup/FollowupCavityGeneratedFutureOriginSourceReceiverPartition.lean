module
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginSourceReceiver
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixPayload
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternValueBounds

@[expose] public section

/-! The actual selected-origin kernel is supported on its original Ioc
edge cell. The finite future chart partition therefore reproduces the
literal selected future payload, including each upper atom exactly once. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

private def futureSourceValid
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) : CavityGeneratedOriginSelection (W.tree c) → Prop
  | .inl _ => True
  | .inr (.inl z) => z.2∈Ioc
      (W.clockTemplate.clock h c (((cavityGeneratedOriginEdges (W.tree c)).get z.1).depth+1))
      (W.clockTemplate.clock h c ((cavityGeneratedOriginEdges (W.tree c)).get z.1).depth)
  | .inr (.inr _) => True

private theorem futureSourceValid_measurableSet
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c) |
      futureSourceValid W c z.1 z.2} := by
  let H := CavityGeneratedHistory Paper.Overlap m
  let A := Fin (cavityGeneratedOriginForkVertices (W.tree c)).length
  let B := Fin (cavityGeneratedOriginEdges (W.tree c)).length × Paper.Overlap
  have hlo : Measurable (fun z : H × Fin (cavityGeneratedOriginEdges (W.tree c)).length =>
      W.clockTemplate.clock z.1 c (((cavityGeneratedOriginEdges (W.tree c)).get z.2).depth+1)) :=
    measurable_from_prod_countable_left (fun i=>by
      change Measurable (fun h : H => W.clockTemplate.clock h c
        (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1))
      exact (W.clockTemplate.clock_continuous c _).measurable)
  have hhi : Measurable (fun z : H × Fin (cavityGeneratedOriginEdges (W.tree c)).length =>
      W.clockTemplate.clock z.1 c ((cavityGeneratedOriginEdges (W.tree c)).get z.2).depth) :=
    measurable_from_prod_countable_left (fun i=>by
      change Measurable (fun h : H => W.clockTemplate.clock h c
        ((cavityGeneratedOriginEdges (W.tree c)).get i).depth)
      exact (W.clockTemplate.clock_continuous c _).measurable)
  have hecell : MeasurableSet {z : H×B | z.2.2∈Ioc
      (W.clockTemplate.clock z.1 c (((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth+1))
      (W.clockTemplate.clock z.1 c ((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth)} := by
    have hr : Measurable (fun z : H×B => z.2.2) := measurable_snd.snd
    have hlo' : Measurable (fun z : H×B => W.clockTemplate.clock z.1 c
        (((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth+1)) :=
      hlo.comp (measurable_fst.prodMk measurable_snd.fst)
    have hhi' : Measurable (fun z : H×B => W.clockTemplate.clock z.1 c
        ((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth) :=
      hhi.comp (measurable_fst.prodMk measurable_snd.fst)
    exact (measurableSet_lt (measurable_subtype_coe.comp hlo')
      (measurable_subtype_coe.comp hr)).inter
        (measurableSet_le (measurable_subtype_coe.comp hr)
          (measurable_subtype_coe.comp hhi'))
  have he : Measurable (fun z : H×B => if z.2.2∈Ioc
      (W.clockTemplate.clock z.1 c (((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth+1))
      (W.clockTemplate.clock z.1 c ((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth)
      then (1:ℝ) else 0) := measurable_const.ite hecell measurable_const
  have hi := (he.sumElim (measurable_const : Measurable (fun _ : H×Unit => (1:ℝ)))).comp
    (MeasurableEquiv.prodSumDistrib H B Unit).measurable
  have ho := ((measurable_const : Measurable (fun _ : H×A => (1:ℝ))).sumElim hi).comp
    (MeasurableEquiv.prodSumDistrib H A (B⊕Unit)).measurable
  have hm : Measurable (fun z : H×CavityGeneratedOriginSelection (W.tree c) =>
      if futureSourceValid W c z.1 z.2 then (1:ℝ) else 0) := by
    convert ho using 1
    funext z
    rcases z with ⟨h,g⟩
    rcases g with i | (i | u)
    all_goals simp only [futureSourceValid,ite_true]
    all_goals first | rfl | simp [Function.comp_def, MeasurableEquiv.prodSumDistrib,
      MeasurableEquiv.trans, MeasurableEquiv.sumCongr, MeasurableEquiv.prodComm,
      MeasurableEquiv.sumProdDistrib]
  have hset : {z : H×CavityGeneratedOriginSelection (W.tree c) |
      futureSourceValid W c z.1 z.2} =
      {z | (if futureSourceValid W c z.1 z.2 then (1:ℝ) else 0)=1} := by
    ext z
    by_cases hz : futureSourceValid W c z.1 z.2 <;> simp [hz]
  rw [hset]
  exact measurableSet_eq_fun hm measurable_const

private theorem futureSourceValid_kernel_ae
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m) :
    ∀ᵐg ∂cavityGeneratedOriginSelectionKernel μ a W c h,futureSourceValid W c h g := by
  have hp : MeasurableSet {g | futureSourceValid W c h g} :=
    (futureSourceValid_measurableSet W c).preimage (measurable_const.prodMk measurable_id)
  change ∀ᵐg ∂cavityGeneratedOriginSelectionMeasure μ a
    (W.clockTemplate.clock h c) (W.tree c) a,futureSourceValid W c h g
  rw [cavityGeneratedOriginSelectionMeasure]
  simp only [ae_add_measure_iff,ae_finsetSum_measure_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i _
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff hp).mpr trivial
  · intro i _
    apply (ae_map_iff (measurable_cavityGeneratedOriginSelectionEdge (W.tree c) i).aemeasurable hp).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change r∈Ioc _ _
    exact hr
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hp).mpr trivial

private theorem futureSourceSupport_ae
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet) :
    ∀ᵐz ∂((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
      Kernel.const _ (parisiFreeMeasure μ a)),
      z.1.1∈W.clockTemplate.orderSet ∧ futureSourceValid W c z.1.1 z.1.2 := by
  have hp : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) |
      z.1∈W.clockTemplate.orderSet ∧ futureSourceValid W c z.1 z.2} :=
    (W.clockTemplate.isClosed_orderSet.measurableSet.preimage measurable_fst).inter
      (futureSourceValid_measurableSet W c)
  have hbase : ∀ᵐz ∂M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c,
      z.1∈W.clockTemplate.orderSet ∧ futureSourceValid W c z.1 z.2 := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [horder] with h hh
    exact (futureSourceValid_kernel_ae μ a W c h).mono (fun g hg=>⟨hh,hg⟩)
  exact Measure.ae_compProd_of_ae_fst _ hp hbase

private theorem futureSourceOwnCell
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) (g : CavityGeneratedOriginSelection (W.tree c))
    (hg : futureSourceValid W c h g) :
    printedGeneratedOriginChartCell (W.component c)
      (printedGeneratedFuturePayloadChart (W.component c) g) h
      (printedGeneratedFuturePayloadFreeClock (W.component c) g) := by
  rcases g with i | (i | u)
  · trivial
  · have hc := printedGeneratedComponentClock_eq_native (W.component c) h
    change _ ≤ i.2 ∧ i.2 ≤ _
    rw [←hc]
    exact ⟨hg.1.le,hg.2⟩
  · trivial

private theorem futureSourceCellPayload_eq
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) (g : CavityGeneratedOriginSelection (W.tree c))
    (hg : futureSourceValid W c h g) (j : ℕ) (l : Paper.Overlap)
    (F : CavityGeneratedComponentTerminal n (W.component c) → ℝ) :
    cavityGeneratedSelectedFutureCellPayload D μ a (W.clockTemplate.clock h c) (W.tree c) F j (g,l) =
      if l∈Ioc (W.clockTemplate.clock h c (j+1)) (W.clockTemplate.clock h c j) ∧
          cavityGeneratedOriginSelectionClock W c (h,g)<l then
        nativeStreamingPatternMoment D μ a (W.clockTemplate.clock h c) (W.tree c) F
          (.future (cavityGeneratedOriginSelectionOrigin (W.tree c) g) j l) else 0 := by
  rcases g with i | (i | u)
  · rfl
  · change i.2∈Ioc
      (W.clockTemplate.clock h c (((cavityGeneratedOriginEdges (W.tree c)).get i.1).depth+1))
      (W.clockTemplate.clock h c ((cavityGeneratedOriginEdges (W.tree c)).get i.1).depth) at hg
    simp only [cavityGeneratedSelectedFutureCellPayload,cavityGeneratedSelectedOriginPayload,
      cavityGeneratedOriginCellMask,cavityGeneratedOriginSelectionOrigin,if_pos hg]
    rfl
  · rfl

def cavityGeneratedFutureOriginCellSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap) : ℝ :=
  ∫σ,cavityGeneratedSelectedFutureCellPayload D μ a (W.clockTemplate.clock z.1.1 c) (W.tree c)
    (fun τ=>F (z.1.1,Function.update σ c τ)) j (z.1.2,z.2)
    ∂cavityGeneratedForestTerminalKernel D μ a W z.1.1

private theorem futureSourceValue_partition
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap)
    (hh : z.1.1∈W.clockTemplate.orderSet) (hg : futureSourceValid W c z.1.1 z.1.2) :
    cavityGeneratedFutureOriginCellSourceValue D μ a W c F j z =
      ∑γ : PrintedGeneratedOriginChart (W.component c),
        (cavityGeneratedFutureOriginChartSourceEvent W c γ j).indicator
          (fun z=>cavityGeneratedFutureOriginExpectation D μ a W c γ j F
            (cavityGeneratedFutureOriginChartAppend W c z)) z := by
  classical
  let γ := printedGeneratedFuturePayloadChart (W.component c) z.1.2
  let ht := z.2∈Ioc (W.clockTemplate.clock z.1.1 c (j.val+1))
    (W.clockTemplate.clock z.1.1 c j) ∧ cavityGeneratedOriginSelectionClock W c z.1<z.2
  have hc : W.clockTemplate.clock z.1.1 c =
      nativeStreamingGeneratedComponentClock (W.component c) z.1.1 :=
    printedGeneratedComponentClock_eq_native (W.component c) z.1.1
  have hevent (δ : PrintedGeneratedOriginChart (W.component c)) :
      z∈cavityGeneratedFutureOriginChartSourceEvent W c δ j ↔ γ=δ ∧ ht := by
    change (_=δ ∧ _ ∧ _ ∧ (_≤_ ∧ _≤_) ∧ _) ∧ _ ↔ _
    constructor
    · intro hz
      exact ⟨hz.1.1,⟨by rw [hc]; exact ⟨hz.2,hz.1.2.2.2.1.2⟩,hz.1.2.2.2.2⟩⟩
    · rintro ⟨hδ,hfuture⟩
      have hcell := futureSourceOwnCell W c z.1.1 z.1.2 hg
      rw [show printedGeneratedFuturePayloadChart (W.component c) z.1.2=δ from hδ] at hcell
      have hl : z.2∈Ioc (nativeStreamingGeneratedComponentClock (W.component c) z.1.1 (j.val+1))
          (nativeStreamingGeneratedComponentClock (W.component c) z.1.1 j) := by
        rw [←hc]; exact hfuture.1
      exact ⟨⟨hδ,hh,hcell,⟨hl.1.le,hl.2⟩,hfuture.2⟩,hl.1⟩
  have hcellvalue : cavityGeneratedFutureOriginCellSourceValue D μ a W c F j z =
      if ht then (∫σ,nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1.1 c) (W.tree c)
        (fun τ=>F (z.1.1,Function.update σ c τ))
        (.future (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2) j z.2)
        ∂cavityGeneratedForestTerminalKernel D μ a W z.1.1) else 0 := by
    unfold cavityGeneratedFutureOriginCellSourceValue
    simp_rw [futureSourceCellPayload_eq D μ a W c z.1.1 z.1.2 hg]
    change (∫σ,if ht then _ else (0:ℝ)
      ∂cavityGeneratedForestTerminalKernel D μ a W z.1.1) = if ht then _ else 0
    by_cases hht : ht <;> simp only [hht,ite_true,ite_false,integral_zero]
  by_cases hht : ht
  · have hz : z∈cavityGeneratedFutureOriginChartSourceEvent W c γ j := (hevent γ).mpr ⟨rfl,hht⟩
    rw [hcellvalue,if_pos hht]
    rw [Finset.sum_eq_single γ]
    · rw [Set.indicator_of_mem hz]
      exact cavityGeneratedFutureOrigin_source_event_receiver D μ a W c γ j F z hz
    · intro δ _ hδ
      exact Set.indicator_of_notMem (by simpa only [hevent, hht,and_true] using Ne.symm hδ) _
    · simp
  · rw [hcellvalue,if_neg hht]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro δ _
    exact Set.indicator_of_notMem (by simp only [hevent,hht,and_false,not_false_eq_true]) _

private theorem futureExpectation_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    |cavityGeneratedFutureOriginExpectation D μ a W c γ j F H|≤2*C := by
  have hb (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedFutureOriginChartForest W c γ j).depth
      (cavityGeneratedFutureOriginChartForest W c γ j).tree) :
      |cavityGeneratedFutureOriginTest W c γ j F H σ|≤2*C := by
    unfold cavityGeneratedFutureOriginTest
    rw [abs_mul]
    exact (mul_le_mul (hbound _) (cavitySpinOverlapDefect_abs_le_two n _
      (H (Fin.last (m+1))).property _ _) (abs_nonneg _) hC).trans_eq (mul_comm C 2)
  simpa only [cavityGeneratedFutureOriginExpectation,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (f:=cavityGeneratedFutureOriginTest W c γ j F H)
      (C:=2*C) (μ:=cavityGeneratedForestTerminalKernel D μ a
      (cavityGeneratedFutureOriginChartForest W c γ j) H)
      (.of_forall fun σ=>by simpa only [Real.norm_eq_abs] using hb σ)

theorem cavityGeneratedFutureOrigin_source_cell_partition
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C)
    (j : Fin (W.depth c)) :
    Integrable (cavityGeneratedFutureOriginCellSourceValue D μ a W c F j)
      ((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ Kernel.const _ (parisiFreeMeasure μ a)) ∧
    (∑γ : PrintedGeneratedOriginChart (W.component c),
      ∫H,cavityGeneratedFutureOriginExpectation D μ a W c γ j F H
        ∂cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j) =
      ∫z,cavityGeneratedFutureOriginCellSourceValue D μ a W c F j z
        ∂((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ Kernel.const _ (parisiFreeMeasure μ a)) := by
  classical
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  let P := (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ Kernel.const _ (parisiFreeMeasure μ a)
  let I := fun (γ : PrintedGeneratedOriginChart (W.component c)) =>
    (cavityGeneratedFutureOriginChartSourceEvent W c γ j).indicator
      (fun z=>cavityGeneratedFutureOriginExpectation D μ a W c γ j F
        (cavityGeneratedFutureOriginChartAppend W c z))
  have hm (γ : PrintedGeneratedOriginChart (W.component c)) : Measurable (I γ) :=
    ((measurable_cavityGeneratedFutureOriginExpectation D μ a W c γ j F hF).comp
      (measurable_cavityGeneratedFutureOriginChartAppend W c)).indicator
        (measurableSet_cavityGeneratedFutureOriginChartSourceEvent W c γ j)
  have hi (γ : PrintedGeneratedOriginChart (W.component c)) : Integrable (I γ) P := by
    refine (integrable_const (2*C)).mono' (hm γ).aestronglyMeasurable (.of_forall fun z=>?_)
    by_cases hz : z∈cavityGeneratedFutureOriginChartSourceEvent W c γ j
    · rw [show I γ z = cavityGeneratedFutureOriginExpectation D μ a W c γ j F
        (cavityGeneratedFutureOriginChartAppend W c z) from Set.indicator_of_mem hz _]
      simpa only [Real.norm_eq_abs] using futureExpectation_abs_le D μ a W c γ j F C hC hbound _
    · rw [show I γ z=0 from Set.indicator_of_notMem hz _,norm_zero]
      positivity
  have he : cavityGeneratedFutureOriginCellSourceValue D μ a W c F j =ᵐ[P] fun z=>∑γ,I γ z :=
    (futureSourceSupport_ae μ a W c M horder).mono
      (fun z hz=>futureSourceValue_partition D μ a W c F j z hz.1 hz.2)
  have hsum : Integrable (fun z=>∑γ,I γ z) P := integrable_finset_sum Finset.univ (fun γ _=>hi γ)
  refine ⟨hsum.congr he.symm,?_⟩
  calc
    _ = ∑γ,∫z,I γ z ∂P := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [cavityGeneratedFutureOriginChartSourceMeasure,integral_map
        (measurable_cavityGeneratedFutureOriginChartAppend W c).aemeasurable
        (measurable_cavityGeneratedFutureOriginExpectation D μ a W c γ j F hF).aestronglyMeasurable]
      exact (integral_indicator (measurableSet_cavityGeneratedFutureOriginChartSourceEvent W c γ j)).symm
    _ = ∫z,∑γ,I γ z ∂P := (integral_finset_sum _ (fun γ _=>hi γ)).symm
    _ = _ := integral_congr_ae he.symm

private theorem futureCellPayload_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀σ,|F σ|≤C) (j : ℕ) (z : CavityGeneratedOriginSelection T×Paper.Overlap) :
    |cavityGeneratedSelectedFutureCellPayload D μ a q T F j z|≤2*C := by
  have hb (o : NativeStreamingOrigin T) :
      |if z.2∈Ioc (q (j+1)) (q j) ∧ nativeStreamingOriginLevel q o<z.2 then
        nativeStreamingPatternMoment D μ a q T F (.future o j z.2) else 0|≤2*C := by
    split_ifs
    · exact abs_nativeStreamingPatternMoment_le D μ a q T F C hC hF _
    · simp only [abs_zero]; positivity
  unfold cavityGeneratedSelectedFutureCellPayload cavityGeneratedSelectedOriginPayload
  cases ho : cavityGeneratedOriginSelectionOrigin T z.1 with
  | vertex v => exact hb (.vertex v)
  | edge e r =>
      change |if r∈Ioc (q (e.depth+1)) (q e.depth) then _ else 0|≤2*C
      by_cases hcell : r∈Ioc (q (e.depth+1)) (q e.depth)
      · rw [if_pos hcell]
        exact hb (.edge e r)
      · rw [if_neg hcell,abs_zero]
        positivity

def cavityGeneratedFutureOriginSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap) : ℝ :=
  ∫σ,cavityGeneratedSelectedFuturePayload D μ a (W.clockTemplate.clock z.1.1 c) (W.tree c)
    (fun τ=>F (z.1.1,Function.update σ c τ)) (z.1.2,z.2)
    ∂cavityGeneratedForestTerminalKernel D μ a W z.1.1

theorem cavityGeneratedFutureOrigin_source_partition
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (cavityGeneratedFutureOriginSourceValue D μ a W c F)
      ((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ Kernel.const _ (parisiFreeMeasure μ a)) ∧
    (∑γ : PrintedGeneratedOriginChart (W.component c),∑j : Fin (W.depth c),
      ∫H,cavityGeneratedFutureOriginExpectation D μ a W c γ j F H
        ∂cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j) =
      ∫z,cavityGeneratedFutureOriginSourceValue D μ a W c F z
        ∂((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ Kernel.const _ (parisiFreeMeasure μ a)) := by
  classical
  have he (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × Paper.Overlap) :
      cavityGeneratedFutureOriginSourceValue D μ a W c F z =
        ∑j : Fin (W.depth c),cavityGeneratedFutureOriginCellSourceValue D μ a W c F j z := by
    have hi j : Integrable (fun σ=>cavityGeneratedSelectedFutureCellPayload D μ a
        (W.clockTemplate.clock z.1.1 c) (W.tree c)
        (fun τ=>F (z.1.1,Function.update σ c τ)) j (z.1.2,z.2))
        (cavityGeneratedForestTerminalKernel D μ a W z.1.1) :=
      (integrable_const (2*C)).mono' (measurable_of_finite _).aestronglyMeasurable
        (.of_forall fun σ=>by simpa only [Real.norm_eq_abs] using
          futureCellPayload_abs_le D μ a _ _ _ C hC (fun τ=>hbound _) j (z.1.2,z.2))
    unfold cavityGeneratedFutureOriginSourceValue cavityGeneratedSelectedFuturePayload
    rw [integral_finset_sum _ (fun j _=>hi j)]
    exact (Fin.sum_univ_eq_sum_range (fun j=>∫σ,cavityGeneratedSelectedFutureCellPayload D μ a
      (W.clockTemplate.clock z.1.1 c) (W.tree c)
      (fun τ=>F (z.1.1,Function.update σ c τ)) j (z.1.2,z.2)
      ∂cavityGeneratedForestTerminalKernel D μ a W z.1.1) (W.depth c)).symm
  have hp j := cavityGeneratedFutureOrigin_source_cell_partition D μ a ha hμ W c M horder F hF C hC hbound j
  have hi := integrable_finset_sum Finset.univ (fun j _=>(hp j).1)
  refine ⟨hi.congr (.of_forall fun z=>(he z).symm),?_⟩
  rw [Finset.sum_comm]
  simp_rw [(fun j=>(hp j).2)]
  rw [←integral_finset_sum _ (fun j _=>(hp j).1)]
  exact integral_congr_ae (.of_forall fun z=>(he z).symm)

end QuantitativeFollowup
