module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionMeasure
public import QuantitativeFollowup.FollowupCavityGeneratedOriginClockKernel
public import QuantitativeFollowup.FollowupCavityGeneratedAppendMarkPayloadBudget
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

@[expose] public section

/-! The genuine origin-selection kernel keeps the attachment payload.
Its clock pushforward is the actual origin clock kernel, so inherited
fork and edge choices share one depth-independent mark budget. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
variable {m : ℕ}

def cavityGeneratedOriginSelectionClock
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :
    Paper.Overlap :=
  nativeStreamingOriginLevel (W.clockTemplate.clock z.1 c)
    (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)

theorem measurable_cavityGeneratedOriginSelectionClock
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    Measurable (cavityGeneratedOriginSelectionClock W c) := by
  let H := CavityGeneratedHistory Paper.Overlap m
  let A := Fin (cavityGeneratedOriginForkVertices (W.tree c)).length
  let B := Fin (cavityGeneratedOriginEdges (W.tree c)).length × Paper.Overlap
  have hf : Measurable (fun z : H × A =>
      W.clockTemplate.clock z.1 c ((cavityGeneratedOriginForkVertices (W.tree c)).get z.2).depth) :=
    measurable_from_prod_countable_left (fun i => by
      change Measurable (fun h : H =>
        W.clockTemplate.clock h c ((cavityGeneratedOriginForkVertices (W.tree c)).get i).depth)
      exact (W.clockTemplate.clock_continuous c _).measurable)
  have he : Measurable (fun z : H × B => z.2.2) := measurable_snd.comp measurable_snd
  have hr : Measurable (fun z : H × Unit => W.clockTemplate.clock z.1 c (W.depth c)) :=
    (W.clockTemplate.clock_continuous c _).measurable.comp measurable_fst
  have hinner := (he.sumElim hr).comp (MeasurableEquiv.prodSumDistrib H B Unit).measurable
  have houter := (hf.sumElim hinner).comp
    (MeasurableEquiv.prodSumDistrib H A (B ⊕ Unit)).measurable
  convert houter using 1
  funext z
  rcases z with ⟨h,g⟩
  cases g with
  | inl i => rfl
  | inr g => cases g <;> rfl

theorem measurable_cavityGeneratedOriginSelectionMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) :
    Measurable (fun h : CavityGeneratedHistory Paper.Overlap m =>
      cavityGeneratedOriginSelectionMeasure μ a (W.clockTemplate.clock h c) (W.tree c) a) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have hc (d : ℕ) : Measurable (fun h : CavityGeneratedHistory Paper.Overlap m =>
      Paper.parisiCDF μ (W.clockTemplate.clock h c d)) :=
    (Paper.parisiCDF_measurable μ).comp
      (measurable_subtype_coe.comp (W.clockTemplate.clock_continuous c d).measurable)
  have hf (i : Fin (cavityGeneratedOriginForkVertices (W.tree c)).length) :
      Measurable (fun h : CavityGeneratedHistory Paper.Overlap m =>
        ENNReal.ofReal (Paper.parisiCDF μ
          (W.clockTemplate.clock h c ((cavityGeneratedOriginForkVertices (W.tree c)).get i).depth))*
            Measure.dirac (Sum.inl i : CavityGeneratedOriginSelection (W.tree c)) S) :=
    (hc _).ennreal_ofReal.mul measurable_const
  have he (i : Fin (cavityGeneratedOriginEdges (W.tree c)).length) :
      Measurable (fun h : CavityGeneratedHistory Paper.Overlap m =>
        (((parisiFreeMeasure μ a).restrict
          (Ioc (W.clockTemplate.clock h c (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1))
            (W.clockTemplate.clock h c ((cavityGeneratedOriginEdges (W.tree c)).get i).depth))).map
              (cavityGeneratedOriginSelectionEdge (W.tree c) i)) S) := by
    let E := cavityGeneratedOriginSelectionEdge (W.tree c) i ⁻¹' S
    have hE : MeasurableSet E := (measurable_cavityGeneratedOriginSelectionEdge _ i) hS
    let f : Paper.Overlap → ℝ := E.indicator (fun _ => 1)
    have hfi : Measurable f := measurable_const.indicator hE
    have hm := measurable_cavityGeneratedMovingCellIntegral (parisiFreeMeasure μ a)
      (fun h => W.clockTemplate.clock h c (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1))
      (fun h => W.clockTemplate.clock h c ((cavityGeneratedOriginEdges (W.tree c)).get i).depth)
      (W.clockTemplate.clock_continuous c _).measurable
      (W.clockTemplate.clock_continuous c _).measurable f hfi
    have hh (h : CavityGeneratedHistory Paper.Overlap m) :
        ENNReal.ofReal (∫r in
          Ioc (W.clockTemplate.clock h c (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1))
            (W.clockTemplate.clock h c ((cavityGeneratedOriginEdges (W.tree c)).get i).depth),
          f r ∂parisiFreeMeasure μ a) =
        (((parisiFreeMeasure μ a).restrict
          (Ioc (W.clockTemplate.clock h c (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1))
            (W.clockTemplate.clock h c ((cavityGeneratedOriginEdges (W.tree c)).get i).depth))).map
              (cavityGeneratedOriginSelectionEdge (W.tree c) i)) S := by
      rw [Measure.map_apply (measurable_cavityGeneratedOriginSelectionEdge _ i) hS]
      change ENNReal.ofReal (∫r,f r ∂(parisiFreeMeasure μ a).restrict
        (Ioc (W.clockTemplate.clock h c (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1))
          (W.clockTemplate.clock h c ((cavityGeneratedOriginEdges (W.tree c)).get i).depth))) =
        ((parisiFreeMeasure μ a).restrict
          (Ioc (W.clockTemplate.clock h c (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1))
            (W.clockTemplate.clock h c ((cavityGeneratedOriginEdges (W.tree c)).get i).depth))) E
      rw [show f = E.indicator (1 : Paper.Overlap → ℝ) from rfl,
        integral_indicator_one hE, ofReal_measureReal]
    exact (funext hh) ▸ hm.ennreal_ofReal
  have hr : Measurable (fun h : CavityGeneratedHistory Paper.Overlap m =>
      ENNReal.ofReal (Paper.parisiCDF μ (W.clockTemplate.clock h c (W.depth c))-a)*
        Measure.dirac (Sum.inr (Sum.inr ()) : CavityGeneratedOriginSelection (W.tree c)) S) :=
    ((hc _).sub measurable_const).ennreal_ofReal.mul measurable_const
  have hm := ((Finset.measurable_fun_sum Finset.univ (fun i _ => hf i)).add
    (Finset.measurable_fun_sum Finset.univ (fun i _ => he i))).add hr
  convert hm using 1
  funext h
  simp only [Pi.add_apply,cavityGeneratedOriginSelectionMeasure, Measure.add_apply,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

def cavityGeneratedOriginSelectionKernel
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) :
    Kernel (CavityGeneratedHistory Paper.Overlap m) (CavityGeneratedOriginSelection (W.tree c)) where
  toFun h := cavityGeneratedOriginSelectionMeasure μ a (W.clockTemplate.clock h c) (W.tree c) a
  measurable' := measurable_cavityGeneratedOriginSelectionMeasure μ a W c

theorem cavityGeneratedOriginSelectionKernel_clock_map
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ ∈ scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    (cavityGeneratedOriginSelectionKernel μ a W c h).map
      (fun g => cavityGeneratedOriginSelectionClock W c (h,g)) =
      cavityGeneratedOriginClockKernel μ a hμ W c h := by
  let q := W.clockTemplate.clock h c
  let M := cavityGeneratedOriginSelectionKernel μ a W c h
  let η := cavityGeneratedOriginClockKernel μ a hμ W c h
  let τ := fun g => cavityGeneratedOriginSelectionClock W c (h,g)
  have hm : Measurable τ := (measurable_cavityGeneratedOriginSelectionClock W c).comp
    (measurable_const.prodMk measurable_id)
  haveI : IsFiniteMeasure M := cavityGeneratedOriginSelectionMeasure_finite μ a q (W.tree c) a
  haveI : IsFiniteMeasure η := printedGeneratedOriginClockMeasure_finite μ a q (W.tree c) a
  have hs : a ≤ Paper.parisiCDF μ (q (W.depth c)) := by
    let c' : Fin W.clockTemplate.componentCount := c
    change a ≤ Paper.parisiCDF μ (W.clockTemplate.clock h c' (W.clockTemplate.depth c'))
    rw [W.clockTemplate.clock_initial h c']
    exact scalarFloor_cdf_lower hμ (by norm_num)
  apply Measure.ext
  intro S hS
  let f : Paper.Overlap → ℝ := S.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hS
  have hb : ∀r, |f r| ≤ 1 := by
    classical
    intro r
    by_cases hr : r ∈ S <;> simp [f,hr]
  have he := integral_cavityGeneratedOriginSelectionMeasure μ a q
    (W.clockTemplate.clock_terminal h c) (W.tree c) a hs
    (fun o => f (nativeStreamingOriginLevel q o)) (hf.comp hm)
    1 (fun o => hb _)
  have hp := printedGeneratedOriginClockMeasure_integral μ a q (W.tree c) a hs f hf 1 hb
  have hh : (M.map τ).real S = η.real S := by
    calc
      _ = ∫r,f r ∂M.map τ := (integral_indicator_one hS).symm
      _ = ∫g,f (τ g) ∂M := integral_map hm.aemeasurable hf.aestronglyMeasurable
      _ = _ := he
      _ = ∫r,f r ∂η := hp.symm
      _ = _ := integral_indicator_one hS
  have hh' := congrArg ENNReal.ofReal hh
  rw [ofReal_measureReal, ofReal_measureReal] at hh'
  exact hh'

theorem cavityGeneratedOriginSelectionKernel_mass_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedOriginSelectionKernel μ a W c h univ ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) := by
  have hm : Measurable (fun g => cavityGeneratedOriginSelectionClock W c (h,g)) :=
    (measurable_cavityGeneratedOriginSelectionClock W c).comp
      (measurable_const.prodMk measurable_id)
  have he := cavityGeneratedOriginSelectionKernel_clock_map μ a hμ W c h
  have hh := congrArg (fun M : Measure Paper.Overlap => M univ) he
  rw [Measure.map_apply hm MeasurableSet.univ,preimage_univ] at hh
  exact hh.le.trans (cavityGeneratedOriginClockKernel_mass_le μ a ha hμ W c h)

theorem cavityGeneratedOriginSelectionKernel_finite
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) :
    IsFiniteKernel (cavityGeneratedOriginSelectionKernel μ a W c) where
  exists_univ_le := ⟨_, ENNReal.natCast_lt_top _,
    cavityGeneratedOriginSelectionKernel_mass_le μ a ha hμ W c⟩

theorem cavityGeneratedOriginSelectionKernel_clock_domination
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ W.clockTemplate.orderSet) :
    (cavityGeneratedOriginSelectionKernel μ a W c h).map
      (fun g => cavityGeneratedOriginSelectionClock W c (h,g)) ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) •
        parisiFreeMeasure μ a +
          ∑i : Fin (cavityGeneratedOriginForkMarks W c).length,
            Measure.dirac (h ((cavityGeneratedOriginForkMarks W c).get i)) := by
  rw [cavityGeneratedOriginSelectionKernel_clock_map μ a hμ W c h]
  exact cavityGeneratedOriginClockKernel_le_history_marks μ a ha hμ W c h hh

theorem cavityGeneratedOriginSelectionKernel_payload_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M
      cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c)
      (cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks
        (cavityGeneratedOriginSelectionClock W c))
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))*C) := by
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  exact cavityGeneratedMarkBudget_payload_compProd (parisiFreeMeasure μ a) M
    (cavityGeneratedOriginSelectionKernel μ a W c) (cavityGeneratedOriginSelectionClock W c)
    (measurable_cavityGeneratedOriginSelectionClock W c)
    cavityGeneratedHistoryMarks cavityGeneratedHistoryMarks_measurable
    (fun i => (cavityGeneratedOriginForkMarks W c).get i) _ C hM
    (.of_forall (cavityGeneratedOriginSelectionKernel_mass_le μ a ha hμ W c))
    (horder.mono (fun h hh =>
      cavityGeneratedOriginSelectionKernel_clock_domination μ a ha hμ W c h hh))

theorem cavityGeneratedOriginSelectionKernel_appended_history_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M
      cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      ((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).map
        (fun z => Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z)))
      cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))*C) := by
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  exact cavityGeneratedMarkBudget_kernel_payload_append (parisiFreeMeasure μ a) M
    (cavityGeneratedOriginSelectionKernel μ a W c) (cavityGeneratedOriginSelectionClock W c)
    (measurable_cavityGeneratedOriginSelectionClock W c)
    (fun i => (cavityGeneratedOriginForkMarks W c).get i) _ C hM
    (.of_forall (cavityGeneratedOriginSelectionKernel_mass_le μ a ha hμ W c))
    (horder.mono (fun h hh =>
      cavityGeneratedOriginSelectionKernel_clock_domination μ a ha hμ W c h hh))

theorem cavityGeneratedOriginSelectionKernel_program_history_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      ((((P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a)) ⊗ₘ
          cavityGeneratedOriginSelectionKernel μ a W c).map
        (fun z => Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z)))
      cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))*(P.budget : ℝ≥0∞)) := by
  let Q := P.restrict W.clockTemplate.orderSet
  haveI := Q.isFiniteMeasure_measure (parisiFreeMeasure μ a)
    (cavityGenerated_free_mass_le_one μ a ha.1)
  have hb := Q.actual_mark_budget (parisiFreeMeasure μ a)
    (cavityGenerated_free_mass_le_one μ a ha.1)
  have horder : ∀ᵐh ∂Q.measure (parisiFreeMeasure μ a), h ∈ W.clockTemplate.orderSet :=
    ae_restrict_mem W.clockTemplate.isClosed_orderSet.measurableSet
  simpa only [Q,CavityGeneratedMarkProgram.budget] using
    cavityGeneratedOriginSelectionKernel_appended_history_budget μ a ha hμ W c
      (Q.measure (parisiFreeMeasure μ a)) (Q.budget : ℝ≥0∞) hb horder

end QuantitativeFollowup
