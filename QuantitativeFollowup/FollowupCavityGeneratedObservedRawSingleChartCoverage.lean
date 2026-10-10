module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedRawOriginCellSupport
public import FourPapersCommon.FiniteMeasureChartPartition

@[expose] public section

/-! True raw single/current charts partition one original selected law.
The common selected-clock map reconstructs its whole source measure;
all chart budgets are aggregated before applying the sharp origin bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

private theorem rawSingle_cell_of_valid (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) (g : CavityGeneratedOriginSelection U.tree)
    (hg : cavityGeneratedOriginCellValid (U.clock h) U.tree
      (cavityGeneratedOriginSelectionOrigin U.tree g)) :
    cavityGeneratedObservedRawChartCell U (cavityGeneratedObservedRawOriginPayloadChart U g) h
      (cavityGeneratedObservedRawOriginPayloadFreeClock U g) := by
  rcases g with i | (z | u)
  · trivial
  · exact ⟨le_of_lt hg.1,hg.2⟩
  · trivial

theorem cavityGeneratedObservedRawSingleOriginChartEvent_cover_ae
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    ∀ᵐz ∂M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c),
      ∃γ, z ∈ cavityGeneratedObservedRawSingleOriginChartEvent W c γ := by
  have hs := Measure.ae_compProd_of_ae_fst
    (cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c)) W.measurableSet_supportSet hsupport
  filter_upwards [hs,cavityGeneratedRawOriginSelectionJointMeasure_ae_cell_valid μ a
    (fun h => W.clock h c) (W.measurable_clock c) (W.tree c) M] with z hz hg
  exact ⟨cavityGeneratedObservedRawOriginPayloadChart (W.component c) z.2,
    rfl,hz,rawSingle_cell_of_valid (W.component c) z.1 z.2 hg⟩

theorem cavityGeneratedObservedRawSingleOriginPayloadMeasure_sum
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    (∑γ, (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c)).restrict
        (cavityGeneratedObservedRawSingleOriginChartEvent W c γ)) =
      M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c) :=
  finiteMeasureChartPartition_sum_restrict _
    (cavityGeneratedObservedRawSingleOriginChartEvent W c)
    (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c)
    (cavityGeneratedObservedRawSingleOriginChartEvent_disjoint W c)
    (cavityGeneratedObservedRawSingleOriginChartEvent_cover_ae μ a W c M hsupport)

theorem cavityGeneratedObservedRawSingleOriginChartMeasure_sum
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    (∑γ, cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ) =
      (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c)).map
        (cavityGeneratedRawOriginAppendedHistory (fun h => W.clock h c) (W.tree c)) := by
  classical
  exact finiteMeasureChartPartition_sum_map_restrict _
    (cavityGeneratedObservedRawSingleOriginChartEvent W c)
    (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c)
    (cavityGeneratedObservedRawSingleOriginChartEvent_disjoint W c)
    (cavityGeneratedObservedRawSingleOriginChartEvent_cover_ae μ a W c M hsupport)
    (cavityGeneratedRawOriginAppendedHistory (fun h => W.clock h c) (W.tree c))
    (measurable_cavityGeneratedRawOriginAppendedHistory (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c))

theorem cavityGeneratedObservedRawSingleOriginChartMeasure_sum_withDensity
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet)
    (w : CavityGeneratedHistory Paper.Overlap (m+1) → ℝ≥0∞) :
    (∑γ, (cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ).withDensity w) =
      ((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c)).map
          (cavityGeneratedRawOriginAppendedHistory (fun h => W.clock h c) (W.tree c))).withDensity w := by
  classical
  rw [←cavityGeneratedObservedRawSingleOriginChartMeasure_sum μ a W c M hsupport]
  simpa only [Measure.sum_fintype] using
    (withDensity_sum (fun γ => cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ) w).symm

theorem cavityGeneratedObservedRawSingleOriginChartMeasure_sum_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (∑γ, cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))*C) := by
  rw [cavityGeneratedObservedRawSingleOriginChartMeasure_sum μ a W c M hsupport]
  exact cavityGeneratedRawOriginSelectionKernel_appended_history_budget μ a ha hμ
    (fun h => W.clock h c) (W.measurable_clock c) (W.tree c) (W.component c).forkMark M C hM
    (hsupport.mono fun h hh => ⟨W.clock_antitone h c,W.clock_terminal h c,
      W.clock_initial h c,(W.component c).fork_clock_is_mark h (hh c)⟩)

theorem cavityGeneratedObservedRawCurrentChartMeasure_sum_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (∑γ, cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))*C) := by
  apply cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _
    (cavityGeneratedObservedRawSingleOriginChartMeasure_sum_budget μ a ha hμ W c M C hM hsupport)
  apply Measure.le_iff.mpr
  intro S hS
  simp only [Measure.coe_finsetSum,Finset.sum_apply]
  exact Finset.sum_le_sum fun γ _ => cavityGeneratedObservedRawCurrentChartMeasure_le μ a W c M γ S

end QuantitativeFollowup
