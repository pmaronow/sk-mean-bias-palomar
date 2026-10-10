module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawSelectionBudget

@[expose] public section

/-! Concrete raw cross and future restrictions inherit sharp budgets
before their exact physical-clock graph maps. These bounds use actual
source laws and do not spend a budget once per observation cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

theorem cavityGeneratedObservedRawOriginCrossSourceMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M] (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet)
    (E : Set ((CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      CavityGeneratedOriginSelection (W.tree c))) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedRawOriginCrossSourceMeasure μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c) M E) cavityGeneratedHistoryMarks
      ((((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))^2)*C) := by
  let τ := cavityGeneratedObservedRawOriginSelectionClock W c
  let ξ := cavityGeneratedRawOriginSecondSelectionClock (fun h => W.clock h c) (W.tree c)
  let marks := cavityGeneratedPayloadExtendedMarks
    (cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks τ) ξ
  have hm : ∀i, Measurable (marks i) :=
    cavityGeneratedPayloadExtendedMarks_measurable _
      (cavityGeneratedPayloadExtendedMarks_measurable cavityGeneratedHistoryMarks
        cavityGeneratedHistoryMarks_measurable τ
        (measurable_cavityGeneratedObservedRawOriginSelectionClock W c)) ξ
      (measurable_cavityGeneratedRawOriginSecondSelectionClock (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c))
  have hb := cavityGeneratedObservedRawOriginDoubleSelection_payload_budget μ a ha hμ W c M C hM hsupport
  have hr := cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) marks hm _ hb
    (Measure.restrict_le_self (μ := cavityGeneratedRawOriginDoubleSelectionMeasure μ a
      (fun h => W.clock h c) (W.measurable_clock c) (W.tree c) M) (s := E))
  unfold cavityGeneratedRawOriginCrossSourceMeasure
  apply cavityGeneratedMarkBudget_map (parisiFreeMeasure μ a) _ marks cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _ hr _
    (measurable_cavityGeneratedRawOriginDoubleAppendedHistory (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c))
  intro i
  funext z
  cases i using Fin.lastCases with
  | last => simp only [Function.comp_apply,cavityGeneratedHistoryMarks,
      cavityGeneratedRawOriginDoubleAppendedHistory,marks,cavityGeneratedPayloadExtendedMarks,
      Fin.snoc_last,ξ]
  | cast i =>
      cases i using Fin.lastCases <;>
        simp only [Function.comp_apply,cavityGeneratedHistoryMarks,
          cavityGeneratedRawOriginDoubleAppendedHistory,cavityGeneratedRawOriginAppendedHistory,
          marks,cavityGeneratedPayloadExtendedMarks,Fin.snoc_last,Fin.snoc_castSucc,
          τ,cavityGeneratedObservedRawOriginSelectionClock]

theorem cavityGeneratedObservedRawOriginFutureSourceMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M] (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet)
    (E : Set ((CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap)) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedRawOriginFutureSourceMeasure μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c) M E) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))*C) := by
  let τ := cavityGeneratedObservedRawOriginSelectionClock W c
  let marks := cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks τ
  have hb := cavityGeneratedObservedRawOriginSelectionKernel_payload_budget μ a ha hμ W c M C hM hsupport
  have hf := cavityGeneratedMarkBudget_fresh (parisiFreeMeasure μ a)
    (cavityGenerated_free_mass_le_one μ a ha.1)
    (M ⊗ₘ cavityGeneratedObservedRawOriginSelectionKernel μ a W c) marks
    (cavityGeneratedPayloadExtendedMarks_measurable cavityGeneratedHistoryMarks
      cavityGeneratedHistoryMarks_measurable τ
      (measurable_cavityGeneratedObservedRawOriginSelectionClock W c)) _ hb E
  unfold cavityGeneratedRawOriginFutureSourceMeasure
  apply cavityGeneratedMarkBudget_map (parisiFreeMeasure μ a) _
    (cavityGeneratedExtendedMarks marks) cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _ hf _
    (measurable_cavityGeneratedRawOriginFutureAppendedHistory (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c))
  intro i
  funext z
  cases i using Fin.lastCases with
  | last => simp only [Function.comp_apply,cavityGeneratedHistoryMarks,
      cavityGeneratedRawOriginFutureAppendedHistory,cavityGeneratedExtendedMarks,Fin.snoc_last]
  | cast i =>
      cases i using Fin.lastCases <;>
        simp only [Function.comp_apply,cavityGeneratedHistoryMarks,
          cavityGeneratedRawOriginFutureAppendedHistory,cavityGeneratedRawOriginAppendedHistory,
          marks,cavityGeneratedExtendedMarks,cavityGeneratedPayloadExtendedMarks,
          Fin.snoc_last,Fin.snoc_castSucc,τ,cavityGeneratedObservedRawOriginSelectionClock]

theorem cavityGeneratedObservedRawCurrentWeight_budget
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (M : Measure (CavityGeneratedHistory Paper.Overlap (m+1))) (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (M.withDensity (fun h => ENNReal.ofReal (Paper.parisiCDF μ (h (Fin.last m)))))
      cavityGeneratedHistoryMarks C := by
  have hb := cavityGeneratedMarkBudget_weight (parisiFreeMeasure μ a) M
    cavityGeneratedHistoryMarks cavityGeneratedHistoryMarks_measurable C 1 hM
    (fun h => ENNReal.ofReal (Paper.parisiCDF μ (h (Fin.last m))))
    (fun h => by simpa using ENNReal.ofReal_le_ofReal (Paper.parisiCDF_le_one μ _))
  simpa only [one_mul] using hb

end QuantitativeFollowup
