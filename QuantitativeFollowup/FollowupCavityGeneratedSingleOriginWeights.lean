module
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginFamilies

@[expose] public section

/-! The literal absolute coefficient of original/fresh is two. The current
term carries the actual scalar CDF at its original selected clock. Both
weights act on the genuine single-origin chart measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {m : ℕ}

def cavityGeneratedOriginalFreshChartMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) :=
  (2 : ℝ≥0∞) • cavityGeneratedSingleOriginChartMeasure μ a W c M γ

def cavityGeneratedCurrentChartMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) :=
  (cavityGeneratedSingleOriginChartMeasure μ a W c M γ).withDensity
    (fun h => ENNReal.ofReal (Paper.parisiCDF μ (h (Fin.last m))))

theorem cavityGeneratedSingleOriginChartMeasure_budget_each
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (γ : PrintedGeneratedOriginChart (W.component c)) (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedSingleOriginChartMeasure μ a W c M γ) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))*C) := by
  classical
  exact cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _
    (cavityGeneratedSingleOriginChartMeasure_budget μ a ha hμ W c M C hM horder)
    (Finset.single_le_sum (f := fun δ => cavityGeneratedSingleOriginChartMeasure μ a W c M δ)
      (fun _ _ => bot_le) (Finset.mem_univ γ))

theorem cavityGeneratedOriginalFreshChartMeasure_order
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) :
    ∀ᵐh ∂cavityGeneratedOriginalFreshChartMeasure μ a W c M γ,
      h ∈ (cavityGeneratedSingleOriginChartForest W c γ .single).clockTemplate.orderSet :=
  Measure.ae_smul_measure (cavityGeneratedSingleOriginChartMeasure_order μ a W c M γ .single) 2

theorem cavityGeneratedCurrentChartMeasure_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) :
    cavityGeneratedCurrentChartMeasure μ a W c M γ ≤
      cavityGeneratedSingleOriginChartMeasure μ a W c M γ := by
  unfold cavityGeneratedCurrentChartMeasure
  simpa only [one_smul] using cavityGenerated_withDensity_le
    (cavityGeneratedSingleOriginChartMeasure μ a W c M γ)
    (fun h => ENNReal.ofReal (Paper.parisiCDF μ (h (Fin.last m)))) 1
    (fun h => (ENNReal.ofReal_le_ofReal (Paper.parisiCDF_le_one μ _)).trans_eq
      (by norm_num))

theorem cavityGeneratedCurrentChartMeasure_order
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c)) :
    ∀ᵐh ∂cavityGeneratedCurrentChartMeasure μ a W c M γ,
      h ∈ (cavityGeneratedSingleOriginChartForest W c γ .current).clockTemplate.orderSet :=
  (cavityGeneratedSingleOriginChartMeasure_order μ a W c M γ .current).filter_mono
    (ae_mono (cavityGeneratedCurrentChartMeasure_le μ a W c M γ))

theorem cavityGeneratedOriginalFreshChartMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (γ : PrintedGeneratedOriginChart (W.component c)) (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedOriginalFreshChartMeasure μ a W c M γ) cavityGeneratedHistoryMarks
      (2*((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))*C) := by
  have hb := cavityGeneratedSingleOriginChartMeasure_budget_each μ a ha hμ W c M γ C hM horder
  refine ⟨?_,fun i => ?_⟩
  · change ((2 : ℝ≥0∞) • cavityGeneratedSingleOriginChartMeasure μ a W c M γ) univ ≤ _
    rw [Measure.smul_apply,smul_eq_mul]
    simpa only [mul_assoc] using mul_le_mul_right hb.1 (2 : ℝ≥0∞)
  · change ((2 : ℝ≥0∞) • cavityGeneratedSingleOriginChartMeasure μ a W c M γ).map
      (cavityGeneratedHistoryMarks i) ≤ _
    rw [Measure.map_smul _ (cavityGeneratedHistoryMarks_measurable i).aemeasurable]
    apply Measure.le_iff.mpr
    intro E hE
    simpa only [Measure.smul_apply,smul_eq_mul,mul_assoc] using
      mul_le_mul_right (hb.2 i E) (2 : ℝ≥0∞)

theorem cavityGeneratedCurrentChartMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (γ : PrintedGeneratedOriginChart (W.component c)) (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedCurrentChartMeasure μ a W c M γ) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))*C) :=
  cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _
    (cavityGeneratedSingleOriginChartMeasure_budget_each μ a ha hμ W c M γ C hM horder)
    (cavityGeneratedCurrentChartMeasure_le μ a W c M γ)

end QuantitativeFollowup
