module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTermCounts
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTermSupport
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawIndexedSelectionBudget
public import QuantitativeFollowup.SupportingGeneratedStreamingTermCost

@[expose] public section

/-! The normalized absolute mark law of an actual observed path has a
count-only budget. Unary cuts do not enter the recurrence: origin mass
and domination use actual leaves and actual forks on the source support. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {C m : ℕ}

private theorem observedRawTermMarkBudget_next
    (ν : Measure Paper.Overlap) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (K0 r : ℕ) (k : ℝ≥0∞)
    (hk : k ≤ (printedGeneratedStreamingStepCost
      (printedGeneratedStreamingLeafBound K0 r) (printedGeneratedStreamingMarkBound r) : ℝ≥0∞))
    (hM : cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks
      (k*(printedGeneratedStreamingBudget K0 r : ℝ≥0∞))) :
    cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks
      (printedGeneratedStreamingBudget K0 (r+1) : ℝ≥0∞) := by
  rw [printedGeneratedStreamingBudget_succ_ennreal]
  exact cavityGeneratedMarkBudget_mono_constant ν M cavityGeneratedHistoryMarks _ _ hM
    (mul_le_mul_left hk (printedGeneratedStreamingBudget K0 r : ℝ≥0∞))

private theorem observedRawTerm_actual_costs
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M) (c : Fin W.componentCount) :
    let B : ℝ≥0∞ := printedGeneratedStreamingStepCost
      (printedGeneratedStreamingLeafBound (cavityGeneratedObservedRawStreamingInitialLeafCount S) r)
      (printedGeneratedStreamingMarkBound r)
    let A : ℝ≥0∞ := (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
      ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞)
    1 ≤ B ∧ 2*A ≤ B ∧ A^2 ≤ B ∧ A ≤ B := by
  let K := printedGeneratedStreamingLeafBound (cavityGeneratedObservedRawStreamingInitialLeafCount S) r
  let L := printedGeneratedStreamingMarkBound r
  have hc := cavityGeneratedActualObservedRawStreamingTerm_counts μ a S H
  have hpos : 0 < K := cavityGeneratedObservedRaw_component_bound_pos W c K hc.2.2
  have hA := cavityGeneratedObservedRaw_component_origin_cost_le_uniform_ennreal W c hc.1 K L hc.2.2 hc.2.1
  change (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞)+
    ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞)≤
      (printedGeneratedOriginAppendCost K L : ℝ≥0∞) at hA
  have hb := printedGeneratedStreamingTermCosts_le_ennreal K L hpos
  refine ⟨hb.1,?_,?_,hA.trans hb.2.2.2⟩
  · exact (mul_le_mul_of_nonneg_left hA (by positivity)).trans hb.2.1
  · exact (pow_le_pow_left₀ (by positivity) hA 2).trans hb.2.2.1

private theorem observedRawTerm_single_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (B : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks B)
    (hs : ∀ᵐh ∂M,h∈W.supportSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞)+
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))*B) :=
  cavityGeneratedObservedRawOriginSourceMeasure_budget μ a ha hμ W c M B hM hs _

private theorem observedRawTerm_originalFresh_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (B : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks B)
    (hs : ∀ᵐh ∂M,h∈W.supportSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ) cavityGeneratedHistoryMarks
      (2*((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞)+
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))*B) := by
  have hb := observedRawTerm_single_budget μ a ha hμ W c M γ B hM hs
  refine ⟨?_,fun i=>?_⟩
  · change ((2 : ℝ≥0∞) • cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ) univ≤_
    rw [Measure.smul_apply,smul_eq_mul]
    simpa only [mul_assoc] using mul_le_mul_right hb.1 (2 : ℝ≥0∞)
  · change ((2 : ℝ≥0∞) • cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ).map
      (cavityGeneratedHistoryMarks i)≤_
    rw [Measure.map_smul _ (cavityGeneratedHistoryMarks_measurable i).aemeasurable]
    apply Measure.le_iff.mpr
    intro E hE
    simpa only [Measure.smul_apply,smul_eq_mul,mul_assoc] using
      mul_le_mul_right (hb.2 i E) (2 : ℝ≥0∞)

theorem cavityGeneratedActualObservedRawStreamingTerm_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (S : CavityGeneratedObservedRawInitialForest C)
    {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks
      (printedGeneratedStreamingBudget (cavityGeneratedObservedRawStreamingInitialLeafCount S) r : ℝ≥0∞) := by
  induction H with
  | initial =>
      simpa only [printedGeneratedStreamingBudget_zero,Nat.cast_one] using
        printedGeneratedInitialFreeHistory_budget μ a ha.1
  | @original r m W M previous c b e ih =>
      have hc := observedRawTerm_actual_costs μ a S previous c
      apply observedRawTermMarkBudget_next (parisiFreeMeasure μ a) M
        (cavityGeneratedObservedRawStreamingInitialLeafCount S) r 1 hc.1
      simpa only [one_mul] using ih
  | @originalFresh r m W M previous c b γ ih =>
      haveI : IsFiniteMeasure M := ⟨ih.1.trans_lt (ENNReal.natCast_lt_top _)⟩
      have hc := observedRawTerm_actual_costs μ a S previous c
      have hb := observedRawTerm_originalFresh_budget μ a ha hμ W c M γ _ ih
        (cavityGeneratedActualObservedRawStreamingTerm_support μ a ha S previous)
      exact observedRawTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedObservedRawStreamingInitialLeafCount S) r _ hc.2.1 hb
  | @cross r m W M previous c γ δ χ ih =>
      haveI : IsFiniteMeasure M := ⟨ih.1.trans_lt (ENNReal.natCast_lt_top _)⟩
      have hc := observedRawTerm_actual_costs μ a S previous c
      have hb := cavityGeneratedObservedRawOriginCrossSourceMeasure_budget μ a ha hμ W c M _ ih
        (cavityGeneratedActualObservedRawStreamingTerm_support μ a ha S previous)
        (cavityGeneratedObservedRawCrossChartEvent W c γ δ χ)
      exact observedRawTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedObservedRawStreamingInitialLeafCount S) r _ hc.2.2.1 hb
  | @current r m W M previous c γ ih =>
      haveI : IsFiniteMeasure M := ⟨ih.1.trans_lt (ENNReal.natCast_lt_top _)⟩
      have hc := observedRawTerm_actual_costs μ a S previous c
      have hb := observedRawTerm_single_budget μ a ha hμ W c M γ _ ih
        (cavityGeneratedActualObservedRawStreamingTerm_support μ a ha S previous)
      have hw := cavityGeneratedObservedRawCurrentWeight_budget μ a _ _ hb
      exact observedRawTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedObservedRawStreamingInitialLeafCount S) r _ hc.2.2.2 hw
  | @future r m W M previous c γ j ih =>
      haveI : IsFiniteMeasure M := ⟨ih.1.trans_lt (ENNReal.natCast_lt_top _)⟩
      have hc := observedRawTerm_actual_costs μ a S previous c
      have hb := cavityGeneratedObservedRawFutureSourceMeasure_budget μ a ha hμ W c γ j M _ ih
        (cavityGeneratedActualObservedRawStreamingTerm_support μ a ha S previous)
      exact observedRawTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedObservedRawStreamingInitialLeafCount S) r _ hc.2.2.2 hb
  | @normalizer r m W M previous c ih =>
      have hc := observedRawTerm_actual_costs μ a S previous c
      have hb := cavityGeneratedObservedRawNormalizerForest_budget a ha.2 (parisiFreeMeasure μ a)
        (cavityGenerated_free_mass_le_one μ a ha.1) M _ ih
      apply observedRawTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedObservedRawStreamingInitialLeafCount S) r 1 hc.1
      simpa only [one_mul] using hb

end QuantitativeFollowup
