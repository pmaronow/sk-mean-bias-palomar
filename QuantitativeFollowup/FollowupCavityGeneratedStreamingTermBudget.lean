module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTermCounts
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTermOrder
public import QuantitativeFollowup.SupportingGeneratedStreamingTermCost

@[expose] public section

/-! Mark-budget induction for the genuine six-operation term grammar.
Only the model floor and mass assumptions enter the public induction;
all per-path counts and coefficients come from the actual constructors. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {C m : ℕ}

private theorem streamingTermMarkBudget_const_mono
    (ν : Measure Paper.Overlap) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (A B : ℝ≥0∞) (hAB : A ≤ B)
    (hM : cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks A) :
    cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks B :=
  ⟨hM.1.trans hAB,fun i => (hM.2 i).trans (cavityGenerated_smul_mono ν hAB)⟩

private theorem streamingTermMarkBudget_next
    (ν : Measure Paper.Overlap) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (K0 r : ℕ) (k : ℝ≥0∞)
    (hk : k ≤ (printedGeneratedStreamingStepCost
      (printedGeneratedStreamingLeafBound K0 r) (printedGeneratedStreamingMarkBound r) : ℝ≥0∞))
    (hM : cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks
      (k*(printedGeneratedStreamingBudget K0 r : ℝ≥0∞))) :
    cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks
      (printedGeneratedStreamingBudget K0 (r+1) : ℝ≥0∞) := by
  rw [printedGeneratedStreamingBudget_succ_ennreal]
  exact streamingTermMarkBudget_const_mono ν M _ _
    (mul_le_mul_left hk (printedGeneratedStreamingBudget K0 r : ℝ≥0∞)) hM


private theorem streamingTerm_actual_costs
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape)
    {r m : ℕ} {W : CavityGeneratedConstructedForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualStreamingTerm μ a S r m W M) (c : Fin W.componentCount) :
    let B : ℝ≥0∞ := printedGeneratedStreamingStepCost
      (printedGeneratedStreamingLeafBound (cavityGeneratedStreamingInitialLeafCount S) r)
      (printedGeneratedStreamingMarkBound r)
    let A : ℝ≥0∞ := (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
      ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞)
    1 ≤ B ∧ 2*A ≤ B ∧ A^2 ≤ B ∧ A ≤ B := by
  let K := printedGeneratedStreamingLeafBound (cavityGeneratedStreamingInitialLeafCount S) r
  let L := printedGeneratedStreamingMarkBound r
  have hc := cavityGeneratedActualStreamingTerm_counts μ a S H
  have hpos : 0 < K := cavityGenerated_component_leaf_bound_pos W c K hc.2.2
  have hA := cavityGenerated_component_origin_cost_le_uniform_ennreal W c hc.1 K L hc.2.2 hc.2.1
  have hb := printedGeneratedStreamingTermCosts_le_ennreal K L hpos
  refine ⟨hb.1,?_,?_,hA.trans hb.2.2.2⟩
  · exact (mul_le_mul_of_nonneg_left hA (by positivity)).trans hb.2.1
  · exact (pow_le_pow_left₀ (by positivity) hA 2).trans hb.2.2.1

theorem cavityGeneratedActualStreamingTerm_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (S : Fin C → CavityGeneratedSiblingShape)
    {r m : ℕ} {W : CavityGeneratedConstructedForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualStreamingTerm μ a S r m W M) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks
      (printedGeneratedStreamingBudget (cavityGeneratedStreamingInitialLeafCount S) r : ℝ≥0∞) := by
  induction H with
  | initial =>
      simpa only [printedGeneratedStreamingBudget_zero,Nat.cast_one] using
        printedGeneratedInitialFreeHistory_budget μ a ha.1
  | @original r m W M previous c b e ih =>
      have hc := streamingTerm_actual_costs μ a S previous c
      apply streamingTermMarkBudget_next (parisiFreeMeasure μ a) M
        (cavityGeneratedStreamingInitialLeafCount S) r 1 hc.1
      simpa only [one_mul] using ih
  | @originalFresh r m W M previous c b γ ih =>
      haveI : IsFiniteMeasure M := ⟨ih.1.trans_lt (ENNReal.natCast_lt_top _)⟩
      have hc := streamingTerm_actual_costs μ a S previous c
      have hb := cavityGeneratedOriginalFreshChartMeasure_budget μ a ha hμ W c M γ _ ih
        (cavityGeneratedActualStreamingTerm_order μ a ha S previous)
      exact streamingTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedStreamingInitialLeafCount S) r _ hc.2.1 hb
  | @cross r m W M previous c γ δ χ ih =>
      haveI : IsFiniteMeasure M := ⟨ih.1.trans_lt (ENNReal.natCast_lt_top _)⟩
      have hc := streamingTerm_actual_costs μ a S previous c
      have hb := cavityGeneratedCrossOriginChartMeasure_budget μ a ha hμ W c M γ δ χ _ ih
        (cavityGeneratedActualStreamingTerm_order μ a ha S previous)
      exact streamingTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedStreamingInitialLeafCount S) r _ hc.2.2.1 hb
  | @current r m W M previous c γ ih =>
      haveI : IsFiniteMeasure M := ⟨ih.1.trans_lt (ENNReal.natCast_lt_top _)⟩
      have hc := streamingTerm_actual_costs μ a S previous c
      have hb := cavityGeneratedCurrentChartMeasure_budget μ a ha hμ W c M γ _ ih
        (cavityGeneratedActualStreamingTerm_order μ a ha S previous)
      exact streamingTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedStreamingInitialLeafCount S) r _ hc.2.2.2 hb
  | @future r m W M previous c γ j ih =>
      haveI : IsFiniteMeasure M := ⟨ih.1.trans_lt (ENNReal.natCast_lt_top _)⟩
      have hc := streamingTerm_actual_costs μ a S previous c
      have hb := cavityGeneratedFutureOriginChartSourceMeasure_budget μ a ha hμ W c M γ j _ ih
        (cavityGeneratedActualStreamingTerm_order μ a ha S previous)
      exact streamingTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedStreamingInitialLeafCount S) r _ hc.2.2.2 hb
  | @normalizer r m W M previous c ih =>
      have hc := streamingTerm_actual_costs μ a S previous c
      have hb := cavityGeneratedNormalizerFamilyMeasure_budget a ha.2 (parisiFreeMeasure μ a)
        (cavityGenerated_free_mass_le_one μ a ha.1) M _ ih
      apply streamingTermMarkBudget_next (parisiFreeMeasure μ a) _
        (cavityGeneratedStreamingInitialLeafCount S) r 1 hc.1
      simpa only [one_mul] using hb

end QuantitativeFollowup
