module
public import QuantitativeFollowup.SupportingGeneratedForestLeafCounts
public import QuantitativeFollowup.FollowupCavityGeneratedForestHistoryStreamingBase

@[expose] public section

/-! The actual starting integrated sibling forest, including independent
components and a joint history-dependent test. The single original mark is
drawn from the free measure. Every distinct original pair branches at that
mark, and its unit budget is derived from the genuine pushforward law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n C : ℕ}

def printedGeneratedInitialHistory (p : Paper.Overlap) : CavityGeneratedHistory Paper.Overlap 1 :=
  fun _ => p

theorem continuous_printedGeneratedInitialHistory : Continuous printedGeneratedInitialHistory :=
  continuous_pi fun _ => continuous_id

theorem measurable_printedGeneratedInitialHistory : Measurable printedGeneratedInitialHistory :=
  continuous_printedGeneratedInitialHistory.measurable

def printedGeneratedInitialHistoryMeasure (ν : Measure Paper.Overlap) :
    Measure (CavityGeneratedHistory Paper.Overlap 1) := ν.map printedGeneratedInitialHistory

theorem printedGeneratedInitialHistoryMeasure_eq_program (ν : Measure Paper.Overlap) :
    printedGeneratedInitialHistoryMeasure ν =
      (CavityGeneratedMarkProgram.initial : CavityGeneratedMarkProgram Paper.Overlap 1).measure ν := rfl

theorem printedGeneratedInitialHistoryMeasure_mass (ν : Measure Paper.Overlap) :
    printedGeneratedInitialHistoryMeasure ν univ = ν univ := by
  rw [printedGeneratedInitialHistoryMeasure,
    Measure.map_apply measurable_printedGeneratedInitialHistory MeasurableSet.univ,preimage_univ]

theorem printedGeneratedInitialHistoryMeasure_coordinate (ν : Measure Paper.Overlap) (i : Fin 1) :
    (printedGeneratedInitialHistoryMeasure ν).map (cavityGeneratedHistoryMarks i) = ν := by
  rw [printedGeneratedInitialHistoryMeasure,
    Measure.map_map (cavityGeneratedHistoryMarks_measurable i) measurable_printedGeneratedInitialHistory]
  change ν.map id = ν
  exact Measure.map_id

theorem printedGeneratedInitialHistoryMeasure_budget (ν : Measure Paper.Overlap) [SFinite ν]
    (hν : ν univ ≤ 1) :
    cavityGeneratedMarkBudget ν (printedGeneratedInitialHistoryMeasure ν)
      cavityGeneratedHistoryMarks 1 := by
  simpa only [printedGeneratedInitialHistoryMeasure_eq_program,CavityGeneratedMarkProgram.budget,
    Nat.cast_one] using
    (CavityGeneratedMarkProgram.initial : CavityGeneratedMarkProgram Paper.Overlap 1).actual_mark_budget ν hν

theorem printedGeneratedInitialFreeHistory_budget (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (printedGeneratedInitialHistoryMeasure (parisiFreeMeasure μ a)) cavityGeneratedHistoryMarks 1 :=
  printedGeneratedInitialHistoryMeasure_budget _ (cavityGenerated_free_mass_le_one μ a ha)

theorem printedGeneratedInitialSiblingForest_order (S : Fin C → CavityGeneratedSiblingShape)
    (h : CavityGeneratedHistory Paper.Overlap 1) :
    h ∈ (cavityGeneratedInitialSiblingForest S).clockTemplate.orderSet := by
  rw [cavityGeneratedInitialSiblingForest_orderSet_eq_univ]
  exact mem_univ h

theorem printedGeneratedInitialSiblingForest_order_ae (S : Fin C → CavityGeneratedSiblingShape)
    (ν : Measure Paper.Overlap) :
    ∀ᵐh ∂printedGeneratedInitialHistoryMeasure ν,
      h ∈ (cavityGeneratedInitialSiblingForest S).clockTemplate.orderSet :=
  .of_forall (printedGeneratedInitialSiblingForest_order S)

theorem printedGeneratedInitialSiblingForest_leafCount (S : Fin C → CavityGeneratedSiblingShape) :
    cavityGeneratedForestLeafCount (cavityGeneratedInitialSiblingForest S) =
      ∑c : Fin C,FiniteCascadeGenealogy.leafCount (asGenealogy (S c).tree) := rfl

theorem printedGeneratedInitialSiblingForest_pair_clock
    (S : Fin C → CavityGeneratedSiblingShape) (c : Fin C)
    (b e : ObservationLeaf ((cavityGeneratedInitialSiblingForest S).tree c)) (hbe : b ≠ e)
    (p : Paper.Overlap) :
    (cavityGeneratedInitialSiblingForest S).clockTemplate.clock (printedGeneratedInitialHistory p) c
      (observationCommonLevel ((cavityGeneratedInitialSiblingForest S).tree c) b e) = p := by
  let W := cavityGeneratedInitialSiblingForest S
  have hj := cavityGenerated_observationCommonLevel_le (W.tree c) b e
  obtain ⟨i,hi⟩ := W.clockTemplate.branch_label c b e hbe
  change W.label c ⟨observationCommonLevel (W.tree c) b e,by omega⟩ = .mark i at hi
  rw [W.clockTemplate.clock_eq_raw_of_mem _ (printedGeneratedInitialSiblingForest_order S _) c _ hj]
  change (if hd : observationCommonLevel (W.tree c) b e ≤ W.depth c then
    (W.label c ⟨observationCommonLevel (W.tree c) b e,by omega⟩).value (printedGeneratedInitialHistory p)
    else 0) = p
  rw [dif_pos hj,hi]
  rfl

theorem printedGeneratedInitialSiblingForest_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ν : Measure Paper.Overlap) (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 →
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    (∫h,∫σ,F h σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a
      (cavityGeneratedInitialSiblingForest S).depth (cavityGeneratedInitialSiblingForest S).tree
      ((cavityGeneratedInitialSiblingForest S).clockTemplate.clock h) : Measure _)
      ∂printedGeneratedInitialHistoryMeasure ν) =
    ∫p,∫σ,F (printedGeneratedInitialHistory p) σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a
      (cavityGeneratedInitialSiblingForest S).depth (cavityGeneratedInitialSiblingForest S).tree
      ((cavityGeneratedInitialSiblingForest S).clockTemplate.clock (printedGeneratedInitialHistory p)) : Measure _)
      ∂ν := by
  have hm := hF.stronglyMeasurable.integral_kernel_prod_right'
    (κ:=cavityGeneratedForestTerminalKernel D μ a (cavityGeneratedInitialSiblingForest S))
  have hm' : StronglyMeasurable (fun h => ∫σ,F h σ
      ∂cavityGeneratedForestTerminalKernel D μ a (cavityGeneratedInitialSiblingForest S) h) := by
    simpa only [Function.uncurry_apply_pair] using hm
  change (∫h,∫σ,F h σ ∂cavityGeneratedForestTerminalKernel D μ a (cavityGeneratedInitialSiblingForest S) h
    ∂ν.map printedGeneratedInitialHistory) = _
  exact integral_map measurable_printedGeneratedInitialHistory.aemeasurable hm'.aestronglyMeasurable

theorem printedGeneratedInitialSiblingForest_history_integral
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ν : Measure Paper.Overlap)
    (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 →
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    (hF : Measurable (Function.uncurry F)) (u : ℝ) :
    followupCavityGeneratedForestHistoryExpectation β ρ hβ hρ μ a
      (cavityGeneratedInitialSiblingForest S) (printedGeneratedInitialHistoryMeasure ν) F u =
      ∫p,followupCavityGeneratedForestTerminalExpectation β ρ hβ hρ μ a
        (cavityGeneratedInitialSiblingForest S).depth (cavityGeneratedInitialSiblingForest S).tree
        ((cavityGeneratedInitialSiblingForest S).clockTemplate.clock (printedGeneratedInitialHistory p))
        (F (printedGeneratedInitialHistory p)) u ∂ν := by
  unfold followupCavityGeneratedForestHistoryExpectation
  by_cases hu : u ∈ Icc (0:ℝ) 1
  · simp only [followupCavityGeneratedForestTerminalExpectation,dif_pos hu]
    exact printedGeneratedInitialSiblingForest_integral _ μ a ν S F hF
  · simp only [followupCavityGeneratedForestTerminalExpectation,dif_neg hu,integral_zero]

end QuantitativeFollowup
