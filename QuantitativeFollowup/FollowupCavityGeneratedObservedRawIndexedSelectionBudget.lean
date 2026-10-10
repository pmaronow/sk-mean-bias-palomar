module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawSelectionBudget
public import QuantitativeFollowup.FollowupCavityGeneratedOriginUniversalBudget
public import QuantitativeFollowup.FollowupCavityGeneratedIndexedAppendPayloadBudget

@[expose] public section

/-! Different actual raw forest charts share one aggregate history
budget. The inherited-fork majorant uses every old coordinate a computed
number of times, so varying static fork indices add no chart-count factor. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ} {I : Type*} [Fintype I]

theorem cavityGeneratedMarkBudget_mono_constant
    {H Q : Type*} [MeasurableSpace H] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (ν : Measure Q) (M : Measure H) (marks : Fin m → H → Q)
    (C D : ℝ≥0∞) (hM : cavityGeneratedMarkBudget ν M marks C) (hCD : C ≤ D) :
    cavityGeneratedMarkBudget ν M marks D :=
  ⟨hM.1.trans hCD, fun i => (hM.2 i).trans (cavityGenerated_smul_mono ν hCD)⟩

theorem cavityGeneratedObservedRawOriginSelectionKernel_clock_universal_domination
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (K : ℕ)
    (hK : FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) ≤ K)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h ∈ W.supportSet) :
    (cavityGeneratedObservedRawOriginSelectionKernel μ a W c h).map
      (fun g => cavityGeneratedObservedRawOriginSelectionClock W c (h,g)) ≤
      (K : ℝ≥0∞) • parisiFreeMeasure μ a +
        ∑i : Fin (Fintype.card (Fin (K-1) × Fin m)),
          Measure.dirac (h (cavityGeneratedUniversalForkIndex K m i)) := by
  classical
  have hd := cavityGeneratedObservedRawOriginSelectionKernel_clock_domination μ a ha hμ W c h hh
  have hf : (cavityGeneratedOriginForkVertices (W.tree c)).length ≤ K-1 := by
    have hc := cavityGeneratedOriginForkVertices_count (W.tree c)
    omega
  have hl := cavityGeneratedForkDiracList_le_all_marks
    (List.ofFn (W.component c).forkMark) h
  simp only [List.map_ofFn,List.sum_ofFn,List.length_ofFn,Fintype.card_fin,Function.comp_def] at hl
  apply hd.trans
  apply add_le_add
  · apply cavityGenerated_smul_mono
    exact_mod_cast hK
  · rw [cavityGeneratedUniversalForkIndex_sum]
    exact hl.trans (nsmul_le_nsmul_left bot_le hf)

theorem cavityGeneratedObservedRawIndexedOriginSourceMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : I → CavityGeneratedObservedRawForest m)
    (c : (i : I) → Fin (W i).componentCount) (K : ℕ)
    (hK : ∀i, FiniteCascadeGenealogy.leafCount (asGenealogy ((W i).tree (c i))) ≤ K)
    (M : I → Measure (CavityGeneratedHistory Paper.Overlap m)) [∀i, SFinite (M i)]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) (∑i, M i) cavityGeneratedHistoryMarks C)
    (hsupport : ∀i, ∀ᵐh ∂M i, h ∈ (W i).supportSet)
    (E : (i : I) → Set (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection ((W i).tree (c i)))) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (∑i, cavityGeneratedRawOriginSourceMeasure μ a (fun h => (W i).clock h (c i))
        ((W i).measurable_clock (c i)) ((W i).tree (c i)) (M i) (E i))
      cavityGeneratedHistoryMarks
      (((K : ℝ≥0∞) + (((K-1)*m : ℕ) : ℝ≥0∞))*C) := by
  classical
  let κ (i : I) := cavityGeneratedObservedRawOriginSelectionKernel μ a (W i) (c i)
  let τ (i : I) := cavityGeneratedObservedRawOriginSelectionClock (W i) (c i)
  have hm (i : I) : ∀ᵐh ∂M i, κ i h univ ≤ (K : ℝ≥0∞) := by
    apply Filter.Eventually.of_forall
    intro h
    exact (cavityGeneratedObservedRawOriginSelectionKernel_mass_le μ a ha hμ (W i) (c i) h).trans
      (by exact_mod_cast hK i)
  have hd (i : I) : ∀ᵐh ∂M i, (κ i h).map (fun g => τ i (h,g)) ≤
      (K : ℝ≥0∞) • parisiFreeMeasure μ a +
        ∑j : Fin (Fintype.card (Fin (K-1) × Fin m)),
          Measure.dirac (h (cavityGeneratedUniversalForkIndex K m j)) :=
    (hsupport i).mono fun h hh =>
      cavityGeneratedObservedRawOriginSelectionKernel_clock_universal_domination
        μ a ha hμ (W i) (c i) K (hK i) h hh
  have hb := cavityGeneratedMarkBudget_indexed_kernel_payload_append (parisiFreeMeasure μ a)
    M κ τ (fun i => measurable_cavityGeneratedObservedRawOriginSelectionClock (W i) (c i))
    (cavityGeneratedUniversalForkIndex K m) (K : ℝ≥0∞) C hM hm hd
  rw [cavityGeneratedUniversalForkIndex_count] at hb
  apply cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _ hb
  apply Measure.le_iff.mpr
  intro A hA
  simp only [Measure.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_le_sum
  intro i _
  exact cavityGeneratedRawOriginSourceMeasure_le_full μ a (fun h => (W i).clock h (c i))
    ((W i).measurable_clock (c i)) ((W i).tree (c i)) (M i) (E i) A

end QuantitativeFollowup
