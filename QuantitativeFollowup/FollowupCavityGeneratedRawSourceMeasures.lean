module
public import QuantitativeFollowup.FollowupCavityGeneratedRawOriginMarkBudget

@[expose] public section

/-! Actual raw source measures retain the old history and original
selected payloads until the final physical-clock graph map. Restrictions
are applied to that true joint law; no observation labels are discarded. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {m J : ℕ}

def cavityGeneratedRawOriginAppendedHistory
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T) :
    CavityGeneratedHistory Paper.Overlap (m+1) :=
  Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock q T z)

theorem measurable_cavityGeneratedRawOriginAppendedHistory
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J) :
    Measurable (cavityGeneratedRawOriginAppendedHistory q T) := by
  apply measurable_pi_lambda
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [cavityGeneratedRawOriginAppendedHistory, Fin.snoc_last] using
      measurable_cavityGeneratedRawOriginSelectionClock q hq T
  | cast i => simpa only [cavityGeneratedRawOriginAppendedHistory, Fin.snoc_castSucc,
      Function.comp_def] using (measurable_pi_apply i).comp measurable_fst

def cavityGeneratedRawOriginSourceMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (E : Set (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+1)) :=
  ((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a q hq T).restrict E).map
    (cavityGeneratedRawOriginAppendedHistory q T)

theorem cavityGeneratedRawOriginSourceMeasure_le_full
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (E : Set (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T)) :
    cavityGeneratedRawOriginSourceMeasure μ a q hq T M E ≤
      (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a q hq T).map
        (cavityGeneratedRawOriginAppendedHistory q T) :=
  Measure.map_mono Measure.restrict_le_self
    (measurable_cavityGeneratedRawOriginAppendedHistory q hq T)

theorem cavityGeneratedRawOriginSourceMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (idx : Fin (cavityGeneratedOriginForkVertices T).length → Fin m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, Antitone (q h) ∧ q h 0 = 1 ∧ q h J = zeroOverlap ∧
      ∀i, q h ((cavityGeneratedOriginForkVertices T).get i).depth = h (idx i))
    (E : Set (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T)) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedRawOriginSourceMeasure μ a q hq T M E) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices T).length : ℝ≥0∞))*C) := by
  apply cavityGeneratedMarkBudget_mono (parisiFreeMeasure μ a) cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable _
    (cavityGeneratedRawOriginSelectionKernel_appended_history_budget
      μ a ha hμ q hq T idx M C hM hsupport)
  exact cavityGeneratedRawOriginSourceMeasure_le_full μ a q hq T M E

def cavityGeneratedRawOriginSecondSelectionClock
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T) ×
      CavityGeneratedOriginSelection T) : Paper.Overlap :=
  cavityGeneratedRawOriginSelectionClock q T (z.1.1,z.2)

theorem measurable_cavityGeneratedRawOriginSecondSelectionClock
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J) :
    Measurable (cavityGeneratedRawOriginSecondSelectionClock q T) :=
  (measurable_cavityGeneratedRawOriginSelectionClock q hq T).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

def cavityGeneratedRawOriginDoubleSelectionMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    Measure ((CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T) ×
      CavityGeneratedOriginSelection T) :=
  (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a q hq T) ⊗ₘ
    (cavityGeneratedRawOriginSelectionKernel μ a q hq T).comap Prod.fst measurable_fst

theorem cavityGeneratedRawOriginSecondSelectionKernel_apply
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (h : CavityGeneratedHistory Paper.Overlap m) (g : CavityGeneratedOriginSelection T) :
    ((cavityGeneratedRawOriginSelectionKernel μ a q hq T).comap
      (Prod.fst : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T →
        CavityGeneratedHistory Paper.Overlap m) measurable_fst :
      Kernel (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T)
        (CavityGeneratedOriginSelection T)) (h,g) =
      cavityGeneratedOriginSelectionMeasure μ a (q h) T a := rfl

def cavityGeneratedRawOriginDoubleAppendedHistory
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T) ×
      CavityGeneratedOriginSelection T) : CavityGeneratedHistory Paper.Overlap (m+1+1) :=
  Fin.snoc (cavityGeneratedRawOriginAppendedHistory q T z.1)
    (cavityGeneratedRawOriginSecondSelectionClock q T z)

theorem measurable_cavityGeneratedRawOriginDoubleAppendedHistory
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J) :
    Measurable (cavityGeneratedRawOriginDoubleAppendedHistory q T) := by
  apply measurable_pi_lambda
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [cavityGeneratedRawOriginDoubleAppendedHistory, Fin.snoc_last] using
      measurable_cavityGeneratedRawOriginSecondSelectionClock q hq T
  | cast i => simpa only [cavityGeneratedRawOriginDoubleAppendedHistory, Fin.snoc_castSucc,
      Function.comp_def] using ((measurable_pi_apply i).comp
      ((measurable_cavityGeneratedRawOriginAppendedHistory q hq T).comp measurable_fst))

def cavityGeneratedRawOriginCrossSourceMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (E : Set ((CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T) ×
      CavityGeneratedOriginSelection T)) : Measure (CavityGeneratedHistory Paper.Overlap (m+1+1)) :=
  ((cavityGeneratedRawOriginDoubleSelectionMeasure μ a q hq T M).restrict E).map
    (cavityGeneratedRawOriginDoubleAppendedHistory q T)

def cavityGeneratedRawOriginFutureAppendedHistory
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T) ×
      Paper.Overlap) : CavityGeneratedHistory Paper.Overlap (m+1+1) :=
  Fin.snoc (cavityGeneratedRawOriginAppendedHistory q T z.1) z.2

theorem measurable_cavityGeneratedRawOriginFutureAppendedHistory
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J) :
    Measurable (cavityGeneratedRawOriginFutureAppendedHistory q T) := by
  apply measurable_pi_lambda
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [cavityGeneratedRawOriginFutureAppendedHistory, Fin.snoc_last] using
      (measurable_snd : Measurable (Prod.snd :
        (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T) ×
          Paper.Overlap → Paper.Overlap))
  | cast i => simpa only [cavityGeneratedRawOriginFutureAppendedHistory, Fin.snoc_castSucc,
      Function.comp_def] using ((measurable_pi_apply i).comp
      ((measurable_cavityGeneratedRawOriginAppendedHistory q hq T).comp measurable_fst))

def cavityGeneratedRawOriginFutureSourceMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (E : Set ((CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T) ×
      Paper.Overlap)) : Measure (CavityGeneratedHistory Paper.Overlap (m+1+1)) :=
  (((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a q hq T).prod
    (parisiFreeMeasure μ a)).restrict E).map (cavityGeneratedRawOriginFutureAppendedHistory q T)

end QuantitativeFollowup
