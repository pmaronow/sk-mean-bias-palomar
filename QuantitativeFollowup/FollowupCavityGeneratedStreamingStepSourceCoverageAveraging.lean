module
public import QuantitativeFollowup.FollowupCavityGeneratedForestStreamingReplacement
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixPayload

@[expose] public section

/-! Actual probability averaging of the joint test commutes with each
marked source callback. These identities use finite terminal-test
linearity, preserve the unused component probability, and divide by no
streaming coefficient. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ} {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedNativeForest_pattern_partial_integral_eq_average
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ) (c : I)
    (P : NativeStreamingAttachmentPattern (T c)) :
    (∫σ,nativeStreamingPatternMoment D μ a (q c) (T c)
      (cavityGeneratedForestPartialTerminalTest J T F c σ) P
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
    nativeStreamingPatternMoment D μ a (q c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) P := by
  apply cavityGeneratedNativeForest_partial_functional_integral D μ a J T q F c
    (fun G => nativeStreamingPatternMoment D μ a (q c) (T c) G P)
  intro G
  exact nativeStreamingPatternMoment_terminal_basis D μ a (q c) (T c) G P

private theorem average_mask
    {X : Type*} [MeasurableSpace X] (N : Measure X)
    {j : ℕ} (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (Φ : X → NativeStreamingOrigin T → ℝ) (o : NativeStreamingOrigin T) :
    (∫x,cavityGeneratedOriginCellMask q T (Φ x) o ∂N)=
    cavityGeneratedOriginCellMask q T (fun p=>∫x,Φ x p ∂N) o := by
  cases o with
  | vertex v => rfl
  | edge e r =>
    by_cases hr : r∈Ioc (q (e.depth+1)) (q e.depth) <;>
      simp only [cavityGeneratedOriginCellMask,hr,ite_true,ite_false,integral_zero]

theorem cavityGeneratedNativeForest_originalFreshPayload_average
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ) (c : I)
    (i : ObservationLeaf (T c)) (g : CavityGeneratedOriginSelection (T c)) :
    (∫σ,cavityGeneratedSelectedOriginalFreshPayload D μ a (q c) (T c)
      (cavityGeneratedForestPartialTerminalTest J T F c σ) i g
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
    cavityGeneratedSelectedOriginalFreshPayload D μ a (q c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) i g := by
  unfold cavityGeneratedSelectedOriginalFreshPayload cavityGeneratedSelectedOriginPayload
  rw [average_mask]
  simp_rw [cavityGeneratedNativeForest_pattern_partial_integral_eq_average]

theorem cavityGeneratedNativeForest_currentPayload_average
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ) (c : I)
    (g : CavityGeneratedOriginSelection (T c)) :
    (∫σ,cavityGeneratedSelectedCurrentPayload D μ a (q c) (T c)
      (cavityGeneratedForestPartialTerminalTest J T F c σ) g
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
    cavityGeneratedSelectedCurrentPayload D μ a (q c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) g := by
  unfold cavityGeneratedSelectedCurrentPayload cavityGeneratedSelectedOriginPayload
  rw [average_mask]
  simp_rw [integral_const_mul,cavityGeneratedNativeForest_pattern_partial_integral_eq_average]

theorem cavityGeneratedNativeForest_crossPayload_average
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ) (c : I)
    (z : CavityGeneratedOriginSelection (T c) × CavityGeneratedOriginSelection (T c)) :
    (∫σ,cavityGeneratedSelectedCrossPayload D μ a (q c) (T c)
      (cavityGeneratedForestPartialTerminalTest J T F c σ) z
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
    cavityGeneratedSelectedCrossPayload D μ a (q c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) z := by
  unfold cavityGeneratedSelectedCrossPayload cavityGeneratedSelectedOriginPayload
  rw [average_mask]
  simp_rw [average_mask,cavityGeneratedNativeForest_pattern_partial_integral_eq_average]

theorem cavityGeneratedNativeForest_futureCellPayload_average
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ) (c : I)
    (j : ℕ) (z : CavityGeneratedOriginSelection (T c) × Paper.Overlap) :
    (∫σ,cavityGeneratedSelectedFutureCellPayload D μ a (q c) (T c)
      (cavityGeneratedForestPartialTerminalTest J T F c σ) j z
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
    cavityGeneratedSelectedFutureCellPayload D μ a (q c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) j z := by
  unfold cavityGeneratedSelectedFutureCellPayload cavityGeneratedSelectedOriginPayload
  rw [average_mask]
  congr 1
  funext o
  by_cases ho : z.2∈Ioc (q c (j+1)) (q c j) ∧ nativeStreamingOriginLevel (q c) o<z.2
  · simp only [if_pos ho]
    exact cavityGeneratedNativeForest_pattern_partial_integral_eq_average D μ a J T q F c _
  · simp only [if_neg ho,integral_zero]

theorem cavityGeneratedNativeForest_futurePayload_average
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ) (c : I)
    (z : CavityGeneratedOriginSelection (T c) × Paper.Overlap) :
    (∫σ,cavityGeneratedSelectedFuturePayload D μ a (q c) (T c)
      (cavityGeneratedForestPartialTerminalTest J T F c σ) z
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
    cavityGeneratedSelectedFuturePayload D μ a (q c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) z := by
  unfold cavityGeneratedSelectedFuturePayload
  rw [integral_finset_sum _ (fun j _ => by
    simpa only [integrableOn_univ] using IntegrableOn.of_finite
      (μ:=(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _))
      (f:=fun σ=>cavityGeneratedSelectedFutureCellPayload D μ a (q c) (T c)
        (cavityGeneratedForestPartialTerminalTest J T F c σ) j z)
      (s:=Set.univ) Set.finite_univ)]
  simp_rw [cavityGeneratedNativeForest_futureCellPayload_average]

end QuantitativeFollowup
