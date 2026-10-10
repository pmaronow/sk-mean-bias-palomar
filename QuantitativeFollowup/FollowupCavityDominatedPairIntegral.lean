module
public import QuantitativeFollowup.FollowupCavityPairProductBounds

@[expose] public section

/-! Genuine integral domination for a two-defect observable multiplied
by any measurable spin factor whose absolute value is at most one. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem abs_integral_le_integral_abs_of_domination {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P)
    (h : ∀ω, |f ω| ≤ |g ω|) : |∫ω, f ω ∂P| ≤ ∫ω, |g ω| ∂P := by
  have hh : |∫ω, f ω ∂P| ≤ ∫ω, |f ω| ∂P := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := P) (f := f))
  exact hh.trans (integral_mono hf.abs hg.abs h)

theorem integrable_cavityDominatedPair {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i l : Fin 2 → ObservationLeaf T)
    (R : Ω → CavityPathRecordSpace T (n+1)) (F : Ω → ℝ) (hF : Measurable F)
    (hdom : ∀ω, |F ω| ≤ |cavityRecordedPairProduct s T i l (R ω)|) : Integrable F P := by
  apply (integrable_const (4 : ℝ)).mono' hF.aestronglyMeasurable
  exact .of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using
      (hdom ω).trans (cavityRecordedPairProduct_abs_le_four s T i l (R ω))

theorem abs_integral_cavityDominatedPair_mul_defect {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i l : Fin 2 → ObservationLeaf T)
    (R : Ω → CavityPathRecordSpace T (n+1)) (hR : Measurable R)
    (F : Ω → ℝ) (hF : Measurable F)
    (hdom : ∀ω, |F ω| ≤ |cavityRecordedPairProduct s T i l (R ω)|)
    (σ τ : Ω → Configuration (n+1)) (hσ : Measurable σ) (hτ : Measurable τ)
    (q : Paper.Overlap) :
    |∫ω, F ω*cavitySpinOverlapDefect n q (σ ω) (τ ω) ∂P| ≤
      ∫ω, |cavityRecordedPairProduct s T i l (R ω)*
        cavitySpinOverlapDefect n q (σ ω) (τ ω)| ∂P := by
  have hFb (ω) : |F ω| ≤ 4 :=
    (hdom ω).trans (cavityRecordedPairProduct_abs_le_four s T i l (R ω))
  exact abs_integral_le_integral_abs_of_domination P _ _
    (integrable_bounded_pair_mul_cavityDefect P F hF hFb σ τ hσ hτ q)
    (integrable_bounded_pair_mul_cavityDefect P _
      ((measurable_cavityRecordedPairProduct s T i l).comp hR)
      (fun ω => cavityRecordedPairProduct_abs_le_four s T i l (R ω)) σ τ hσ hτ q)
    (fun ω => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hdom ω) (abs_nonneg _))

end QuantitativeFollowup
