module
public import QuantitativePaper.NormalizedSpinScore
public import QuantitativePaper.VectorMarkedTiltConvergence
public import QuantitativeFollowup.VectorMeanOverlap

@[expose] public section

/-! Actual marked-spin overlap scores for all measures, and their genuine
first/second-moment convergence from the finite-grid diffusion law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureOverlapScore (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  normalizedSpinScore (vectorMeasureSpinMean μ β t ht q p.1) p.2

def vectorDyadicOverlapScore (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (p : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  normalizedSpinScore (vectorDyadicSpinMean μ β t ht q j p.1) p.2

theorem measurable_vectorMeasureOverlapScore (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) : Measurable (vectorMeasureOverlapScore (n:=n) μ β t ht q) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact (continuous_normalizedSpinScore σ).measurable.comp
    ((adapted_vectorMeasureSpinMean μ β t ht q).mono
      ((vectorBrownianFiltration n).le _) le_rfl)

theorem measurable_vectorDyadicOverlapScore (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) :
    Measurable (vectorDyadicOverlapScore (n:=n) μ β t ht q j) := by
  apply measurable_from_prod_countable_left
  intro σ
  have hm : Measurable (vectorDyadicSpinMean (n:=n) μ β t ht q j) := by
    exact (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
      (Measurable.of_eval (fun l=>measurable_vectorDyadicSpinMean_component μ β t ht q j l))
  exact (continuous_normalizedSpinScore σ).measurable.comp hm

theorem vectorMeasureOverlapScore_bound (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (p : VectorDisorderBrownianSample n×Configuration n) :
    |vectorMeasureOverlapScore μ β t ht q p|≤3/2 :=
  normalizedSpinScore_bound _ _ (fun l=>vectorMeasureSpinMean_component_bound μ β t ht q p.1 l)

theorem vectorDyadicOverlapScore_bound (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (p : VectorDisorderBrownianSample n×Configuration n) :
    |vectorDyadicOverlapScore μ β t ht q j p|≤3/2 :=
  normalizedSpinScore_bound _ _ (fun l=>vectorDyadicSpinMean_component_bound μ β t ht q j p.1 l)

theorem tendsto_vectorDyadicOverlapScore (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n)
    (σ : Configuration n) :
    Tendsto (fun j=>vectorDyadicOverlapScore μ β t ht q j (sample,σ)) atTop
      (𝓝 (vectorMeasureOverlapScore μ β t ht q (sample,σ))) :=
  (continuous_normalizedSpinScore σ).tendsto _ |>.comp
    (tendsto_vectorDyadicSpinMean μ β t ht q sample)

theorem tendsto_integral_vectorDyadicOverlapScore (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    Tendsto (fun j=>∫p,vectorDyadicOverlapScore (n:=n) μ β t ht q j p
      ∂vectorFiniteSpinPathLaw (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ht)
      atTop (𝓝 (∫p,vectorMeasureOverlapScore (n:=n) μ β t ht q p
        ∂vectorMeasureSpinPathLaw μ β t a ht)) := by
  apply tendsto_integral_vectorDyadicSpinPathLaw_bounded μ β t a ht _ _ (3/2) (by norm_num)
    (fun j=>measurable_vectorDyadicOverlapScore μ β t ht q j)
    (measurable_vectorMeasureOverlapScore μ β t ht q)
  · intro j p
    simpa only [Real.norm_eq_abs] using vectorDyadicOverlapScore_bound μ β t ht q j p
  · intro p
    simpa only [Real.norm_eq_abs] using vectorMeasureOverlapScore_bound μ β t ht q p
  · exact fun sample σ=>tendsto_vectorDyadicOverlapScore μ β t ht q sample σ

theorem tendsto_variance_vectorDyadicOverlapScore (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    Tendsto (fun j=>variance (vectorDyadicOverlapScore (n:=n) μ β t ht q j)
      (vectorFiniteSpinPathLaw (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ht))
      atTop (𝓝 (variance (vectorMeasureOverlapScore (n:=n) μ β t ht q)
        (vectorMeasureSpinPathLaw μ β t a ht))) := by
  apply tendsto_variance_vectorDyadicSpinPathLaw_bounded μ β t a ht _ _ (3/2) (by norm_num)
    (fun j=>measurable_vectorDyadicOverlapScore μ β t ht q j)
    (measurable_vectorMeasureOverlapScore μ β t ht q)
  · intro j p
    simpa only [Real.norm_eq_abs] using vectorDyadicOverlapScore_bound μ β t ht q j p
  · intro p
    simpa only [Real.norm_eq_abs] using vectorMeasureOverlapScore_bound μ β t ht q p
  · exact fun sample σ=>tendsto_vectorDyadicOverlapScore μ β t ht q sample σ

end QuantitativePaper
