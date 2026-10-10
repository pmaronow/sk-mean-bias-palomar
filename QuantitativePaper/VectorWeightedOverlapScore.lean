module
public import QuantitativePaper.VectorOverlapScoreRegularity
public import QuantitativeFollowup.ParisiFreeGrid
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Genuine deterministic-kernel integrals of the marked spin score.
The finite-grid integrals are expressed on the original free measure,
including partial root atoms, and converge under the actual joint laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureWeightedOverlapScore (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1)
    (κ : Paper.Overlap→ℝ) (p : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  ∫q,κ q*vectorMeasureOverlapScore μ β t ht q p ∂parisiFreeMeasure μ s

def vectorDyadicWeightedOverlapScore (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1)
    (κ : Paper.Overlap→ℝ) (j : ℕ) (p : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  ∫q,κ (Paper.parisiGridRound (vectorDyadicIndex j) q)*
    vectorDyadicOverlapScore μ β t ht q j p ∂parisiFreeMeasure μ s

theorem measurable_vectorMeasureWeightedOverlapScore (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) :
    Measurable (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht κ) := by
  have hm : Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      κ z.1*vectorMeasureOverlapScore μ β t ht z.1 z.2) :=
    (hκ.comp measurable_fst).mul (measurable_uncurry_vectorMeasureOverlapScore μ β t ht)
  exact (hm.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ s)).measurable

theorem measurable_vectorDyadicWeightedOverlapScore (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (j : ℕ) :
    Measurable (vectorDyadicWeightedOverlapScore (n:=n) μ s β t ht κ j) := by
  have hm : Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      κ (Paper.parisiGridRound (vectorDyadicIndex j) z.1)*
        vectorDyadicOverlapScore μ β t ht z.1 j z.2) :=
    ((hκ.comp (Paper.measurable_parisiGridRound _)).comp measurable_fst).mul
      (measurable_uncurry_vectorDyadicOverlapScore μ β t ht j)
  exact (hm.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ s)).measurable

private theorem norm_free_integral_le (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0 : ℝ) 1) (f : Paper.Overlap→ℝ) (B : ℝ) (hB : 0≤B)
    (hb : ∀q,‖f q‖≤B) : ‖∫q,f q ∂parisiFreeMeasure μ s‖≤B := by
  have hi:=norm_integral_le_of_norm_le (integrable_const B : Integrable _ (parisiFreeMeasure μ s))
    (.of_forall hb)
  have he : (∫_q : Paper.Overlap,B ∂parisiFreeMeasure μ s)=(1-s)*B := by
    simp only [integral_const,Measure.real,parisiFreeMeasure_univ,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2),smul_eq_mul]
  rw [he] at hi
  exact hi.trans (by nlinarith [mul_nonneg hs.1 hB])

theorem vectorMeasureWeightedOverlapScore_bound (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (hs : s∈Icc (0 : ℝ) 1) (κ : Paper.Overlap→ℝ)
    (K : ℝ) (hK : 0≤K) (hκ : ∀q,|κ q|≤K)
    (p : VectorDisorderBrownianSample n×Configuration n) :
    ‖vectorMeasureWeightedOverlapScore μ s β t ht κ p‖≤K*(3/2) := by
  apply norm_free_integral_le μ s hs _ _ (by positivity)
  intro q
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact mul_le_mul (hκ q) (vectorMeasureOverlapScore_bound μ β t ht q p)
    (abs_nonneg _) hK

theorem vectorDyadicWeightedOverlapScore_bound (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (hs : s∈Icc (0 : ℝ) 1) (κ : Paper.Overlap→ℝ)
    (K : ℝ) (hK : 0≤K) (hκ : ∀q,|κ q|≤K) (j : ℕ)
    (p : VectorDisorderBrownianSample n×Configuration n) :
    ‖vectorDyadicWeightedOverlapScore μ s β t ht κ j p‖≤K*(3/2) := by
  apply norm_free_integral_le μ s hs _ _ (by positivity)
  intro q
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact mul_le_mul (hκ _) (vectorDyadicOverlapScore_bound μ β t ht q j p)
    (abs_nonneg _) hK

theorem tendsto_vectorDyadicWeightedOverlapScore (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Continuous κ)
    (K : ℝ) (hK : 0≤K) (hbκ : ∀q,|κ q|≤K)
    (sample : VectorDisorderBrownianSample n) (σ : Configuration n) :
    Tendsto (fun j=>vectorDyadicWeightedOverlapScore μ s β t ht κ j (sample,σ)) atTop
      (𝓝 (vectorMeasureWeightedOverlapScore μ s β t ht κ (sample,σ))) := by
  apply tendsto_integral_of_dominated_convergence (fun _=>K*(3/2))
  · intro j
    have hm : Measurable (fun q : Paper.Overlap=>vectorDyadicOverlapScore μ β t ht q j (sample,σ)) := by
      have hh := (measurable_uncurry_vectorDyadicOverlapScore (n:=n) μ β t ht j).comp
        (measurable_id.prodMk (measurable_const : Measurable
          (fun _ : Paper.Overlap=>(sample,σ))))
      simpa only [Function.comp_def,id_eq] using hh
    exact ((hκ.measurable.comp (Paper.measurable_parisiGridRound _)).mul hm).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact .of_forall fun q=>by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact mul_le_mul (hbκ _) (vectorDyadicOverlapScore_bound μ β t ht q j (sample,σ))
        (abs_nonneg _) hK
  · exact .of_forall fun q=>
      ((hκ.tendsto q).comp ((Paper.tendsto_parisiGridRound q).comp
        tendsto_vectorDyadicIndex)).mul (tendsto_vectorDyadicOverlapScore μ β t ht q sample σ)

theorem tendsto_variance_vectorDyadicWeightedOverlapScore (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (hs : s∈Icc (0 : ℝ) 1)
    (κ : Paper.Overlap→ℝ) (hκ : Continuous κ) (K : ℝ) (hK : 0≤K)
    (hbκ : ∀q,|κ q|≤K) :
    Tendsto (fun j=>variance (vectorDyadicWeightedOverlapScore (n:=n) μ s β t ht κ j)
      (vectorFiniteSpinPathLaw (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t s ht))
      atTop (𝓝 (variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht κ)
        (vectorMeasureSpinPathLaw μ β t s ht))) := by
  exact tendsto_variance_vectorDyadicSpinPathLaw_bounded μ β t s ht _ _ (K*(3/2))
    (by positivity) (fun j=>measurable_vectorDyadicWeightedOverlapScore μ s β t ht κ hκ.measurable j)
    (measurable_vectorMeasureWeightedOverlapScore μ s β t ht κ hκ.measurable)
    (vectorDyadicWeightedOverlapScore_bound μ s β t ht hs κ K hK hbκ)
    (vectorMeasureWeightedOverlapScore_bound μ s β t ht hs κ K hK hbκ)
    (tendsto_vectorDyadicWeightedOverlapScore μ s β t ht κ hκ K hK hbκ)

end QuantitativePaper
