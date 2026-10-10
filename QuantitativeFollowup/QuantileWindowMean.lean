module
public import QuantitativeFollowup.QuantileWindowAveraging
public import QuantitativeFollowup.VectorMeanMartingale
public import QuantitativePaper.VectorOverlapScoreRegularity
public import QuantitativePaper.VectorWeightedOverlapScore

@[expose] public section

/-! The literal padded-window mean and its exact Stieltjes-kernel form. -/
noncomputable section
open Set MeasureTheory Filter QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorQuantileWindowMean (μ : Paper.ParisiMeasure) (s β t v x : ℝ) (ht : t≤1)
    (sample : VectorDisorderBrownianSample n) : Field n :=
  ∫w,vectorMeasureSpinMean μ β t ht (parisiPaddedFreeQuantile μ s w) sample
    ∂quantileWindowAveraging v x

theorem norm_vectorMeasureSpinMean_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureSpinMean μ β t ht q sample‖≤Real.sqrt (n:ℝ) :=
  norm_vectorMeasureGradient_le μ β t ht q sample.1
    (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample)

theorem measurable_padded_vectorMeasureSpinMean (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) :
    Measurable (fun z : ℝ×VectorDisorderBrownianSample n=>
      vectorMeasureSpinMean μ β t ht (parisiPaddedFreeQuantile μ s z.1) z.2) := by
  have hm:= (measurable_uncurry_vectorMeasureSpinMean (n:=n) μ β t ht).comp
    (((measurable_parisiPaddedFreeQuantile μ s).comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def] using hm

theorem measurable_vectorQuantileWindowMean (μ : Paper.ParisiMeasure)
    (s β t v x : ℝ) (ht : t≤1) : Measurable (vectorQuantileWindowMean (n:=n) μ s β t v x ht) :=
  ((measurable_padded_vectorMeasureSpinMean μ s β t ht).stronglyMeasurable.integral_prod_left'
    (μ:=quantileWindowAveraging v x)).measurable

theorem norm_vectorQuantileWindowMean_le (μ : Paper.ParisiMeasure)
    (s β t v x : ℝ) (ht : t≤1) (hx : 0<x) (sample : VectorDisorderBrownianSample n) :
    ‖vectorQuantileWindowMean μ s β t v x ht sample‖≤Real.sqrt (n:ℝ) := by
  let :=quantileWindowAveraging_probability v x hx
  have h:=norm_integral_le_of_norm_le
    (integrable_const (Real.sqrt (n:ℝ)) : Integrable _ (quantileWindowAveraging v x))
    (.of_forall fun w=>norm_vectorMeasureSpinMean_le μ β t ht (parisiPaddedFreeQuantile μ s w) sample)
  simpa only [vectorQuantileWindowMean,integral_const,probReal_univ,one_smul] using h

theorem vectorQuantileWindowMean_eq_kernel (μ : Paper.ParisiMeasure)
    (s β t v x : ℝ) (ht : t≤1) (hv : v≤1-s) (hx : 0<x) (sample : VectorDisorderBrownianSample n) :
    vectorQuantileWindowMean μ s β t v x ht sample=
      ∫q,quantileWindowKernel μ s v x q • vectorMeasureSpinMean μ β t ht q sample ∂parisiFreeMeasure μ s := by
  have hm:Measurable (fun q : Paper.Overlap=>vectorMeasureSpinMean μ β t ht q sample):=by
    have h:=(measurable_uncurry_vectorMeasureSpinMean (n:=n) μ β t ht).comp
      (measurable_id.prodMk (measurable_const (a:=sample)))
    simpa only [Function.comp_def,id_eq] using h
  exact integral_padded_window_eq_kernel μ s v x hv hx _ hm (vectorMeasureSpinMean_zero μ β t ht sample)

theorem vectorMeasureOverlapScore_zero (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (p : VectorDisorderBrownianSample n×Configuration n) :
    vectorMeasureOverlapScore μ β t ht QuantitativePaper.zeroOverlap p=0 := by
  have hz : vectorMeasureSpinMean μ β t ht QuantitativePaper.zeroOverlap p.1=0:=
    vectorMeasureSpinMean_zero μ β t ht p.1
  rw [vectorMeasureOverlapScore,hz]
  simp [normalizedSpinScore,fieldDot]

theorem vectorQuantileWindowScore_eq_kernel (μ : Paper.ParisiMeasure)
    (s β t v x : ℝ) (ht : t≤1) (hv : v≤1-s) (hx : 0<x)
    (p : VectorDisorderBrownianSample n×Configuration n) :
    (∫w,vectorMeasureOverlapScore μ β t ht (parisiPaddedFreeQuantile μ s w) p
      ∂quantileWindowAveraging v x)=
      vectorMeasureWeightedOverlapScore μ s β t ht (quantileWindowKernel μ s v x) p := by
  have hm : Measurable (fun q : Paper.Overlap=>vectorMeasureOverlapScore μ β t ht q p) := by
    have h:=(measurable_uncurry_vectorMeasureOverlapScore (n:=n) μ β t ht).comp
      (measurable_id.prodMk (measurable_const (a:=p)))
    simpa only [Function.comp_def,id_eq] using h
  simpa only [vectorMeasureWeightedOverlapScore,smul_eq_mul] using integral_padded_window_eq_kernel μ s v x hv hx _ hm
    (vectorMeasureOverlapScore_zero μ β t ht p)

end QuantitativeFollowup
