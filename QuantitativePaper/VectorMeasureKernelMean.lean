module
public import QuantitativePaper.VectorWeightedOverlapScore
public import QuantitativePaper.VectorMeasureAffineScoreConditionalVariance

@[expose] public section

/-! Actual deterministic-kernel means and offsets. Full-past adaptation
uses the genuine stopped mean path and almost-everywhere kernel support. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 300000

def vectorMeasureKernelMean (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1)
    (κ : Paper.Overlap→ℝ) (sample : VectorDisorderBrownianSample n) : Field n :=
  ∫q,κ q •vectorMeasureSpinMean μ β t ht q sample ∂parisiFreeMeasure μ s

def vectorMeasureKernelOffset (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1)
    (κ : Paper.Overlap→ℝ) (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∫q,κ q*‖vectorMeasureSpinMean μ β t ht q sample‖^2/2 ∂parisiFreeMeasure μ s

theorem continuous_vectorMeasureSpinMean_path (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun q : Paper.Overlap=>vectorMeasureSpinMean μ β t ht q sample) := by
  have hX : Continuous (fun q : Paper.Overlap=>vectorMeasureState μ β t ht (q:ℝ).toNNReal sample) :=
    (continuous_vectorMeasureState μ β t ht sample).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)
  have hz : Continuous (fun q : Paper.Overlap=>(q,(sample.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal sample))) :=
    continuous_id.prodMk (continuous_const.prodMk hX)
  simpa only [Function.comp_def,vectorMeasureSpinMean] using
    (continuous_vectorMeasureGradient (n:=n) μ β t ht).comp hz

theorem measurable_stopped_vectorMeasureSpinMean (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (Q : Paper.Overlap) :
    @Measurable (Paper.Overlap×VectorDisorderBrownianSample n) (Field n)
      ((inferInstance : MeasurableSpace Paper.Overlap).prod (vectorBrownianFiltration n (Q:ℝ).toNNReal)) inferInstance
      (fun z=>vectorMeasureSpinMean μ β t ht (min z.1 Q) z.2) := by
  let m:=vectorBrownianFiltration n (Q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n):=m
  have hcont (sample : VectorDisorderBrownianSample n) :
      Continuous (fun q : Paper.Overlap=>vectorMeasureSpinMean μ β t ht (min q Q) sample) :=
    (continuous_vectorMeasureSpinMean_path μ β t ht sample).comp (continuous_id.min continuous_const)
  have hmeas (q : Paper.Overlap) :
      Measurable (fun sample : VectorDisorderBrownianSample n=>vectorMeasureSpinMean μ β t ht (min q Q) sample) := by
    exact (adapted_vectorMeasureSpinMean μ β t ht (min q Q)).mono
      ((vectorBrownianFiltration n).mono (Real.toNNReal_mono (show ((min q Q : Paper.Overlap):ℝ)≤(Q:ℝ)
        from min_le_right _ _))) le_rfl
  exact measurable_uncurry_of_continuous_of_measurable hcont hmeas

theorem adapted_vectorMeasureKernelMean (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (Q : Paper.Overlap)
    (hSupport : ∀ᵐq ∂parisiFreeMeasure μ s,κ q≠0→q≤Q) :
    StronglyMeasurable[vectorBrownianFiltration n (Q:ℝ).toNNReal]
      (vectorMeasureKernelMean (n:=n) μ s β t ht κ) := by
  let m:=vectorBrownianFiltration n (Q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n):=m
  have hM:=measurable_stopped_vectorMeasureSpinMean (n:=n) μ β t ht Q
  have hF : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      κ z.1 •vectorMeasureSpinMean μ β t ht (min z.1 Q) z.2) :=
    (hκ.comp measurable_fst).smul hM
  have hi := hF.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ s)
  have he : vectorMeasureKernelMean (n:=n) μ s β t ht κ=
      fun sample=>∫q,κ q •vectorMeasureSpinMean μ β t ht (min q Q) sample ∂parisiFreeMeasure μ s := by
    funext sample
    apply integral_congr_ae
    filter_upwards [hSupport] with q hq
    by_cases hz : κ q=0
    · simp only [hz,zero_smul]
    · rw [min_eq_left (hq hz)]
  rw [he]
  exact hi

theorem adapted_vectorMeasureKernelOffset (μ : Paper.ParisiMeasure) (s β t : ℝ)
    (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (Q : Paper.Overlap)
    (hSupport : ∀ᵐq ∂parisiFreeMeasure μ s,κ q≠0→q≤Q) :
    StronglyMeasurable[vectorBrownianFiltration n (Q:ℝ).toNNReal]
      (vectorMeasureKernelOffset (n:=n) μ s β t ht κ) := by
  let m:=vectorBrownianFiltration n (Q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n):=m
  have hM:=measurable_stopped_vectorMeasureSpinMean (n:=n) μ β t ht Q
  have hF : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      κ z.1*‖vectorMeasureSpinMean μ β t ht (min z.1 Q) z.2‖^2/2) :=
    ((hκ.comp measurable_fst).mul (hM.norm.pow_const 2)).div_const 2
  have hi := hF.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ s)
  have he : vectorMeasureKernelOffset (n:=n) μ s β t ht κ=
      fun sample=>∫q,κ q*‖vectorMeasureSpinMean μ β t ht (min q Q) sample‖^2/2 ∂parisiFreeMeasure μ s := by
    funext sample
    apply integral_congr_ae
    filter_upwards [hSupport] with q hq
    by_cases hz : κ q=0
    · simp only [hz,zero_mul,zero_div]
    · rw [min_eq_left (hq hz)]
  rw [he]
  exact hi

end QuantitativePaper
