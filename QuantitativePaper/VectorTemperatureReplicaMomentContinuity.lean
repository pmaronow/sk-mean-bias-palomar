module
public import QuantitativePaper.VectorTemperatureCovarianceContinuity
public import QuantitativePaper.VectorDyadicUniformResponseDensity
public import QuantitativePaper.VectorConditionalReplicaMoments

@[expose] public section

/-! Continuity of the genuine conditional second-spin moments and mean
products. The second moment is evaluated using conditional expectation on
the fixed Wiener law, with the actual initial density paired afterwards. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology BigOperators RealInnerProductSpace
namespace QuantitativePaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem vectorMeasureConditionalPair_square_eq_base (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (i j : Fin n) :
    (∫ sample, (vectorMeasureSpinCovariance μ β t a ht q sample i j +
      vectorBaseMeanProduct μ β t ht q i j sample)^2
        ∂vectorMeasureDisorderTilt (n := n) μ β t a) =
      ∫ sample, vectorBaseOuterWeight μ β t a sample *
        ((vectorDisorderBrownianMeasure n)[vectorBasePairObservable μ β t ht i j |
          vectorBrownianFiltration n (q : ℝ).toNNReal] sample)^2
        ∂vectorDisorderBrownianMeasure n := by
  have he := vectorMeasureTerminalObservable_condExp_eq_base (n := n) μ β t a ht q
    (fun σ => Paper.spinSign (σ i) * Paper.spinSign (σ j))
  have hh : (∫ sample, (vectorMeasureSpinCovariance μ β t a ht q sample i j +
      vectorBaseMeanProduct μ β t ht q i j sample)^2
        ∂vectorMeasureDisorderTilt (n := n) μ β t a) =
      ∫ sample, ((vectorDisorderBrownianMeasure n)[vectorBasePairObservable μ β t ht i j |
        vectorBrownianFiltration n (q : ℝ).toNNReal] sample)^2
        ∂vectorMeasureDisorderTilt μ β t a := by
    apply integral_congr_ae
    filter_upwards [he] with sample hs
    simp only [vectorMeasureSpinCovariance, vectorBasePairObservable,
      vectorBaseMeanProduct, hs, sub_add_cancel]
  rw [hh, integral_vectorMeasureDisorderTilt_eq_weighted μ β t a ht]
  rfl

theorem continuous_integral_vectorMeasureConditionalPair_square_temperature
    (μ : Paper.ParisiMeasure) (β a : ℝ) (q : Paper.Overlap) (i j : Fin n) :
    Continuous (fun t : Iio (1 : ℝ) => ∫ sample,
      (vectorMeasureSpinCovariance μ β t a t.property.le q sample i j +
        vectorBaseMeanProduct μ β t t.property.le q i j sample)^2
        ∂vectorMeasureDisorderTilt (n := n) μ β t a) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  change Tendsto _ (𝓝 t) (𝓝 _)
  simp_rw [vectorMeasureConditionalPair_square_eq_base]
  have hz : MemLp (fun _ : VectorDisorderBrownianSample n => (0 : ℝ)) 2
      (vectorDisorderBrownianMeasure n) := memLp_const 0
  have hzero : Tendsto (fun _ : Iio (1 : ℝ) => hz.toLp (fun _ => (0 : ℝ)))
      (𝓝 t) (𝓝 (hz.toLp (fun _ => (0 : ℝ)))) := tendsto_const_nhds
  have h := tendsto_weighted_conditional_covariance_square
    (vectorBrownianFiltration n (q : ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
    (fun u : Iio (1 : ℝ) => vectorBasePairObservable μ β u u.property.le i j)
    (fun _ _ => 0) (fun u => vectorBaseOuterWeight μ β u a)
    (vectorBasePairObservable μ β t t.property.le i j) (fun _ => 0)
    (vectorBaseOuterWeight μ β t a)
    (fun u => memLp_vectorBasePairObservable μ β u u.property.le i j)
    (fun _ => hz) (fun u => memLp_vectorBaseOuterWeight μ β u a u.property.le)
    (memLp_vectorBasePairObservable μ β t t.property.le i j) hz
    (memLp_vectorBaseOuterWeight μ β t a t.property.le)
    ((continuous_vectorTemperaturePairObservableL2 μ β i j).tendsto t)
    hzero ((continuous_vectorTemperatureOuterWeightL2 μ β a).tendsto t)
    (fun u => .of_forall (vectorBasePairObservable_bound μ β u u.property.le i j))
    (fun _ => .of_forall fun _ => by simp)
    (.of_forall (vectorBasePairObservable_bound μ β t t.property.le i j))
    (.of_forall fun _ => by simp)
  simpa only [sub_zero] using h

theorem continuous_integral_vectorBaseMeanProduct_temperature
    (μ : Paper.ParisiMeasure) (β a : ℝ) (q : Paper.Overlap) (i j : Fin n) :
    Continuous (fun t : Iio (1 : ℝ) => ∫ sample,
      vectorBaseMeanProduct μ β t t.property.le q i j sample
        ∂vectorMeasureDisorderTilt (n := n) μ β t a) := by
  have hc : Continuous (fun t : Iio (1 : ℝ) => inner ℝ
      (vectorTemperatureOuterWeightL2 μ β a t)
      (vectorTemperatureMeanProductL2 μ β q i j t)) :=
    (continuous_vectorTemperatureOuterWeightL2 μ β a).inner
      (continuous_vectorTemperatureMeanProductL2 μ β q i j)
  have he (t : Iio (1 : ℝ)) : (inner ℝ (vectorTemperatureOuterWeightL2 μ β a t)
      (vectorTemperatureMeanProductL2 μ β q i j t)) =
      ∫ sample, vectorBaseMeanProduct μ β t t.property.le q i j sample
        ∂vectorMeasureDisorderTilt (n := n) μ β t a := by
    rw [L2.inner_def, integral_vectorMeasureDisorderTilt_eq_weighted μ β t a t.property.le]
    simp only [RCLike.inner_apply, conj_trivial]
    apply integral_congr_ae
    filter_upwards [(memLp_vectorBaseOuterWeight (n := n) μ β t a t.property.le).coeFn_toLp,
      (memLp_vectorBaseMeanProduct (n := n) μ β t t.property.le q i j).coeFn_toLp] with sample hw hg
    change _ = vectorBaseOuterWeight μ β t a sample * _
    change (vectorTemperatureMeanProductL2 μ β q i j t) sample *
      (vectorTemperatureOuterWeightL2 μ β a t) sample = _
    rw [show (vectorTemperatureMeanProductL2 μ β q i j t) sample =
      vectorBaseMeanProduct μ β t t.property.le q i j sample from hg,
      show (vectorTemperatureOuterWeightL2 μ β a t) sample =
      vectorBaseOuterWeight μ β t a sample from hw]
    exact mul_comm _ _
  simpa only [he] using hc

theorem integrable_vectorMeasureConditionalPair_square (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (i j : Fin n) :
    Integrable (fun sample => (vectorMeasureSpinCovariance μ β t a ht q sample i j +
      vectorBaseMeanProduct μ β t ht q i j sample)^2)
      (vectorMeasureDisorderTilt (n := n) μ β t a) := by
  letI := vectorMeasureDisorderTilt_probability (n := n) μ β t a ht
  have hmi : Measurable (fun sample : VectorDisorderBrownianSample n =>
      vectorMeasureSpinMean μ β t ht q sample i) :=
    (adapted_vectorMeasureSpinMean_component μ β t ht q i).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  have hmj : Measurable (fun sample : VectorDisorderBrownianSample n =>
      vectorMeasureSpinMean μ β t ht q sample j) :=
    (adapted_vectorMeasureSpinMean_component μ β t ht q j).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  apply (integrable_const (9 : ℝ)).mono'
    (((measurable_vectorMeasureSpinCovariance_entry μ β t a ht q i j).add
      (hmi.mul hmj)).pow_const 2).aestronglyMeasurable
  filter_upwards [vectorMeasureSpinCovariance_entry_bound (n := n) μ β t a ht q]
    with sample hs
  have hb := vectorBaseMeanProduct_bound μ β t ht q i j sample
  rw [Real.norm_eq_abs] at hb
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (vectorMeasureSpinCovariance μ β t a ht q sample i j +
    vectorBaseMeanProduct μ β t ht q i j sample)^2 ≤ 9
  have hsum := (abs_add_le _ _).trans (add_le_add (hs i j) hb)
  nlinarith [abs_le.mp hsum]

end QuantitativePaper
