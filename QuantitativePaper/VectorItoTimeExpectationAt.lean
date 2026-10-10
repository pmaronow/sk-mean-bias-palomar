module
public import QuantitativePaper.VectorShiftedGaussianMoments
public import QuantitativePaper.VectorSpatialItoLimitAt
public import QuantitativePaper.VectorItoIncrementBoundsAt
public import FourPapersCommon.TimeFTCLimit

@[expose] public section

/-! The time-dependent Itô expectation identity. Its finite telescope,
spatial Gaussian cancellation, Taylor limits, and time fundamental theorem
are proved here and in the imported modules. No stochastic identity is an
input to this theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
variable {a : ℝ≥0}
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ} {T : ℝ≥0}

theorem vector_time_spatial_partition_telescopeAt
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (X : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (Z : VectorDisorderBrownianSample n → ℝ) {N : ℕ} (hN : 0 < N)
    (sample : VectorDisorderBrownianSample n) :
    Z sample*(test.f T sample (X T sample)-test.f 0 sample (X 0 sample))=
      vectorSpatialIncrementApproxAt (fun q=>test.f q) X Z T N sample+
      timeRightPartitionSum test X Z N sample := by
  let r : ℕ → ℝ≥0 := uniformPartitionTime T N
  let g : ℕ → ℝ := fun j=>Z sample*test.f (r j) sample (X (r j) sample)
  have hr0 : r 0=0 := by simp [r,uniformPartitionTime]
  have hrN : r N=T := by simp [r,uniformPartitionTime,ne_of_gt hN]
  calc
    _ = g N-g 0 := by dsimp only [g];rw [hrN,hr0];simp only [NNReal.coe_zero];ring
    _ = ∑ j∈Finset.range N,(g (j+1)-g j) := (Finset.sum_range_sub g N).symm
    _ = ∑ j∈Finset.range N,
        (Z sample*(test.f (r j) sample (X (r (j+1)) sample)-
          test.f (r j) sample (X (r j) sample))+
        Z sample*(test.f (r (j+1)) sample (X (r (j+1)) sample)-
          test.f (r j) sample (X (r (j+1)) sample))) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [g]
      ring
    _ = _ := Finset.sum_add_distrib

theorem vector_ito_time_expectation_of_increment_boundAt
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristicsAt a X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (hf : VectorSpatialItoTestAt a (fun q=>test.f q) X)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (A D : ℝ≥0)
    (hi : ∀ r t : ℝ≥0,r ≤ t → t ≤ T →
      Integrable (fun sample=>‖X t sample-X r sample‖) (vectorDisorderBrownianMeasure n))
    (hinc : ∀ r t : ℝ≥0,r ≤ t → t ≤ T →
      (∫ sample,‖X t sample-X r sample‖ ∂vectorDisorderBrownianMeasure n) ≤
        A*Real.sqrt ((t : ℝ)-r)+D*((t : ℝ)-r)) :
    Integrable (fun sample=>Z sample*(test.f T sample (X T sample)-
      test.f 0 sample (X 0 sample))) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(test.f T sample (X T sample)-test.f 0 sample (X 0 sample))
      ∂vectorDisorderBrownianMeasure n)=
      (∫ sample,Z sample*(∫ s in Ioc 0 T,fderiv ℝ (test.f s sample) (X s sample)
        (d s sample) ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n)+
      σ^2/2*(∫ sample,(∫ s in Ioc 0 T,Z sample*vectorBilinearTrace
        (vectorHessian (test.f s sample) (X s sample)) ∂nonnegativeLebesgueMeasure)
        ∂vectorDisorderBrownianMeasure n)+
      (∫ sample,timeFTCIntegral test X Z sample ∂vectorDisorderBrownianMeasure n) := by
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltrationAt n a).le 0) le_rfl
  have hsp (N : ℕ) := vector_spatial_partition_expectationAt hc hf Z hZ C hC T (Nat.succ_pos N)
  have hti (N : ℕ) := (timeRightPartitionSum_expectation_error_bound
    (vectorDisorderBrownianMeasure n) test X hc.measurable_state Z hZg C hC A D hi hinc
    (Nat.succ_pos N)).1
  have he (N : ℕ) : (fun sample=>Z sample*(test.f T sample (X T sample)-
      test.f 0 sample (X 0 sample)))=
      (fun sample=>vectorSpatialIncrementApproxAt (fun q=>test.f q) X Z T (N+1) sample+
        timeRightPartitionSum test X Z (N+1) sample) :=
    funext (vector_time_spatial_partition_telescopeAt test X Z (Nat.succ_pos N))
  have hEi := ((hsp 0).1.add (hti 0)).congr (Eventually.of_forall fun sample=>
    (congrFun (he 0) sample).symm)
  refine ⟨hEi,?_⟩
  have hspatial := tendsto_integral_vectorSpatialIncrementApproxAt hc hf Z hZ C hC T
  have htime := tendsto_integral_timeRightPartitionSum (vectorDisorderBrownianMeasure n)
    test X hc.measurable_state Z hZg C hC A D hi hinc
  have hsum := hspatial.add htime
  have hconstant : Tendsto (fun _ : ℕ=>∫ sample,Z sample*(test.f T sample (X T sample)-
      test.f 0 sample (X 0 sample)) ∂vectorDisorderBrownianMeasure n) atTop
      (𝓝 ((∫ sample,Z sample*(∫ s in Ioc 0 T,fderiv ℝ (test.f s sample) (X s sample)
          (d s sample) ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n)+
        σ^2/2*(∫ sample,(∫ s in Ioc 0 T,Z sample*vectorBilinearTrace
          (vectorHessian (test.f s sample) (X s sample)) ∂nonnegativeLebesgueMeasure)
          ∂vectorDisorderBrownianMeasure n)+
        (∫ sample,timeFTCIntegral test X Z sample ∂vectorDisorderBrownianMeasure n))) := by
    convert hsum using 1
    funext N
    rw [he N,integral_add (hsp N).1 (hti N)]
  exact tendsto_nhds_unique tendsto_const_nhds hconstant

theorem vector_ito_time_expectationAt
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristicsAt a X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (hf : VectorSpatialItoTestAt a (fun q=>test.f q) X)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) :
    Integrable (fun sample=>Z sample*(test.f T sample (X T sample)-
      test.f 0 sample (X 0 sample))) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(test.f T sample (X T sample)-test.f 0 sample (X 0 sample))
      ∂vectorDisorderBrownianMeasure n)=
      (∫ sample,Z sample*(∫ s in Ioc 0 T,fderiv ℝ (test.f s sample) (X s sample)
        (d s sample) ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n)+
      σ^2/2*(∫ sample,(∫ s in Ioc 0 T,Z sample*vectorBilinearTrace
        (vectorHessian (test.f s sample) (X s sample)) ∂nonnegativeLebesgueMeasure)
        ∂vectorDisorderBrownianMeasure n)+
      (∫ sample,timeFTCIntegral test X Z sample ∂vectorDisorderBrownianMeasure n) := by
  obtain ⟨D,hD⟩ := hc.bounded_drift
  let A : ℝ≥0 := ⟨|σ| * vectorGaussianNormMoment n 1,
    mul_nonneg (abs_nonneg _) (vectorGaussianNormMoment_nonneg n 1)⟩
  exact vector_ito_time_expectation_of_increment_boundAt hc test hf Z hZ C hC A D
    (fun r t hrt _=>hc.integrable_increment_norm r t hrt)
    (fun r t hrt _=>hc.integral_norm_increment_le D hD r t hrt)

end QuantitativePaper
