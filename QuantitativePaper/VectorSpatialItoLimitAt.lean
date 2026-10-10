module
public import QuantitativePaper.VectorShiftedGaussianMoments
public import QuantitativePaper.VectorItoPartitionAt

@[expose] public section

/-! Spatial Itô expectation limit proved from the constructed Wiener law,
literal bounded-drift Riemann sums, and vanishing Taylor errors. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
variable {a : ℝ≥0}
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem tendsto_integral_vectorSpatialIncrementApproxAt
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristicsAt a X d σ)
    {f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ}
    (hf : VectorSpatialItoTestAt a f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (t : ℝ≥0) :
    Tendsto (fun N=>∫ sample,vectorSpatialIncrementApproxAt f X Z t (N+1) sample
      ∂vectorDisorderBrownianMeasure n) atTop
      (𝓝 ((∫ sample,Z sample*(∫ s in Ioc 0 t,fderiv ℝ (f s sample) (X s sample)
          (d s sample) ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n)+
        σ^2/2*(∫ sample,(∫ s in Ioc 0 t,Z sample*vectorBilinearTrace
          (vectorHessian (f s sample) (X s sample)) ∂nonnegativeLebesgueMeasure)
          ∂vectorDisorderBrownianMeasure n))) := by
  obtain ⟨D,hD⟩ := hc.bounded_drift
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltrationAt n a).le 0) le_rfl
  have hw (s : ℝ≥0) : StronglyMeasurable
      (fun sample=>fderiv ℝ (f s sample) (X s sample)) :=
    ((hf.adapted_first s s).mono ((vectorBrownianFiltrationAt n a).le s) le_rfl).stronglyMeasurable
  have hdlim := tendsto_integral_vectorWeightedDriftApprox (vectorDisorderBrownianMeasure n)
    d hc.measurable_drift D hD (fun s sample=>fderiv ℝ (f s sample) (X s sample)) hw
    hf.continuous_first_path hf.firstBound t (fun s _ sample=>hf.first_le s sample _)
    Z hZg.stronglyMeasurable C hC
  have htrace (s : ℝ≥0) : StronglyMeasurable (fun sample=>Z sample*vectorBilinearTrace
      (vectorHessian (f s sample) (X s sample))) := by
    have hm := ((hf.adapted_second s s).mono ((vectorBrownianFiltrationAt n a).le s) le_rfl).stronglyMeasurable
    apply hZg.stronglyMeasurable.mul
    exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _=>
      (show Continuous (fun H : Field n →L[ℝ] Field n →L[ℝ] ℝ=>
          H (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) from by fun_prop).comp_stronglyMeasurable hm)
  have htracec (sample : VectorDisorderBrownianSample n) : Continuous
      (fun s=>Z sample*vectorBilinearTrace (vectorHessian (f s sample) (X s sample))) :=
    continuous_const.mul (hf.continuous_trace_path sample)
  have htraceb (s : ℝ≥0) (_ : s∈Icc 0 t) (sample : VectorDisorderBrownianSample n) :
      |Z sample*vectorBilinearTrace (vectorHessian (f s sample) (X s sample))| ≤
        (C*(n : ℝ≥0)*hf.secondBound : ℝ≥0) := by
    rw [abs_mul]
    have hz : |Z sample| ≤ C := by simpa only [Real.norm_eq_abs] using hC sample
    have hh := mul_le_mul hz (hf.trace_bound s sample) (abs_nonneg _) C.coe_nonneg
    simpa only [NNReal.coe_mul,NNReal.coe_natCast,mul_assoc] using hh
  have hqlim := (tendsto_integral_boundedPartitionLeftSum (vectorDisorderBrownianMeasure n)
    (fun s sample=>Z sample*vectorBilinearTrace (vectorHessian (f s sample) (X s sample)))
    htrace htracec (C*(n : ℝ≥0)*hf.secondBound) t htraceb).const_mul (σ^2/2)
  have hR (r s : ℝ≥0) (_ : r ≤ s) : AEStronglyMeasurable
      (fun sample=>Z sample*vectorSpatialTaylorError (f r) (X r)
        (fun sample=>σ • disorderVectorBrownianIncrementAt a r s sample)
        (fun sample=>vectorIntegratedDrift (fun q=>d q sample) s-
          vectorIntegratedDrift (fun q=>d q sample) r) sample)
      (vectorDisorderBrownianMeasure n) :=
    (hZg.mul (measurable_vectorSpatialTaylorErrorAt hc (hf.slice r) r s)).aestronglyMeasurable
  have hrlim := tendsto_integral_vectorSpatialTaylorApproxAt f hf.regularity hf.secondBound
    hf.thirdBound D hf.second_le hf.third_le X d hc.measurable_drift hD σ Z C hC hR t
  have hsum := (hdlim.add hqlim).add hrlim
  simp only [add_zero] at hsum
  convert hsum using 1
  funext N
  exact (vector_spatial_partition_expectationAt hc hf Z hZ C hC t (Nat.succ_pos N)).2

end QuantitativePaper
