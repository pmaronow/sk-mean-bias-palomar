module
public import QuantitativePaper.VectorShiftedGaussianMoments
public import QuantitativePaper.VectorSpatialItoTestAt
public import QuantitativePaper.VectorTaylorPartitionAt

@[expose] public section

/-! Exact finite partition expectation identity for the actual vector
Wiener state. The drift and quadratic terms are the literal Riemann sums,
and every summand is proved integrable from analytic derivative bounds. -/
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

def vectorSpatialIncrementApproxAt
    (f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ)
    (X : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (Z : VectorDisorderBrownianSample n → ℝ) (t : ℝ≥0) (N : ℕ)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∑ j∈Finset.range N,Z sample*(f (uniformPartitionTime t N j) sample
    (X (uniformPartitionTime t N (j+1)) sample)-
    f (uniformPartitionTime t N j) sample (X (uniformPartitionTime t N j) sample))

theorem integrable_vector_weighted_traceAt
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTestAt a f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (r : ℝ≥0) :
    Integrable (fun sample=>Z sample*vectorBilinearTrace
      (vectorHessian (f sample) (X r sample))) (vectorDisorderBrownianMeasure n) := by
  have hi := integrable_weightedVectorSecondAt hf Z hZ C hC r
  have hs := integrable_finsetSum Finset.univ (fun (i : Fin n) _=>
    (hi.apply_continuousLinearMap (EuclideanSpace.single i 1)).apply_continuousLinearMap
      (EuclideanSpace.single i 1))
  simpa only [vectorBilinearTrace,weightedVectorSecond,ContinuousLinearMap.smul_apply,
    smul_eq_mul,Finset.mul_sum] using hs

theorem integrable_vector_weighted_drift_cellAt
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristicsAt a X d σ)
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    (hf : VectorStaticItoTestAt a f X) (r t : ℝ≥0) (hrt : r ≤ t)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) :
    Integrable (fun sample=>Z sample*fderiv ℝ (f sample) (X r sample)
      (vectorIntegratedDrift (fun s=>d s sample) t-
        vectorIntegratedDrift (fun s=>d s sample) r)) (vectorDisorderBrownianMeasure n) := by
  obtain ⟨D,hD⟩ := hc.bounded_drift
  have hm := (show Measurable (fun p : (Field n →L[ℝ] ℝ) × Field n=>p.1 p.2) from by fun_prop).comp
    (((hf.adapted_first r).mono ((vectorBrownianFiltrationAt n a).le r) le_rfl).prodMk
      ((stronglyMeasurable_vectorIntegratedDrift d hc.measurable_drift t).measurable.sub
        (stronglyMeasurable_vectorIntegratedDrift d hc.measurable_drift r).measurable))
  apply (integrable_const ((C : ℝ)*hf.firstBound*D*((t : ℝ)-r))).mono'
    (((hZ.mono ((vectorBrownianFiltrationAt n a).le 0) le_rfl).mul hm).aestronglyMeasurable)
  apply Eventually.of_forall
  intro sample
  have hv := vectorIntegratedDrift_increment_bound (fun s=>d s sample)
    (hc.measurable_drift.comp (measurable_id.prodMk measurable_const)) D
    (fun s=>hD s sample) hrt
  have hg := (fderiv ℝ (f sample) (X r sample)).le_opNorm
    (vectorIntegratedDrift (fun s=>d s sample) t-vectorIntegratedDrift (fun s=>d s sample) r)
  change ‖Z sample*fderiv ℝ (f sample) (X r sample)
    (vectorIntegratedDrift (fun s=>d s sample) t-vectorIntegratedDrift (fun s=>d s sample) r)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (C : ℝ)*(‖fderiv ℝ (f sample) (X r sample)‖*
        ‖vectorIntegratedDrift (fun s=>d s sample) t-vectorIntegratedDrift (fun s=>d s sample) r‖) :=
      mul_le_mul (hC sample) hg (norm_nonneg _) C.coe_nonneg
    _ ≤ (C : ℝ)*(hf.firstBound*(D*((t : ℝ)-r))) := mul_le_mul_of_nonneg_left
      (mul_le_mul (hf.first_le sample _) hv (norm_nonneg _) hf.firstBound.coe_nonneg) C.coe_nonneg
    _ = _ := by ring

theorem vector_spatial_partition_expectationAt
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristicsAt a X d σ)
    {f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ}
    (hf : VectorSpatialItoTestAt a f X) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltrationAt n a 0] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C) (t : ℝ≥0) {N : ℕ} (hN : 0 < N) :
    Integrable (vectorSpatialIncrementApproxAt f X Z t N) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,vectorSpatialIncrementApproxAt f X Z t N sample ∂vectorDisorderBrownianMeasure n)=
      (∫ sample,Z sample*vectorWeightedDriftApprox (fun s=>d s sample)
        (fun s=>fderiv ℝ (f s sample) (X s sample)) t N ∂vectorDisorderBrownianMeasure n)+
      σ^2/2*(∫ sample,boundedPartitionLeftSum (fun s=>Z sample*vectorBilinearTrace
        (vectorHessian (f s sample) (X s sample))) t N ∂vectorDisorderBrownianMeasure n)+
      (∫ sample,vectorSpatialTaylorApproxAt (a:=a) f X d σ Z t N sample ∂vectorDisorderBrownianMeasure n) := by
  let r := fun j=>uniformPartitionTime t N j
  have hrt (j : ℕ) : r j ≤ r (j+1) := monotone_uniformPartitionTime t N (Nat.le_add_right j 1)
  have hlen (j : ℕ) : ((r (j+1) : ℝ≥0) : ℝ)-(r j : ℝ)=(t : ℝ)/(N : ℝ) := by
    have hh := dist_uniformPartitionTime_succ_eq t hN j
    rw [NNReal.dist_eq,abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hrt j)))] at hh
    simpa only [NNReal.coe_div,NNReal.coe_natCast] using hh
  have hs (j : ℕ) := vector_ito_step_expectationAt hc (hf.slice (r j)) (r j) (r (j+1))
    (hrt j) Z hZ C hC
  have ha (j : ℕ) := integrable_vector_weighted_drift_cellAt hc (hf.slice (r j))
    (r j) (r (j+1)) (hrt j) Z hZ C hC
  have hq (j : ℕ) := integrable_vector_weighted_traceAt (hf.slice (r j)) Z hZ C hC (r j)
  obtain ⟨D,hD⟩ := hc.bounded_drift
  have hr (j : ℕ) := (integral_weighted_vectorSpatialTaylorError_boundAt a (r j) (r (j+1))
    (hrt j) σ (f (r j)) (hf.regularity _) hf.secondBound hf.thirdBound D
    (hf.second_le _) (hf.third_le _) (X (r j))
    (fun sample=>vectorIntegratedDrift (fun s=>d s sample) (r (j+1))-
      vectorIntegratedDrift (fun s=>d s sample) (r j))
    (fun sample=>vectorIntegratedDrift_increment_bound _
      (hc.measurable_drift.comp (measurable_id.prodMk measurable_const)) D
      (fun s=>hD s sample) (hrt j)) Z C hC
    (((hZ.mono ((vectorBrownianFiltrationAt n a).le 0) le_rfl).mul
      (measurable_vectorSpatialTaylorErrorAt hc (hf.slice (r j)) (r j) (r (j+1)))).aestronglyMeasurable)).1
  refine ⟨integrable_finsetSum (Finset.range N) (fun j _=>(hs j).1),?_⟩
  have heD : (fun sample=>Z sample*vectorWeightedDriftApprox (fun s=>d s sample)
      (fun s=>fderiv ℝ (f s sample) (X s sample)) t N)=
      (fun sample=>∑ j∈Finset.range N,Z sample*fderiv ℝ (f (r j) sample) (X (r j) sample)
        (vectorIntegratedDrift (fun s=>d s sample) (r (j+1))-
          vectorIntegratedDrift (fun s=>d s sample) (r j))) := by
    funext sample
    simp only [vectorWeightedDriftApprox,Finset.mul_sum,r]
  change (∫ sample,∑ j∈Finset.range N,Z sample*(f (r j) sample (X (r (j+1)) sample)-
    f (r j) sample (X (r j) sample)) ∂vectorDisorderBrownianMeasure n)=_
  rw [integral_finsetSum _ (fun j _=>(hs j).1),heD,
    integral_finsetSum _ (fun j _=>ha j)]
  unfold boundedPartitionLeftSum vectorSpatialTaylorApproxAt
  rw [integral_finsetSum _ (fun j _=>(hq j).mul_const ((t : ℝ)/(N : ℝ))),
    integral_finsetSum _ (fun j _=>hr j)]
  rw [Finset.mul_sum]
  simp_rw [(hs _).2,hlen,integral_mul_const]
  simp only [Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  ring

end QuantitativePaper
