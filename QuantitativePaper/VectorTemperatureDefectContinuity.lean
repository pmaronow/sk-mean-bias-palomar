module
public import QuantitativePaper.VectorTemperatureReplicaMomentContinuity
public import QuantitativePaper.VectorInterpolationDefect

@[expose] public section

/-! The actual conditional two-replica defect is continuous in physical
interpolation time. Its overlap integral uses the fixed genuine free
measure, and the conditional-replica bound supplies dominated convergence. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem vectorConditionalReplicaDefect_eq_second_moment_integrals (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1)
    (q : Paper.Overlap) :
    vectorConditionalReplicaDefect (n := n) μ β t a ht.le q =
      (1 / (n : ℝ))^2 * ∑ i : Fin n, ∑ j : Fin n,
        ∫ sample, (vectorMeasureSpinCovariance μ β t a ht.le q sample i j +
          vectorBaseMeanProduct μ β t ht.le q i j sample)^2
          ∂vectorMeasureDisorderTilt μ β t a -
      2 * (q : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n,
        ∫ sample, vectorBaseMeanProduct μ β t ht.le q i i sample
          ∂vectorMeasureDisorderTilt μ β t a) + (q : ℝ)^2 := by
  let P := vectorMeasureDisorderTilt (n := n) μ β t a
  letI := vectorMeasureDisorderTilt_probability (n := n) μ β t a ht.le
  have hM (i : Fin n) : Measurable (fun sample : VectorDisorderBrownianSample n =>
      vectorMeasureSpinMean μ β t ht.le q sample i) :=
    (adapted_vectorMeasureSpinMean_component μ β t ht.le q i).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  have hB (i j : Fin n) : Measurable (fun sample : VectorDisorderBrownianSample n =>
      (vectorMeasureSpinCovariance μ β t a ht.le q sample i j +
        vectorBaseMeanProduct μ β t ht.le q i j sample)^2) :=
    ((measurable_vectorMeasureSpinCovariance_entry μ β t a ht.le q i j).add
      ((hM i).mul (hM j))).pow_const 2
  have hF : Measurable (vectorConditionalReplicaMatrixDefect (n := n) μ β t a ht.le q) := by
    unfold vectorConditionalReplicaMatrixDefect
    exact ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => hB i j)).sub
      (measurable_const.mul (measurable_const.mul
        (Finset.measurable_sum _ fun i _ => (hM i).pow_const 2)))).add measurable_const
  have hBi (i j : Fin n) : Integrable (fun sample : VectorDisorderBrownianSample n =>
      (vectorMeasureSpinCovariance μ β t a ht.le q sample i j +
        vectorBaseMeanProduct μ β t ht.le q i j sample)^2) P :=
    integrable_vectorMeasureConditionalPair_square μ β t a ht.le q i j
  have hMi (i : Fin n) : Integrable
      (vectorBaseMeanProduct μ β t ht.le q i i) P := by
    apply (integrable_const (1 : ℝ)).mono' ((hM i).mul (hM i)).aestronglyMeasurable
    exact .of_forall (vectorBaseMeanProduct_bound μ β t ht.le q i i)
  have hBs := integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hBi i j
  have hMs := integrable_finsetSum Finset.univ fun i _ => hMi i
  rw [vectorConditionalReplicaDefect_eq_matrix_integral hn μ β t a hβ ht q,
    integral_vectorMeasureSpinPathLaw_sample μ β t a ht.le _ hF]
  have hpoint (sample : VectorDisorderBrownianSample n) :
      vectorConditionalReplicaMatrixDefect μ β t a ht.le q sample =
      (1 / (n : ℝ))^2 * (∑ i : Fin n, ∑ j : Fin n,
        (vectorMeasureSpinCovariance μ β t a ht.le q sample i j +
          vectorBaseMeanProduct μ β t ht.le q i j sample)^2) -
        (2 * (q : ℝ) * (1 / (n : ℝ))) *
          (∑ i : Fin n, vectorBaseMeanProduct μ β t ht.le q i i sample) + (q : ℝ)^2 := by
    unfold vectorConditionalReplicaMatrixDefect vectorBaseMeanProduct
    simp only [pow_two]
    ring
  simp_rw [hpoint]
  change (∫ sample, (1 / (n : ℝ))^2 * (∑ i : Fin n, ∑ j : Fin n,
      (vectorMeasureSpinCovariance μ β t a ht.le q sample i j +
        vectorBaseMeanProduct μ β t ht.le q i j sample)^2) -
      (2 * (q : ℝ) * (1 / (n : ℝ))) *
        (∑ i : Fin n, vectorBaseMeanProduct μ β t ht.le q i i sample) +
      (q : ℝ)^2 ∂P) = _
  have hadd := integral_add
    ((hBs.const_mul ((1 / (n : ℝ))^2)).sub
      (hMs.const_mul (2 * (q : ℝ) * (1 / (n : ℝ)))))
    (integrable_const ((q : ℝ)^2) : Integrable (fun _ : VectorDisorderBrownianSample n => (q : ℝ)^2) P)
  have hsub := integral_sub (hBs.const_mul ((1 / (n : ℝ))^2))
    (hMs.const_mul (2 * (q : ℝ) * (1 / (n : ℝ))))
  simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul,
    integral_const_mul, integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ fun j _ => hBi i j),
    integral_finsetSum _ (fun i _ => hMi i)]
  simp_rw [integral_finsetSum _ (fun j _ => hBi _ j)]
  simp only [integral_const, probReal_univ, one_smul]
  ring

theorem continuous_vectorConditionalReplicaDefect_temperature (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β a : ℝ) (hβ : β ≠ 0) (q : Paper.Overlap) :
    Continuous (fun t : Iio (1 : ℝ) =>
      vectorConditionalReplicaDefect (n := n) μ β t a t.property.le q) := by
  have hc : Continuous (fun t : Iio (1 : ℝ) =>
      (1 / (n : ℝ))^2 * ∑ i : Fin n, ∑ j : Fin n,
        ∫ sample, (vectorMeasureSpinCovariance μ β t a t.property.le q sample i j +
          vectorBaseMeanProduct μ β t t.property.le q i j sample)^2
          ∂vectorMeasureDisorderTilt μ β t a -
      2 * (q : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n,
        ∫ sample, vectorBaseMeanProduct μ β t t.property.le q i i sample
          ∂vectorMeasureDisorderTilt μ β t a) + (q : ℝ)^2) :=
    ((continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ =>
      continuous_integral_vectorMeasureConditionalPair_square_temperature μ β a q i j)).sub
    (continuous_const.mul (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_integral_vectorBaseMeanProduct_temperature μ β a q i i)))).add continuous_const
  exact hc.congr fun t =>
    (vectorConditionalReplicaDefect_eq_second_moment_integrals hn μ β t a hβ t.property q).symm

theorem continuous_vectorInterpolationDefect_temperature (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (s β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun t : Iio (1 : ℝ) =>
      vectorInterpolationDefect (n := n) μ s β t t.property.le) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ))
    (.of_forall fun u => (integrable_vectorInterpolationDefect hn μ s β u hβ u.property).aestronglyMeasurable)
    (.of_forall fun u => .of_forall fun q => by
      rw [Real.norm_of_nonneg (vectorConditionalReplicaDefect_bounds hn μ β u s u.property.le q).1]
      exact (vectorConditionalReplicaDefect_bounds hn μ β u s u.property.le q).2)
    (integrable_const (4 : ℝ))
    (.of_forall fun q => (continuous_vectorConditionalReplicaDefect_temperature hn μ β s hβ q).tendsto t)

end QuantitativePaper
