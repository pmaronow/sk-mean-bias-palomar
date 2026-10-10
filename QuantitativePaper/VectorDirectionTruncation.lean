module
public import QuantitativePaper.VectorMeasureRandomReaction

@[expose] public section

/-! Bounded whole-past truncations of a square-integrable random direction.
The original vector is retained once its norm falls below the cutoff. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def truncateVectorDirection (b : VectorDisorderBrownianSample n→Field n)
    (k : ℕ) : VectorDisorderBrownianSample n→Field n :=
  {sample | ‖b sample‖≤(k:ℝ)}.indicator b

theorem measurable_truncateVectorDirection
    {m : MeasurableSpace (VectorDisorderBrownianSample n)}
    (b : VectorDisorderBrownianSample n→Field n) (hb : Measurable[m] b) (k : ℕ) :
    Measurable[m] (truncateVectorDirection b k) :=
  hb.indicator (measurableSet_le hb.norm measurable_const)

theorem norm_truncateVectorDirection_le (b : VectorDisorderBrownianSample n→Field n)
    (k : ℕ) (sample : VectorDisorderBrownianSample n) :
    ‖truncateVectorDirection b k sample‖≤(k:ℝ) := by
  by_cases h : ‖b sample‖≤(k:ℝ)
  · simpa [truncateVectorDirection,h] using h
  · simp [truncateVectorDirection,h]

theorem norm_truncateVectorDirection_le_original (b : VectorDisorderBrownianSample n→Field n)
    (k : ℕ) (sample : VectorDisorderBrownianSample n) :
    ‖truncateVectorDirection b k sample‖≤‖b sample‖ := by
  by_cases h : ‖b sample‖≤(k:ℝ)
  · simp [truncateVectorDirection,h]
  · simp [truncateVectorDirection,h]

theorem truncateVectorDirection_eventually_eq (b : VectorDisorderBrownianSample n→Field n)
    (sample : VectorDisorderBrownianSample n) :
    ∀ᶠ k : ℕ in atTop,truncateVectorDirection b k sample=b sample := by
  obtain ⟨k,hk⟩ := exists_nat_gt ‖b sample‖
  filter_upwards [eventually_ge_atTop k] with j hj
  apply indicator_of_mem (s:={sample | ‖b sample‖≤(j:ℝ)})
  exact hk.le.trans (Nat.cast_le.mpr hj)

theorem memLp_truncateVectorDirection (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (b : VectorDisorderBrownianSample n→Field n) (hbm : Measurable b)
    (hb : MemLp b 2 (vectorMeasureDisorderTilt μ β t a)) (k : ℕ) :
    MemLp (truncateVectorDirection b k) 2 (vectorMeasureDisorderTilt μ β t a) :=
  hb.of_le (measurable_truncateVectorDirection b hbm k).aestronglyMeasurable
    (.of_forall (norm_truncateVectorDirection_le_original b k))

theorem tendsto_integral_truncateVectorDirection_covariance
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n→Field n) (hbm : Measurable b)
    (hb : MemLp b 2 (vectorMeasureDisorderTilt μ β t a)) :
    Tendsto (fun k=>∫sample,vectorMeasureCovarianceQuadratic μ β t a ht q sample
      (truncateVectorDirection b k sample)∂vectorMeasureDisorderTilt μ β t a) atTop
      (𝓝 (∫sample,vectorMeasureCovarianceQuadratic μ β t a ht q sample (b sample)
        ∂vectorMeasureDisorderTilt μ β t a)) := by
  have hi : Integrable (fun sample=>‖b sample‖^2) (vectorMeasureDisorderTilt μ β t a) := by
    have hi := hb.norm.integrable_mul hb.norm
    change Integrable (fun sample=>‖b sample‖*‖b sample‖) _ at hi
    simpa only [pow_two] using hi
  apply tendsto_integral_of_dominated_convergence (fun sample=>2*(n:ℝ)^2*‖b sample‖^2)
  · intro k
    exact (integrable_vectorMeasureRandomCovariance μ β t a ht q _
      (memLp_truncateVectorDirection μ β t a b hbm hb k)).aestronglyMeasurable
  · exact hi.const_mul _
  · intro k
    filter_upwards [vectorMeasureCovarianceQuadratic_uniform_bound μ β t a ht q] with sample hs
    rw [Real.norm_eq_abs]
    exact (hs _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_truncateVectorDirection_le_original b k sample) 2)
      (by positivity))
  · exact .of_forall fun sample=>tendsto_const_nhds.congr'
      ((truncateVectorDirection_eventually_eq b sample).mono fun k hk=>by
        change vectorMeasureCovarianceQuadratic μ β t a ht q sample (b sample)=
          vectorMeasureCovarianceQuadratic μ β t a ht q sample (truncateVectorDirection b k sample)
        rw [hk])

end QuantitativePaper
