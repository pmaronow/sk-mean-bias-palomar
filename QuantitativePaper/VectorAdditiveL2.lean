module
public import QuantitativePaper.VectorAdditiveBounds
public import QuantitativePaper.VectorAdditiveUniqueness
public import FourPapersCommon.VectorGaussianMoments

@[expose] public section

/-! Genuine square increment bounds and drift adaptation for the actual
constructed vector diffusion. -/
noncomputable section
open FourPapersCommon Function MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1500000
variable {n : ℕ}

theorem stronglyAdapted_vectorAdditiveDrift (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T : ℝ≥0) :
    StronglyAdapted (vectorBrownianFiltration n) (vectorAdditiveDrift d σ x0 T) := by
  intro r
  letI : MeasurableSpace (VectorDisorderBrownianSample n) := vectorBrownianFiltration n r
  by_cases hr : r ≤ T
  · change StronglyMeasurable (fun sample =>
      if r ≤ T then d.drift r sample.1 (vectorAdditiveState d σ x0 T r sample) else 0)
    simp only [ite_eq_left hr]
    exact (d.measurable.comp (measurable_const.prodMk
      ((stronglyMeasurable_initialVectorDisorder n r).measurable.prodMk
        (stronglyAdapted_vectorAdditiveState d σ x0 T r).measurable))).stronglyMeasurable
  · change StronglyMeasurable (fun sample =>
      if r ≤ T then d.drift r sample.1 (vectorAdditiveState d σ x0 T r sample) else 0)
    simp only [ite_eq_right hr]
    exact stronglyMeasurable_const

theorem integral_square_vectorAdditiveState_increment_le
    (d : VectorAdditiveDriftData n) (σ : ℝ) (x0 : Field n)
    (T r t : ℝ≥0) (hrt : r ≤ t) :
    (∫ sample,‖vectorAdditiveState d σ x0 T t sample-vectorAdditiveState d σ x0 T r sample‖^2
      ∂vectorDisorderBrownianMeasure n) ≤
      2*(d.bound : ℝ)^2*((t : ℝ)-r)^2+2*σ^2*n*((t : ℝ)-r) := by
  have hiX : Integrable (fun sample =>
      ‖vectorAdditiveState d σ x0 T t sample-vectorAdditiveState d σ x0 T r sample‖^2)
      (vectorDisorderBrownianMeasure n) :=
    ((memLp_vectorAdditiveState d σ x0 T t).sub
      (memLp_vectorAdditiveState d σ x0 T r)).integrable_norm_pow'
  have hiW := integrable_disorderVectorBrownianIncrement_norm_pow (n := n) r t hrt 2
  have hpoint (sample : VectorDisorderBrownianSample n) :
      ‖vectorAdditiveState d σ x0 T t sample-vectorAdditiveState d σ x0 T r sample‖^2 ≤
        2*(d.bound : ℝ)^2*((t : ℝ)-r)^2+2*σ^2*‖disorderVectorBrownianIncrement r t sample‖^2 := by
    have hnorm := norm_vectorAdditiveState_increment_le d σ x0 T r t hrt sample
    have hdt : 0 ≤ (t : ℝ)-r := sub_nonneg.mpr (show (r : ℝ) ≤ t from hrt)
    have hsq := sq_le_sq₀ (norm_nonneg _)
      (by positivity : 0 ≤ d.bound*((t : ℝ)-r)+|σ| * ‖disorderVectorBrownianIncrement r t sample‖) |>.mpr hnorm
    nlinarith only [hsq,sq_abs σ,sq_nonneg
      (d.bound*((t : ℝ)-r)-|σ| * ‖disorderVectorBrownianIncrement r t sample‖)]
  have hm := integral_mono hiX
    ((integrable_const (2*(d.bound : ℝ)^2*((t : ℝ)-r)^2)).add (hiW.const_mul (2*σ^2))) hpoint
  change (∫ sample,‖vectorAdditiveState d σ x0 T t sample-vectorAdditiveState d σ x0 T r sample‖^2
    ∂vectorDisorderBrownianMeasure n) ≤
    ∫ sample,2*(d.bound : ℝ)^2*((t : ℝ)-r)^2+2*σ^2*‖disorderVectorBrownianIncrement r t sample‖^2
      ∂vectorDisorderBrownianMeasure n at hm
  rw [integral_add (f := fun _ => 2*(d.bound : ℝ)^2*((t : ℝ)-r)^2)
      (g := fun sample => 2*σ^2*‖disorderVectorBrownianIncrement r t sample‖^2)
      (integrable_const _) (hiW.const_mul (2*σ^2)),integral_const,integral_const_mul] at hm
  simp only [MeasureTheory.probReal_univ,one_smul] at hm
  rw [FourPapersCommon.integral_increment_norm_sq r t hrt] at hm
  convert hm using 1 <;> ring

end QuantitativePaper
