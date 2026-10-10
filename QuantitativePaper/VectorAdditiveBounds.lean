module
public import QuantitativePaper.VectorAdditiveDrift
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Actual vector additive states have square-integrable endpoints and
quantitative L1 and L2 increment bounds. The constants come from the genuine
Gaussian increment law and the actual bounded drift. -/
noncomputable section
open FourPapersCommon Function MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1500000
variable {n : ℕ}

theorem measurable_uncurry_vectorIntegratedAdditiveDrift
    (d : VectorAdditiveDriftData n) (σ : ℝ) (x0 : Field n) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × VectorDisorderBrownianSample n =>
      vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s p.2) p.1) := by
  have he : (fun p : ℝ≥0 × VectorDisorderBrownianSample n =>
      vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s p.2) p.1) =
      (fun p => vectorAdditiveState d σ x0 T p.1 p.2-x0-σ • disorderVectorBrownian p.1 p.2) := by
    funext p
    have hp := vectorAdditiveState_decomposition d σ x0 T p.1 p.2
    rw [hp]
    abel
  rw [he]
  exact ((measurable_uncurry_vectorAdditiveState d σ x0 T).sub measurable_const).sub
    ((measurable_uncurry_disorderVectorBrownian n).const_smul σ)

theorem norm_vectorIntegratedAdditiveDrift_le
    (d : VectorAdditiveDriftData n) (σ : ℝ) (x0 : Field n) (T r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s sample) r‖ ≤ d.bound*(r : ℝ) := by
  have hh := vectorIntegratedDrift_increment_bound
    (fun s => vectorAdditiveDrift d σ x0 T s sample)
    ((measurable_uncurry_vectorAdditiveDrift d σ x0 T).of_uncurry_right)
    d.bound (fun s => norm_vectorAdditiveDrift_le d σ x0 T s sample)
    (show (0 : ℝ≥0) ≤ r from bot_le)
  simpa [vectorIntegratedDrift] using hh

theorem memLp_disorderVectorBrownian (r : ℝ≥0) :
    MemLp (disorderVectorBrownian (n := n) r) 2 (vectorDisorderBrownianMeasure n) := by
  apply (memLp_two_iff_integrable_sq_norm (measurable_disorderVectorBrownian r).aestronglyMeasurable).mpr
  simpa [disorderVectorBrownianIncrement,disorderVectorBrownian] using
    integrable_disorderVectorBrownianIncrement_norm_pow (n := n) 0 r bot_le 2

theorem memLp_vectorAdditiveState (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) :
    MemLp (vectorAdditiveState d σ x0 T r) 2 (vectorDisorderBrownianMeasure n) := by
  have hi : MemLp (fun sample : VectorDisorderBrownianSample n =>
      vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s sample) r)
      2 (vectorDisorderBrownianMeasure n) := MemLp.of_bound
    (Measurable.of_uncurry_left
      (f := fun r sample => vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s sample) r)
      (x := r) (measurable_uncurry_vectorIntegratedAdditiveDrift d σ x0 T)).aestronglyMeasurable
    (d.bound*(r : ℝ)) (.of_forall (norm_vectorIntegratedAdditiveDrift_le d σ x0 T r))
  have he : vectorAdditiveState d σ x0 T r =
      (fun sample => x0+vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s sample) r+
        σ • disorderVectorBrownian r sample) :=
    funext (vectorAdditiveState_decomposition d σ x0 T r)
  rw [he]
  exact ((memLp_const x0).add hi).add ((memLp_disorderVectorBrownian r).const_smul σ)

theorem integrable_vectorAdditiveState (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) :
    Integrable (vectorAdditiveState d σ x0 T r) (vectorDisorderBrownianMeasure n) :=
  (memLp_vectorAdditiveState d σ x0 T r).integrable (by norm_num)

/-- All-path increment bound, with genuine Brownian increment and exact drift constant. -/
theorem norm_vectorAdditiveState_increment_le (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r t : ℝ≥0) (hrt : r ≤ t) (sample : VectorDisorderBrownianSample n) :
    ‖vectorAdditiveState d σ x0 T t sample-vectorAdditiveState d σ x0 T r sample‖ ≤
      d.bound*((t : ℝ)-r)+|σ| * ‖disorderVectorBrownianIncrement r t sample‖ := by
  rw [vectorAdditiveState_decomposition,vectorAdditiveState_decomposition]
  have he : (x0+vectorIntegratedDrift (fun s=>vectorAdditiveDrift d σ x0 T s sample) t+
        σ • disorderVectorBrownian t sample)-
      (x0+vectorIntegratedDrift (fun s=>vectorAdditiveDrift d σ x0 T s sample) r+
        σ • disorderVectorBrownian r sample) =
      (vectorIntegratedDrift (fun s=>vectorAdditiveDrift d σ x0 T s sample) t-
        vectorIntegratedDrift (fun s=>vectorAdditiveDrift d σ x0 T s sample) r)+
        σ • disorderVectorBrownianIncrement r t sample := by
    simp only [disorderVectorBrownianIncrement,smul_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (vectorIntegratedDrift_increment_bound _
      (measurable_uncurry_vectorAdditiveDrift d σ x0 T).of_uncurry_right d.bound
      (fun s=>norm_vectorAdditiveDrift_le d σ x0 T s sample) hrt)
    (by rw [norm_smul,Real.norm_eq_abs]))

/-- The expectation increment bound needed for genuine time-FTC limits. -/
theorem integral_norm_vectorAdditiveState_increment_le
    (d : VectorAdditiveDriftData n) (σ : ℝ) (x0 : Field n)
    (T r t : ℝ≥0) (hrt : r ≤ t) :
    (∫ sample,‖vectorAdditiveState d σ x0 T t sample-vectorAdditiveState d σ x0 T r sample‖
      ∂vectorDisorderBrownianMeasure n) ≤
      |σ| * vectorGaussianNormMoment n 1*Real.sqrt ((t : ℝ)-r)+d.bound*((t : ℝ)-r) := by
  have hi : Integrable (fun sample => ‖disorderVectorBrownianIncrement r t sample‖)
      (vectorDisorderBrownianMeasure n) := by
    simpa only [pow_one] using integrable_disorderVectorBrownianIncrement_norm_pow r t hrt 1
  have hpoint := integral_mono
    ((integrable_vectorAdditiveState d σ x0 T t).sub
      (integrable_vectorAdditiveState d σ x0 T r)).norm
    ((integrable_const (d.bound*((t : ℝ)-r))).add (hi.const_mul |σ|))
    (norm_vectorAdditiveState_increment_le d σ x0 T r t hrt)
  change (∫ sample,‖vectorAdditiveState d σ x0 T t sample-vectorAdditiveState d σ x0 T r sample‖
    ∂vectorDisorderBrownianMeasure n) ≤
    ∫ sample,d.bound*((t : ℝ)-r)+|σ| * ‖disorderVectorBrownianIncrement r t sample‖
      ∂vectorDisorderBrownianMeasure n at hpoint
  rw [integral_add (f := fun _ => d.bound*((t : ℝ)-r))
      (g := fun sample => |σ| * ‖disorderVectorBrownianIncrement r t sample‖)
      (integrable_const _) (hi.const_mul |σ|),integral_const,integral_const_mul] at hpoint
  simp only [MeasureTheory.probReal_univ,one_smul] at hpoint
  have hm := integral_disorderVectorBrownianIncrement_norm_pow (n := n) r t hrt 1
  simp only [pow_one] at hm
  rw [hm] at hpoint
  convert hpoint using 1 <;> ring

end QuantitativePaper
