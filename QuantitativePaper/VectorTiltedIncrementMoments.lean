module
public import QuantitativePaper.VectorTiltedBrownian
public import FourPapersCommon.VectorGaussianMoments

@[expose] public section

/-! Exact Gaussian moments and adapted linear/quadratic cancellations under
the actual fractional disorder law. No Brownian law under the tilt is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem integral_vectorMeasureDisorderTilt_wienerFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1)
    (f : VectorBrownianSample n → E) (hf : Measurable f) :
    (∫ sample, f sample.2 ∂vectorMeasureDisorderTilt μ β t a) =
      ∫ sample, f sample.2 ∂vectorDisorderBrownianMeasure n := by
  have h1 := (hasLaw_vectorBrownian_samples_tilted μ β t a ht).integral_comp
    hf.aestronglyMeasurable
  have h0 := (hasLaw_vectorBrownian_samples_with_disorder n).integral_comp
    hf.aestronglyMeasurable
  exact h1.trans h0.symm

theorem integrable_tilted_increment_norm_pow (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u) (p : ℕ) :
    Integrable (fun sample => ‖disorderVectorBrownianIncrement (n := n) r u sample‖ ^ p)
      (vectorMeasureDisorderTilt μ β t a) := by
  change Integrable ((fun z : Field n => ‖z‖ ^ p) ∘ disorderVectorBrownianIncrement r u) _
  apply (hasLaw_disorderVectorBrownianIncrement_tilted μ β t a ht r u hru).integrable_comp
  unfold fieldIncrementLaw
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow] using
    (integrable_vectorGaussian_norm_pow n p).const_mul (Real.sqrt ((u-r : ℝ≥0) : ℝ)^p)

theorem integral_tilted_increment_norm_pow (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u) (p : ℕ) :
    (∫ sample, ‖disorderVectorBrownianIncrement (n := n) r u sample‖ ^ p
      ∂vectorMeasureDisorderTilt μ β t a) =
      Real.sqrt ((u : ℝ)-r)^p*vectorGaussianNormMoment n p := by
  rw [show (fun sample : VectorDisorderBrownianSample n =>
    ‖disorderVectorBrownianIncrement r u sample‖ ^ p) =
    (fun sample => ‖vectorBrownian u sample.2-vectorBrownian r sample.2‖ ^ p) from rfl,
    integral_vectorMeasureDisorderTilt_wienerFunction μ β t a ht
      (fun sample : VectorBrownianSample n => ‖vectorBrownian u sample-vectorBrownian r sample‖ ^ p)
      (((measurable_vectorBrownian u).sub (measurable_vectorBrownian r)).norm.pow_const p)]
  exact integral_disorderVectorBrownianIncrement_norm_pow r u hru p

theorem integrable_tilted_increment (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u) :
    Integrable (disorderVectorBrownianIncrement (n := n) r u)
      (vectorMeasureDisorderTilt μ β t a) := by
  apply (integrable_norm_iff
    (measurable_disorderVectorBrownianIncrement r u).aestronglyMeasurable).mp
  simpa only [pow_one] using integrable_tilted_increment_norm_pow μ β t a ht r u hru 1

theorem integral_tilted_increment (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u) :
    (∫ sample, disorderVectorBrownianIncrement (n := n) r u sample
      ∂vectorMeasureDisorderTilt μ β t a) = 0 := by
  rw [show disorderVectorBrownianIncrement (n := n) r u =
    (fun sample => vectorBrownian u sample.2-vectorBrownian r sample.2) from rfl,
    integral_vectorMeasureDisorderTilt_wienerFunction μ β t a ht
      (fun sample : VectorBrownianSample n => vectorBrownian u sample-vectorBrownian r sample)
      ((measurable_vectorBrownian u).sub (measurable_vectorBrownian r))]
  exact integral_increment r u hru

theorem integrable_tilted_increment_coordinates_mul (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u) (i j : Fin n) :
    Integrable (fun sample => disorderVectorBrownianIncrement r u sample i *
      disorderVectorBrownianIncrement r u sample j) (vectorMeasureDisorderTilt μ β t a) := by
  apply (integrable_tilted_increment_norm_pow μ β t a ht r u hru 2).mono'
    ((show Measurable (fun z : Field n => z i*z j) from by fun_prop).comp
      (measurable_disorderVectorBrownianIncrement r u)).aestronglyMeasurable
  exact .of_forall fun sample => by
    change ‖disorderVectorBrownianIncrement r u sample i*
      disorderVectorBrownianIncrement r u sample j‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul (PiLp.norm_apply_le _ i) (PiLp.norm_apply_le _ j)
      (norm_nonneg _) (norm_nonneg _)).trans_eq (pow_two _).symm

theorem integral_tilted_increment_coordinates_mul (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u) (i j : Fin n) :
    (∫ sample, disorderVectorBrownianIncrement r u sample i *
      disorderVectorBrownianIncrement r u sample j ∂vectorMeasureDisorderTilt μ β t a) =
      if i=j then (u : ℝ)-r else 0 := by
  change (∫ sample, (vectorBrownian u sample.2 i-vectorBrownian r sample.2 i)*
    (vectorBrownian u sample.2 j-vectorBrownian r sample.2 j) ∂vectorMeasureDisorderTilt μ β t a) = _
  rw [integral_vectorMeasureDisorderTilt_wienerFunction μ β t a ht
    (fun sample : VectorBrownianSample n =>
      (vectorBrownian u sample i-vectorBrownian r sample i)*
        (vectorBrownian u sample j-vectorBrownian r sample j))
    ((show Measurable (fun z : Field n => z i*z j) from by fun_prop).comp
      ((measurable_vectorBrownian u).sub (measurable_vectorBrownian r)))]
  exact integral_cross_disorderVectorBrownianIncrement_coordinates r u hru i j

theorem integrable_tilted_known_CLM_increment (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u)
    (L : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL : Measurable[vectorBrownianFiltration n r] L)
    (hiL : Integrable L (vectorMeasureDisorderTilt μ β t a)) :
    Integrable (fun sample => L sample (disorderVectorBrownianIncrement r u sample))
      (vectorMeasureDisorderTilt μ β t a) :=
  (indep_disorderVectorBrownianIncrement_known_tilted μ β t a ht r u hru L hL).symm.integrable_bilin
    hiL (integrable_tilted_increment μ β t a ht r u hru) (ContinuousLinearMap.apply ℝ ℝ).flip

theorem integral_tilted_known_CLM_increment (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u)
    (L : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL : Measurable[vectorBrownianFiltration n r] L)
    (hiL : Integrable L (vectorMeasureDisorderTilt μ β t a)) :
    (∫ sample, L sample (disorderVectorBrownianIncrement r u sample)
      ∂vectorMeasureDisorderTilt μ β t a) = 0 := by
  have H := (indep_disorderVectorBrownianIncrement_known_tilted μ β t a ht r u hru L hL).symm.integral_bilin
    hiL (integrable_tilted_increment μ β t a ht r u hru)
      (ContinuousLinearMap.apply ℝ ℝ).flip
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply,
    integral_tilted_increment μ β t a ht r u hru, map_zero] using H

theorem integrable_tilted_known_mul_increment_coordinates (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n r] Z)
    (hiZ : Integrable Z (vectorMeasureDisorderTilt μ β t a)) (i j : Fin n) :
    Integrable (fun sample => Z sample*(disorderVectorBrownianIncrement r u sample i*
      disorderVectorBrownianIncrement r u sample j)) (vectorMeasureDisorderTilt μ β t a) := by
  have hI : IndepFun Z (fun sample => disorderVectorBrownianIncrement r u sample i*
      disorderVectorBrownianIncrement r u sample j) (vectorMeasureDisorderTilt μ β t a) := by
    simpa only [Function.comp_def, id_eq] using
      (indep_disorderVectorBrownianIncrement_known_tilted μ β t a ht r u hru Z hZ).symm.comp
        measurable_id (show Measurable (fun z : Field n => z i*z j) from by fun_prop)
  exact hI.integrable_mul hiZ (integrable_tilted_increment_coordinates_mul μ β t a ht r u hru i j)

theorem integral_tilted_known_mul_increment_coordinates (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n r] Z)
    (hiZ : Integrable Z (vectorMeasureDisorderTilt μ β t a)) (i j : Fin n) :
    (∫ sample, Z sample*(disorderVectorBrownianIncrement r u sample i*
      disorderVectorBrownianIncrement r u sample j) ∂vectorMeasureDisorderTilt μ β t a) =
      (∫ sample, Z sample ∂vectorMeasureDisorderTilt μ β t a)*
        (if i=j then (u : ℝ)-r else 0) := by
  have hI : IndepFun Z (fun sample => disorderVectorBrownianIncrement r u sample i*
      disorderVectorBrownianIncrement r u sample j) (vectorMeasureDisorderTilt μ β t a) := by
    simpa only [Function.comp_def, id_eq] using
      (indep_disorderVectorBrownianIncrement_known_tilted μ β t a ht r u hru Z hZ).symm.comp
        measurable_id (show Measurable (fun z : Field n => z i*z j) from by fun_prop)
  rw [hI.integral_fun_mul_eq_mul_integral hiZ.aestronglyMeasurable
    (integrable_tilted_increment_coordinates_mul μ β t a ht r u hru i j).aestronglyMeasurable,
    integral_tilted_increment_coordinates_mul μ β t a ht r u hru i j]

end QuantitativePaper
