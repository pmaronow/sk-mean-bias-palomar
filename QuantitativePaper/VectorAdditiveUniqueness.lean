module
public import QuantitativePaper.VectorAdditiveDrift

@[expose] public section

/-! Pathwise uniqueness in the genuine continuous integral-equation class,
without differentiability of Brownian noise or an assumed stochastic law. -/
noncomputable section
open FourPapersCommon MeasureTheory Set Function StochasticCalculus
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1500000
variable {n : ℕ}

/-- Any continuous solution driven by the same actual Wiener path equals the constructed state. -/
theorem vectorAdditiveState_unique (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T : ℝ≥0) (sample : VectorDisorderBrownianSample n)
    (X : ℝ≥0 → Field n) (hX : Continuous X)
    (he : ∀ r ≤ T,X r = x0 + σ • disorderVectorBrownian r sample +
      ∫ s in Ioc (0 : ℝ≥0) r,d.drift s sample.1 (X s) ∂nonnegativeLebesgueMeasure) :
    ∀ r ≤ T,X r = vectorAdditiveState d σ x0 T r sample := by
  let Y : ℝ → Field n := fun s => X s.toNNReal-vectorAdditiveNoiseReal σ s sample
  have hY : Continuous Y := (hX.comp continuous_real_toNNReal).sub
    (continuous_vectorAdditiveNoiseReal σ sample)
  let hf := isBounded_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
    (continuous_vectorAdditiveNoiseReal σ) sample
  have hYe : ∀ r ∈ Icc (0 : ℝ) T,Y r = x0+
      ∫ s in 0..r,vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ) sample s (Y s) := by
    intro r hr
    have hrt : r.toNNReal ≤ T := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal r hr.1]
      exact hr.2
    have hx := he r.toNNReal hrt
    rw [vectorIntegral_Ioc_eq_interval,Real.coe_toNNReal r hr.1] at hx
    have hint : (∫ s in (0 : ℝ)..r,vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
        sample s (Y s)) = ∫ s in (0 : ℝ)..r,d.drift s.toNNReal sample.1 (X s.toNNReal) := by
      congr 1
      funext s
      simp only [vectorNoiseCorrectionDrift,Y,sub_add_cancel]
    rw [hint]
    change X r.toNNReal-σ • disorderVectorBrownian r.toNNReal sample = _
    rw [hx]
    abel
  have hu := VectorIntegralPicard.real_solution_unique (h := x0) T.coe_nonneg hf Y hY hYe
  intro r hr
  have h := hu (r : ℝ) ⟨r.coe_nonneg,show (r : ℝ) ≤ T from hr⟩
  change X (r : ℝ).toNNReal-σ • disorderVectorBrownian (r : ℝ).toNNReal sample =
    (vectorAdditiveCorrection d σ x0 T sample).compProj r at h
  simp only [Real.toNNReal_coe] at h
  exact sub_eq_iff_eq_add.mp h

end QuantitativePaper
