module
public import QuantitativePaper.VectorExponentialLocalization

@[expose] public section

/-! Actual fractional-tilt exponential moments of the constructed state and
the retained completion disorder. The proof uses their independent Gaussian
input law and the deterministic bounded-drift estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n : ℕ}

theorem integrable_exp_vectorBrownian_norm (r : ℝ≥0) (K : ℝ) :
    Integrable (fun sample : VectorBrownianSample n => Real.exp (K*‖vectorBrownian r sample‖))
      (vectorBrownianMeasure n) := by
  rw [←(hasLaw_vectorBrownian_samples_with_disorder n).map_eq]
  apply (integrable_map_measure
    ((Real.measurable_exp.comp ((measurable_vectorBrownian r).norm.const_mul K)).aestronglyMeasurable)
      measurable_snd.aemeasurable).mpr
  exact integrable_exp_disorderVectorBrownian_norm r K

theorem integrable_exp_vectorMeasureState_and_disorder (μ : Paper.ParisiMeasure)
    (β t outer K : ℝ) (ht : t≤1) (r : ℝ≥0) (hr : r≤1) :
    Integrable (fun sample : VectorDisorderBrownianSample n =>
      Real.exp (K*(‖sample.1‖+‖vectorMeasureState μ β t ht r sample‖)))
      (vectorMeasureDisorderTilt μ β t outer) := by
  let c := ((1-t)*β^2)*Real.sqrt (n : ℝ)
  let σ := Real.sqrt ((1-t)*β^2)
  let W := vectorMeasureOuterWeight (n := n) μ β t outer
  have hW : Measurable W:=measurable_vectorMeasureOuterWeight μ β t outer ht
  have hWpos (p : Couplings n×ℝ) : 0 ≤ W p:=by
    exact div_nonneg (Real.exp_pos _).le (vectorMeasureOuterPartition_pos μ β t outer ht).le
  have hs : Measurable (vectorMeasureState (n := n) μ β t ht r):=
    (measurable_uncurry_vectorMeasureState μ β t ht).of_uncurry_left
  have hmeas : Measurable (fun sample : VectorDisorderBrownianSample n =>
      Real.exp (K*(‖sample.1‖+‖vectorMeasureState μ β t ht r sample‖))):=
    Real.measurable_exp.comp ((measurable_fst.norm.add hs.norm).const_mul K)
  have hi := ((integrable_exp_vectorMeasureOuterWeight_norm (n := n) μ β t outer |K| ht).mul_prod
    (integrable_exp_vectorBrownian_norm (n := n) r (|K| *σ))).const_mul (Real.exp (|K| *c))
  have hweighted : Integrable (fun sample : VectorDisorderBrownianSample n =>
      W sample.1*Real.exp (K*(‖sample.1‖+‖vectorMeasureState μ β t ht r sample‖)))
      (vectorDisorderBrownianMeasure n) := by
    apply hi.mono' (((hW.comp measurable_fst).mul hmeas).aestronglyMeasurable)
    filter_upwards [] with sample
    dsimp only [Pi.mul_apply,Function.comp_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (hWpos _) (Real.exp_pos _).le)]
    have hstate := norm_vectorMeasureState_le μ β t ht r hr sample
    change ‖vectorMeasureState μ β t ht r sample‖ ≤ c+σ*‖vectorBrownian r sample.2‖ at hstate
    calc
      _ ≤ W sample.1*Real.exp (|K| *(‖sample.1‖+‖vectorMeasureState μ β t ht r sample‖)) := by
        apply mul_le_mul_of_nonneg_left _ (hWpos _)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (le_abs_self K) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ W sample.1*Real.exp (|K| *(‖sample.1‖+(c+σ*‖vectorBrownian r sample.2‖))) := by
        apply mul_le_mul_of_nonneg_left _ (hWpos _)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hstate) (abs_nonneg K)
      _ = Real.exp (|K| *c)*(vectorMeasureOuterWeight μ β t outer sample.1*
          Real.exp (|K| *‖sample.1‖)*Real.exp ((|K| *σ)*‖vectorBrownian r sample.2‖)) := by
        rw [show |K| *(‖sample.1‖+(c+σ*‖vectorBrownian r sample.2‖))=
          |K| *c+|K| *‖sample.1‖+(|K| *σ)*‖vectorBrownian r sample.2‖ by ring]
        simp only [Real.exp_add]
        dsimp only [W]
        ring
  rw [vectorMeasureDisorderTilt]
  apply (integrable_withDensity_iff_integrable_smul'
    (hW.comp measurable_fst).ennreal_ofReal (.of_forall fun _=>ENNReal.ofReal_lt_top)).mpr
  simpa only [Function.comp_apply,ENNReal.toReal_ofReal (hWpos _),smul_eq_mul] using hweighted

end QuantitativePaper
