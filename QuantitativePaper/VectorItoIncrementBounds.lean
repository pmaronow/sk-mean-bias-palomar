module
public import QuantitativePaper.VectorItoCharacteristics
public import QuantitativePaper.VectorDriftBounds

@[expose] public section

/-! The time-FTC increment inputs follow from the proved vector Itô
characteristics, the actual vector Wiener law, and the drift bound. No
integrability of the initial state is required for increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1000000
variable {n : ℕ} {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}

 theorem VectorItoCharacteristics.norm_increment_le (hc : VectorItoCharacteristics X d σ)
    (D : ℝ≥0) (hD : ∀ q sample,‖d q sample‖ ≤ D)
    (r t : ℝ≥0) (hrt : r ≤ t) (sample : VectorDisorderBrownianSample n) :
    ‖X t sample-X r sample‖ ≤ |σ| * ‖disorderVectorBrownianIncrement r t sample‖+D*((t : ℝ)-r) := by
  have he := hc.increment r t sample
  have he' : X t sample-X r sample = σ • disorderVectorBrownianIncrement r t sample+
      (vectorIntegratedDrift (fun s=>d s sample) t-vectorIntegratedDrift (fun s=>d s sample) r) := by
    rw [he]
    abel
  rw [he']
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_smul,Real.norm_eq_abs]
  · exact vectorIntegratedDrift_increment_bound _ hc.measurable_drift.of_uncurry_right D
      (fun s=>hD s sample) hrt

 theorem VectorItoCharacteristics.integrable_increment_norm (hc : VectorItoCharacteristics X d σ)
    (r t : ℝ≥0) (hrt : r ≤ t) :
    Integrable (fun sample=>‖X t sample-X r sample‖) (vectorDisorderBrownianMeasure n) := by
  obtain ⟨D,hD⟩ := hc.bounded_drift
  have hi : Integrable (fun sample=>‖disorderVectorBrownianIncrement r t sample‖)
      (vectorDisorderBrownianMeasure n) := by
    simpa only [pow_one] using integrable_disorderVectorBrownianIncrement_norm_pow (n := n) r t hrt 1
  have hm := ((hc.measurable_state.of_uncurry_left (x := t)).sub
    (hc.measurable_state.of_uncurry_left (x := r))).norm
  apply ((hi.const_mul |σ|).add (integrable_const (D*((t : ℝ)-r)))).mono' hm.aestronglyMeasurable
  exact .of_forall (fun sample=>by
    simpa only [Real.norm_eq_abs,abs_norm,Pi.add_apply,Pi.sub_apply] using hc.norm_increment_le D hD r t hrt sample)

 theorem VectorItoCharacteristics.integral_norm_increment_le (hc : VectorItoCharacteristics X d σ)
    (D : ℝ≥0) (hD : ∀ q sample,‖d q sample‖ ≤ D) (r t : ℝ≥0) (hrt : r ≤ t) :
    (∫ sample,‖X t sample-X r sample‖ ∂vectorDisorderBrownianMeasure n) ≤
      |σ| * vectorGaussianNormMoment n 1*Real.sqrt ((t : ℝ)-r)+D*((t : ℝ)-r) := by
  have hi : Integrable (fun sample=>‖disorderVectorBrownianIncrement r t sample‖)
      (vectorDisorderBrownianMeasure n) := by
    simpa only [pow_one] using integrable_disorderVectorBrownianIncrement_norm_pow (n := n) r t hrt 1
  have hh := integral_mono (hc.integrable_increment_norm r t hrt)
    ((hi.const_mul |σ|).add (integrable_const (D*((t : ℝ)-r)))) (hc.norm_increment_le D hD r t hrt)
  change (∫ sample,‖X t sample-X r sample‖ ∂vectorDisorderBrownianMeasure n) ≤
    ∫ sample,|σ| * ‖disorderVectorBrownianIncrement r t sample‖+D*((t : ℝ)-r)
      ∂vectorDisorderBrownianMeasure n at hh
  rw [integral_add (f := fun sample=>|σ| * ‖disorderVectorBrownianIncrement r t sample‖)
      (g := fun _=>D*((t : ℝ)-r)) (hi.const_mul |σ|) (integrable_const _),
      integral_const_mul,integral_const] at hh
  have hm := integral_disorderVectorBrownianIncrement_norm_pow (n := n) r t hrt 1
  simp only [pow_one] at hm
  rw [hm] at hh
  simp only [probReal_univ,one_smul] at hh
  convert hh using 1 <;> ring

end QuantitativePaper
