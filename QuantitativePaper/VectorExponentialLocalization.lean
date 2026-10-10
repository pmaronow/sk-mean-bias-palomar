module
public import QuantitativePaper.VectorHistoryLinear
public import QuantitativePaper.VectorMeasureDisorderTilt
public import QuantitativePaper.VectorMeasureState

@[expose] public section

/-! Genuine exponential integrability of completion disorder and the actual
bounded-drift state, including arbitrary fractional disorder tilts. These
are localization inputs; no unbounded Itô identity is postulated. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n : ℕ}

theorem integrable_exp_completion_norm (n : ℕ) (K : ℝ) :
    Integrable (fun p : Couplings n×ℝ => Real.exp (K*‖p‖)) (completionLaw n) := by
  let L : VectorGaussianSpace n 0 →L[ℝ] (Couplings n×ℝ) :=
    (ContinuousLinearMap.fst ℝ (Couplings n×ℝ) (Fin 2→Field n)).comp
      (vectorEuclideanCoordinatesLinear n 0)
  have hmap : (SYK.standardGaussianMeasureOnEuclidean (VectorGaussianIndex n 0)).map L =
      completionLaw n := by
    change (SYK.standardGaussianMeasureOnEuclidean (VectorGaussianIndex n 0)).map
      (Prod.fst ∘ vectorEuclideanCoordinates n 0) = _
    rw [←Measure.map_map measurable_fst (measurable_vectorEuclideanCoordinates n 0),
      vectorEuclideanCoordinates_map,vectorGaussianCoordinateLaw,Measure.map_fst_prod,
      measure_univ,one_smul]
  rw [←hmap]
  apply (integrable_map_measure (by fun_prop) L.measurable.aemeasurable).mpr
  apply (SYK.integrable_exp_mul_norm (ι := VectorGaussianIndex n 0) (|K| *‖L‖)).mono'
    (by fun_prop)
  filter_upwards [] with z
  dsimp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    K*‖L z‖ ≤ |K| *‖L z‖ := mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)
    _ ≤ |K| *(‖L‖*‖z‖) := mul_le_mul_of_nonneg_left (L.le_opNorm z) (abs_nonneg _)
    _ = _ := by ring

def vectorDisorderNormConstant (n : ℕ) (β t : ℝ) : ℝ :=
  |β| *Real.sqrt t*((1/Real.sqrt (n : ℝ))*(Fintype.card (Edge n) : ℝ)+1)

theorem vectorDisorderNormConstant_nonneg (n : ℕ) (β t : ℝ) :
    0 ≤ vectorDisorderNormConstant n β t := by
  unfold vectorDisorderNormConstant
  positivity

theorem vectorDisorderEnvelope_le_norm (n : ℕ) (β t : ℝ) (p : Couplings n×ℝ) :
    vectorDisorderEnvelope n β t p ≤ vectorDisorderNormConstant n β t*‖p‖ := by
  have hsum : (∑ e : Edge n,|p.1 e|) ≤ (Fintype.card (Edge n) : ℝ)*‖p‖ := by
    calc
      _ ≤ ∑ _e : Edge n,‖p‖ := Finset.sum_le_sum fun e _ => by
        have he : |p.1 e| ≤ ‖p.1‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm p.1 e
        exact he.trans (norm_fst_le p)
      _ = _ := by simp
  have hs : |p.2| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le p
  unfold vectorDisorderEnvelope couplingEnvelope vectorDisorderNormConstant
  have hi : 0 ≤ 1/Real.sqrt (n : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hsum hi
  have h := mul_le_mul_of_nonneg_left (add_le_add hh hs)
    (mul_nonneg (abs_nonneg β) (Real.sqrt_nonneg t))
  nlinarith only [h]

theorem integrable_exp_vectorMeasurePotential_add_norm (μ : Paper.ParisiMeasure)
    (β t a K : ℝ) (ht : t≤1) :
    Integrable (fun p : Couplings n×ℝ =>
      Real.exp (a*vectorMeasurePotential μ β t p 0+K*‖p‖)) (completionLaw n) := by
  let C := |a| *vectorDisorderNormConstant n β t+|K|
  apply ((integrable_exp_completion_norm n C).const_mul
    (Real.exp (|a| *|vectorMeasurePotential (n := n) μ β t (0,0) 0|))).mono'
      ((Real.measurable_exp.comp ((measurable_vectorMeasurePotential_initial μ β t ht).const_mul a |>.add
        (measurable_norm.const_mul K))).aestronglyMeasurable)
  filter_upwards [] with p
  dsimp only [Function.comp_apply,Pi.add_apply]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd := (vectorMeasurePotential_disorder_bound μ β t ht p (0 : Field n)).trans
    (vectorDisorderEnvelope_le_norm n β t p)
  have hu : |vectorMeasurePotential μ β t p (0 : Field n)| ≤
      |vectorMeasurePotential (n := n) μ β t (0,0) 0|+vectorDisorderNormConstant n β t*‖p‖ := by
    have hh := abs_add_le (vectorMeasurePotential (n := n) μ β t (0,0) (0 : Field n))
      (vectorMeasurePotential μ β t p 0-vectorMeasurePotential (n := n) μ β t (0,0) 0)
    rw [add_sub_cancel] at hh
    linarith
  have ha := mul_le_mul_of_nonneg_left hu (abs_nonneg a)
  have he : a*vectorMeasurePotential μ β t p (0 : Field n) ≤
      |a| *|vectorMeasurePotential μ β t p 0| := by
    rw [←abs_mul]
    exact le_abs_self _
  have hk := mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg p)
  dsimp [C]
  nlinarith only [ha,he,hk]

theorem integrable_exp_vectorMeasureOuterWeight_norm (μ : Paper.ParisiMeasure)
    (β t a K : ℝ) (ht : t≤1) :
    Integrable (fun p : Couplings n×ℝ =>
      vectorMeasureOuterWeight μ β t a p*Real.exp (K*‖p‖)) (completionLaw n) := by
  convert (integrable_exp_vectorMeasurePotential_add_norm μ β t a K ht).div_const
    (vectorMeasureOuterPartition (n := n) μ β t a) using 1
  funext p
  simp only [vectorMeasureOuterWeight,Real.exp_add]
  ring

theorem integrable_exp_disorderVectorBrownian_norm (r : ℝ≥0) (K : ℝ) :
    Integrable (fun sample : VectorDisorderBrownianSample n =>
      Real.exp (K*‖disorderVectorBrownian r sample‖)) (vectorDisorderBrownianMeasure n) := by
  have hl := hasLaw_disorderVectorBrownianIncrement (n := n) 0 r bot_le
  have hi : Integrable (fun z : Field n => Real.exp (K*‖z‖)) (fieldIncrementLaw n r) := by
    unfold fieldIncrementLaw
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    simpa only [Function.comp_def,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_assoc] using
      SYK.integrable_exp_mul_norm (ι := Fin n) (K*Real.sqrt (r : ℝ))
  simpa [Function.comp_def,disorderVectorBrownianIncrement,disorderVectorBrownian] using hl.integrable_comp
    (f := fun z : Field n => Real.exp (K*‖z‖)) (by simpa only [tsub_zero] using hi)

theorem norm_vectorMeasureState_le (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureState μ β t ht r sample‖ ≤
      ((1-t)*β^2)*Real.sqrt n+Real.sqrt ((1-t)*β^2)*‖disorderVectorBrownian r sample‖ := by
  have hh := norm_vectorAdditiveState_increment_le (vectorMeasureDriftData (n := n) μ β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 1 0 r bot_le sample
  simp only [vectorAdditiveState_zero,sub_zero,NNReal.coe_zero,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hh
  have hbound : ((vectorMeasureDriftData (n := n) μ β t ht).bound : ℝ)=
      ((1-t)*β^2)*Real.sqrt n := rfl
  rw [hbound] at hh
  have he : disorderVectorBrownianIncrement 0 r sample=disorderVectorBrownian r sample := by
    simp [disorderVectorBrownianIncrement,disorderVectorBrownian]
  rw [he] at hh
  change ‖vectorMeasureState μ β t ht r sample‖ ≤ _ at hh
  have hc : 0 ≤ ((1-t)*β^2)*Real.sqrt n :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)) (Real.sqrt_nonneg _)
  exact hh.trans (add_le_add (mul_le_of_le_one_right hc
    (show (r : ℝ)≤1 from hr)) le_rfl)

end QuantitativePaper
