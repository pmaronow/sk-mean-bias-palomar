module
public import QuantitativePaper.VectorItoCharacteristicsAt
public import QuantitativePaper.VectorTaylorExpectation

@[expose] public section

/-! Genuine known-past Wiener moments after an arbitrary deterministic
left endpoint. These are the actual canonical future increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def disorderVectorBrownianIncrementAt (a r t : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : Field n :=
  disorderVectorBrownianIncrement (a+r) (a+t) sample

theorem measurable_disorderVectorBrownianIncrementAt (a r t : ℝ≥0) :
    Measurable (disorderVectorBrownianIncrementAt (n:=n) a r t) :=
  measurable_disorderVectorBrownianIncrement (a+r) (a+t)

theorem integrable_known_CLM_incrementAt (a r t : ℝ≥0) (hrt : r≤t)
    (L : VectorDisorderBrownianSample n→Field n→L[ℝ] ℝ)
    (hL : Measurable[vectorBrownianFiltrationAt n a r] L)
    (hiL : Integrable L (vectorDisorderBrownianMeasure n)) :
    Integrable (fun sample=>L sample (disorderVectorBrownianIncrementAt a r t sample))
      (vectorDisorderBrownianMeasure n) :=
  integrable_known_CLM_increment (a+r) (a+t) (add_le_add (le_refl a) hrt) L hL hiL

theorem integral_known_CLM_incrementAt (a r t : ℝ≥0) (hrt : r≤t)
    (L : VectorDisorderBrownianSample n→Field n→L[ℝ] ℝ)
    (hL : Measurable[vectorBrownianFiltrationAt n a r] L)
    (hiL : Integrable L (vectorDisorderBrownianMeasure n)) :
    (∫ sample,L sample (disorderVectorBrownianIncrementAt a r t sample)
      ∂vectorDisorderBrownianMeasure n)=0 :=
  integral_known_CLM_increment (a+r) (a+t) (add_le_add (le_refl a) hrt) L hL hiL

theorem integrable_known_bilinear_incrementAt (a r t : ℝ≥0) (hrt : r≤t)
    (H : VectorDisorderBrownianSample n→Field n→L[ℝ] Field n→L[ℝ] ℝ)
    (hH : Measurable[vectorBrownianFiltrationAt n a r] H)
    (hiH : Integrable H (vectorDisorderBrownianMeasure n)) :
    Integrable (fun sample=>H sample (disorderVectorBrownianIncrementAt a r t sample)
      (disorderVectorBrownianIncrementAt a r t sample)) (vectorDisorderBrownianMeasure n) :=
  integrable_known_bilinear_increment (a+r) (a+t) (add_le_add (le_refl a) hrt) H hH hiH

theorem integral_known_bilinear_incrementAt (a r t : ℝ≥0) (hrt : r≤t)
    (H : VectorDisorderBrownianSample n→Field n→L[ℝ] Field n→L[ℝ] ℝ)
    (hH : Measurable[vectorBrownianFiltrationAt n a r] H)
    (hiH : Integrable H (vectorDisorderBrownianMeasure n)) :
    (∫ sample,H sample (disorderVectorBrownianIncrementAt a r t sample)
      (disorderVectorBrownianIncrementAt a r t sample) ∂vectorDisorderBrownianMeasure n)=
      ((t : ℝ)-r)*∫ sample,vectorBilinearTrace (H sample) ∂vectorDisorderBrownianMeasure n := by
  simpa only [disorderVectorBrownianIncrementAt,NNReal.coe_add,add_sub_add_left_eq_sub] using
    integral_known_bilinear_increment (a+r) (a+t) (add_le_add (le_refl a) hrt) H hH hiH

theorem integrable_disorderVectorBrownianIncrementAt_norm_pow
    (a r t : ℝ≥0) (hrt : r≤t) (p : ℕ) :
    Integrable (fun sample=>‖disorderVectorBrownianIncrementAt (n:=n) a r t sample‖^p)
      (vectorDisorderBrownianMeasure n) :=
  integrable_disorderVectorBrownianIncrement_norm_pow (a+r) (a+t) (add_le_add (le_refl a) hrt) p

theorem integral_disorderVectorBrownianIncrementAt_norm_pow
    (a r t : ℝ≥0) (hrt : r≤t) (p : ℕ) :
    (∫ sample,‖disorderVectorBrownianIncrementAt (n:=n) a r t sample‖^p
      ∂vectorDisorderBrownianMeasure n)=Real.sqrt ((t : ℝ)-r)^p*vectorGaussianNormMoment n p := by
  simpa only [disorderVectorBrownianIncrementAt,NNReal.coe_add,add_sub_add_left_eq_sub] using
    integral_disorderVectorBrownianIncrement_norm_pow (n:=n) (a+r) (a+t) (add_le_add (le_refl a) hrt) p

theorem integral_weighted_vectorSpatialTaylorError_boundAt
    (a r t : ℝ≥0) (hrt : r≤t) (σ : ℝ)
    (f : VectorDisorderBrownianSample n→Field n→ℝ)
    (hf : ∀ sample,ContDiff ℝ 3 (f sample)) (K₂ K₃ D : ℝ≥0)
    (h₂ : ∀ sample x,‖iteratedFDeriv ℝ 2 (f sample) x‖≤K₂)
    (h₃ : ∀ sample x,‖iteratedFDeriv ℝ 3 (f sample) x‖≤K₃)
    (X V : VectorDisorderBrownianSample n→Field n)
    (hV : ∀ sample,‖V sample‖≤D*((t : ℝ)-r))
    (Z : VectorDisorderBrownianSample n→ℝ) (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C)
    (hR : AEStronglyMeasurable (fun sample=>Z sample*vectorSpatialTaylorError f X
      (fun sample=>σ • disorderVectorBrownianIncrementAt a r t sample) V sample)
      (vectorDisorderBrownianMeasure n)) :
    Integrable (fun sample=>Z sample*vectorSpatialTaylorError f X
      (fun sample=>σ • disorderVectorBrownianIncrementAt a r t sample) V sample)
      (vectorDisorderBrownianMeasure n) ∧
    |∫ sample,Z sample*vectorSpatialTaylorError f X
      (fun sample=>σ • disorderVectorBrownianIncrementAt a r t sample) V sample
      ∂vectorDisorderBrownianMeasure n|≤
      C*(2*K₃*|σ|^3*vectorGaussianNormMoment n 3*((t : ℝ)-r)*Real.sqrt ((t : ℝ)-r)+
        2*K₃*(D*((t : ℝ)-r))^3+
        K₂*|σ| * (D*((t : ℝ)-r))*Real.sqrt ((t : ℝ)-r)*vectorGaussianNormMoment n 1+
        K₂/2*(D*((t : ℝ)-r))^2) := by
  have hVa : ∀ sample,‖V sample‖≤D*(((a+t : ℝ≥0) : ℝ)-(a+r : ℝ≥0)) := by
    simpa only [NNReal.coe_add,add_sub_add_left_eq_sub] using hV
  simpa only [disorderVectorBrownianIncrementAt,NNReal.coe_add,add_sub_add_left_eq_sub] using
    integral_weighted_vectorSpatialTaylorError_bound (a+r) (a+t) (add_le_add (le_refl a) hrt)
      σ f hf K₂ K₃ D h₂ h₃ X V hVa Z C hC hR

end QuantitativePaper
