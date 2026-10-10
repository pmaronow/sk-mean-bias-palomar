module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNoiseRegularity

@[expose] public section

/-! Actual whole-future-noise integral transport and the literal native
initial-field derivative in that genuine continuous-path representation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

theorem anisotropic_full_past_noise_integral {X : Type*} [MeasurableSpace X]
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ≥0)
    (Z : AnisotropicDisorderBrownianSample n→X)
    (hZ : Measurable[anisotropicBrownianFiltration n q] Z)
    (f : X×VectorWienerPath n→ℝ) (hf : Measurable f) (C : ℝ)
    (hbound : ∀z,‖f z‖≤C) :
    (∫sample,(∫V,f (Z sample,V) ∂vectorWienerMeasure n) ∂anisotropicMeasureSampleLaw D μ a)=
      ∫sample,f (Z sample,anisotropicRecordedFutureBrownianPath q sample)
        ∂anisotropicMeasureSampleLaw D μ a := by
  let P:=anisotropicMeasureSampleLaw D μ a
  have hZm : Measurable Z:=hZ.mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hI:=(indep_anisotropicRecordedFutureBrownianPath_known D μ a q Z hZ).symm
  have hh:=hI.hasLaw_prod (hasLaw_map hZm.aemeasurable)
    (hasLaw_anisotropicRecordedFutureBrownianPath D μ a q)
  have hi : Integrable f ((P.map Z).prod (vectorWienerMeasure n)):=
    Integrable.of_bound hf.aestronglyMeasurable C (.of_forall hbound)
  have hm : AEStronglyMeasurable (fun z=>∫V,f (z,V) ∂vectorWienerMeasure n) (P.map Z):=
    hf.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  rw [←integral_map hZm.aemeasurable hm,←integral_prod _ hi,←hh.map_eq,
    integral_map hh.aemeasurable hf.aestronglyMeasurable]

theorem fderiv_anisotropicRestartSpinSquare_field_native_noise (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x : Field n) (i : Fin n) :
    fderiv ℝ (fun y=>anisotropicRestartSpinSquare D μ g q y i r) x
      (cavityRestartInitialMean D μ q (g,x))=
      ∫V,cavityRestartNoiseSquareResponse D μ q r i ((g,x),V) ∂vectorWienerMeasure n := by
  rw [fderiv_anisotropicRestartSpinSquare_field_score D μ g q r hqr]
  have hh : HasLaw (fun sample : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath sample.2)
      (vectorWienerMeasure n) (vectorDisorderBrownianMeasure n):=
    hasLaw_vectorCanonicalBrownianPath.comp (hasLaw_vectorBrownian_samples_with_disorder n)
  have hm : Measurable (fun V=>cavityRestartNoiseSquareResponse D μ q r i ((g,x),V)) :=
    (measurable_cavityRestartNoiseSquareResponse D μ q r i).comp (measurable_const.prodMk measurable_id)
  rw [←hh.map_eq,integral_map hh.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun sample=>(cavityRestartNoiseSquareResponse_canonical D μ g q r hqr x i sample).symm

end QuantitativeFollowup
