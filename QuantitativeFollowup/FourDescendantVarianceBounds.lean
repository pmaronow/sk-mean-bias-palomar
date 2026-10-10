module
public import QuantitativeFollowup.FourDescendantNativeLaw

@[expose] public section

/-! The rest variance is bounded by the genuine four-descendant observable.
This step applies to every profile and does not use rest contact. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000

theorem measurable_cavitySelectedSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (J : Finset (Fin n)) :
    Measurable (fun sample : AnisotropicDisorderBrownianSample n =>
      anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)) := by
  have hm := (continuous_anisotropicSelectedMeanSquare J).measurable.comp
    ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp
      ((measurable_const (a:=q)).prodMk measurable_id))
  simpa only [Function.comp_def,id_eq] using hm

theorem cavityFourDescendant_variance_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (J : Finset (Fin n)) :
    variance (fun sample : AnisotropicDisorderBrownianSample n =>
      anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample))
      (anisotropicMeasureSampleLaw D μ a) ≤
      ∫z,(cavitySelectedSpinOverlap J z.2.1.1 z.2.1.2-(q:ℝ))*
        (cavitySelectedSpinOverlap J z.2.2.1 z.2.2.2-(q:ℝ)) ∂cavityFourDescendantLaw D μ a q := by
  rw [cavityFourDescendantLaw_centered_overlap_product]
  have hA := (measurable_cavitySelectedSelfOverlap D μ q J).aestronglyMeasurable
    (μ := anisotropicMeasureSampleLaw D μ a)
  have h := variance_le_expectation_sq (hA.sub (aestronglyMeasurable_const (b := (q:ℝ))))
  change variance (fun sample : AnisotropicDisorderBrownianSample n =>
      anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)-(q:ℝ))
      (anisotropicMeasureSampleLaw D μ a) ≤
    ∫sample,(anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)-(q:ℝ))^2
      ∂anisotropicMeasureSampleLaw D μ a at h
  rw [variance_sub_const hA (q:ℝ)] at h
  exact h

theorem cavityFourDescendant_centered_product_nonneg (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (J : Finset (Fin n)) :
    0 ≤ ∫z,(cavitySelectedSpinOverlap J z.2.1.1 z.2.1.2-(q:ℝ))*
      (cavitySelectedSpinOverlap J z.2.2.1 z.2.2.2-(q:ℝ)) ∂cavityFourDescendantLaw D μ a q := by
  rw [cavityFourDescendantLaw_centered_overlap_product]
  exact integral_nonneg fun sample => sq_nonneg _

end QuantitativeFollowup
