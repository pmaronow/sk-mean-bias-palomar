module
public import QuantitativeFollowup.FourDescendantVarianceBounds
public import FourPapersCommon.ParameterVarianceMeasurability

@[expose] public section

/-! Actual four-descendant centered moments and selected-rest variances
are integrable level curves for every profile, including all atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

theorem continuous_cavityFourDescendant_centered_product
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (a:ℝ) (J:Finset (Fin n)) :
    Continuous (fun q:Paper.Overlap=>∫z,
      (cavitySelectedSpinOverlap J z.2.1.1 z.2.1.2-(q:ℝ))*
      (cavitySelectedSpinOverlap J z.2.2.1 z.2.2.2-(q:ℝ))∂cavityFourDescendantLaw D μ a q) := by
  simp_rw [cavityFourDescendantLaw_centered_overlap_product]
  apply continuous_of_dominated (μ:=anisotropicMeasureSampleLaw D μ a) (bound:=fun _=>(1:ℝ))
  · intro q
    exact (((measurable_cavitySelectedSelfOverlap D μ q J).sub measurable_const).pow_const 2).aestronglyMeasurable
  · intro q
    exact .of_forall fun sample=>by
      let A:=anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)
      have hA:‖A‖≤1:=anisotropicSelectedMeanSquare_bound _ _
        (fun i=>anisotropicMeasureTailMagnetization_component_bound D μ q _ i)
      have hA0:0≤A:=by dsimp only [A,anisotropicSelectedMeanSquare];positivity
      have hA1:A≤1:=(le_abs_self A).trans (by simpa only [Real.norm_eq_abs] using hA)
      have habs:|A-(q:ℝ)|≤1:=abs_le.mpr ⟨by linarith[q.property.2],by linarith[q.property.1]⟩
      rw [norm_pow,Real.norm_eq_abs]
      exact pow_le_one₀ (abs_nonneg _) habs
  · exact integrable_const _
  · exact .of_forall fun sample=>
      (((continuous_anisotropicSelectedMeanSquare J).comp
        (continuous_anisotropicProcessMagnetization_time D μ sample)).sub continuous_subtype_val).pow 2

theorem integrable_cavityFourDescendant_centered_product
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (a:ℝ) (J:Finset (Fin n))
    (ν:Measure Paper.Overlap) [IsFiniteMeasure ν] :
    Integrable (fun q:Paper.Overlap=>∫z,
      (cavitySelectedSpinOverlap J z.2.1.1 z.2.1.2-(q:ℝ))*
      (cavitySelectedSpinOverlap J z.2.2.1 z.2.2.2-(q:ℝ))∂cavityFourDescendantLaw D μ a q) ν := by
  simpa only [IntegrableOn,Measure.restrict_univ] using
    (continuous_cavityFourDescendant_centered_product D μ a J).continuousOn.integrableOn_compact
      (μ:=ν) isCompact_univ

theorem integrable_cavitySelectedSelfOverlap_variance
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (a:ℝ) (J:Finset (Fin n))
    (ν:Measure Paper.Overlap) [IsFiniteMeasure ν] :
    Integrable (fun q:Paper.Overlap=>variance (fun sample=>
      anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample))
      (anisotropicMeasureSampleLaw D μ a)) ν := by
  have hmA:Measurable (fun z:Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ z.1 z.2)) :=
    (continuous_anisotropicSelectedMeanSquare J).measurable.comp
      (measurable_uncurry_anisotropicProcessMagnetization D μ)
  have hLp (q:Paper.Overlap):MemLp (fun sample=>
      anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)) 2
        (anisotropicMeasureSampleLaw D μ a) :=
    MemLp.of_bound (measurable_cavitySelectedSelfOverlap D μ q J).aestronglyMeasurable 1
      (.of_forall fun sample=>anisotropicSelectedMeanSquare_bound _ _
        (fun i=>anisotropicMeasureTailMagnetization_component_bound D μ q _ i))
  have hm:=measurable_parameter_variance _ hmA hLp
  have hi:=integrable_cavityFourDescendant_centered_product D μ a J ν
  exact hi.mono' hm.aestronglyMeasurable (.of_forall fun q=>by
    rw [Real.norm_of_nonneg (variance_nonneg _ _)]
    exact cavityFourDescendant_variance_le D μ a q J)

end QuantitativeFollowup
