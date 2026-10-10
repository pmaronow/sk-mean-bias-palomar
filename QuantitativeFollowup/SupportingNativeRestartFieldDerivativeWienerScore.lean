module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeRecordedBounds

@[expose] public section

/-! The finite marked-posterior derivative as an expectation on the fixed
actual Wiener probability space. The terminal Gibbs mark is integrated only
after the genuine recorded-law transport. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128

def anisotropicFiniteRestartWienerSquareResponse (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (v : ℕ) (i : Fin n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∫σ,cascadePosteriorRecordedSquareResponse (fun _ : Configuration n=>0)
    (anisotropicSchemeMass (vectorClampedScheme s q q.property))
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
    (k+1) v (cavityCoordinateFeature i) (anisotropicEnergyMap D (anisotropicFieldInjection n w))
    (anisotropicFiniteRestartEnergyHistory D s g q (anisotropicInverseNoiseMap D x) sample,σ)
    ∂anisotropicFiniteRestartSpinKernel D s g q (anisotropicInverseNoiseMap D x) sample

theorem measurable_anisotropicFiniteRestartWienerSquareResponse (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (v : ℕ) (i : Fin n) : Measurable (anisotropicFiniteRestartWienerSquareResponse D s g q x w v i) := by
  let cs:=vectorClampedScheme s q q.property
  let F:=cascadePosteriorRecordedSquareResponse (fun _ : Configuration n=>0)
    (anisotropicSchemeMass cs) (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D cs l))
    (k+1) v (cavityCoordinateFeature i) (anisotropicEnergyMap D (anisotropicFieldInjection n w))
  have hm : Measurable (fun z : VectorDisorderBrownianSample n×Configuration n=>
      F (anisotropicFiniteRestartEnergyHistory D s g q (anisotropicInverseNoiseMap D x) z.1,z.2)) :=
    (measurable_cascadePosteriorRecordedSquareResponse _ _ (anisotropicSchemeMass_nonneg cs) _ _ _ _ _).comp
      ((measurable_anisotropicFiniteRestartEnergyHistory D s g q _).prodMap measurable_id)
  exact hm.stronglyMeasurable.integral_kernel_prod_right.measurable

theorem anisotropicFiniteRestartWienerSquareResponse_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (v : ℕ) (i : Fin n) (sample : VectorDisorderBrownianSample n) :
    ‖anisotropicFiniteRestartWienerSquareResponse D s g q x w v i sample‖≤
      4*‖cavityCoordinateFeature i‖^2*‖anisotropicEnergyMap D (anisotropicFieldInjection n w)‖ := by
  unfold anisotropicFiniteRestartWienerSquareResponse
  have hb:=fun σ=>cascadePosteriorRecordedSquareResponse_bound (fun _ : Configuration n=>0)
    (anisotropicSchemeMass (vectorClampedScheme s q q.property)) (anisotropicSchemeMass_nonneg _)
    (anisotropicSchemeMass_le_one _ 0) (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step _))
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
    (k+1) v (cavityCoordinateFeature i) (anisotropicEnergyMap D (anisotropicFieldInjection n w))
    (anisotropicFiniteRestartEnergyHistory D s g q (anisotropicInverseNoiseMap D x) sample,σ)
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=anisotropicFiniteRestartSpinKernel D s g q (anisotropicInverseNoiseMap D x) sample) (.of_forall hb)

theorem fderiv_anisotropicFiniteRestartPosteriorSquare_wiener (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (v : ℕ) (i : Fin n) (x w : Field n) :
    fderiv ℝ (anisotropicFiniteRestartPosteriorSquare D s g q v i) x w=
      ∫sample,anisotropicFiniteRestartWienerSquareResponse D s g q x w v i sample
        ∂vectorDisorderBrownianMeasure n := by
  rw [fderiv_anisotropicFiniteRestartPosteriorSquare_marked]
  have hm : Measurable (fun z : VectorDisorderBrownianSample n×Configuration n=>
      cascadePosteriorRecordedSquareResponse (fun _ : Configuration n=>0)
        (anisotropicSchemeMass (vectorClampedScheme s q q.property))
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
        (k+1) v (cavityCoordinateFeature i) (anisotropicEnergyMap D (anisotropicFieldInjection n w))
        (anisotropicFiniteRestartEnergyHistory D s g q (anisotropicInverseNoiseMap D x) z.1,z.2)) :=
    (measurable_cascadePosteriorRecordedSquareResponse _ _ (anisotropicSchemeMass_nonneg _) _ _ _ _ _).comp
      ((measurable_anisotropicFiniteRestartEnergyHistory D s g q _).prodMap measurable_id)
  have hi : Integrable _ (anisotropicFiniteRestartMarkedLaw D s g q (anisotropicInverseNoiseMap D x)) :=
    Integrable.of_bound hm.aestronglyMeasurable
      (4*‖cavityCoordinateFeature i‖^2*‖anisotropicEnergyMap D (anisotropicFieldInjection n w)‖)
      (.of_forall fun z=>cascadePosteriorRecordedSquareResponse_bound _ _ (anisotropicSchemeMass_nonneg _)
        (anisotropicSchemeMass_le_one _ 0) (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step _))
        _ _ _ _ _ _)
  exact Measure.integral_compProd hi

end QuantitativeFollowup
