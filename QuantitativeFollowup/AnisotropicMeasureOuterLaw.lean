module
public import QuantitativeFollowup.AnisotropicMeasureDerivative

@[expose] public section

/-! The actual disorder tilt of the arbitrary-profile anisotropic potential.
Its Gaussian exponential integrability and probability normalization are
derived from the constructed limit's global Lipschitz bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}

theorem integrable_exp_anisotropicMeasurePotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Integrable (fun ω => Real.exp (a*anisotropicMeasurePotential D μ (anisotropicDisorderInjection n ω)))
      (anisotropicDisorderLaw n) := by
  simpa only [zero_add,anisotropicDisorderLaw] using integrable_exp_finiteStateGaussian_lipschitz
    (anisotropicMeasurePotential D μ) (anisotropicMeasurePotential_lipschitz D μ)
    (anisotropicDisorderInjection n) 0 a

def anisotropicMeasureOuterPartition (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) : ℝ :=
  ∫ ω,Real.exp (a*anisotropicMeasurePotential D μ (anisotropicDisorderInjection n ω))
    ∂anisotropicDisorderLaw n

theorem anisotropicMeasureOuterPartition_pos (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : 0<anisotropicMeasureOuterPartition D μ a :=
  integral_exp_pos (integrable_exp_anisotropicMeasurePotential D μ a)

def anisotropicMeasureOuterLaw (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) : Measure (AnisotropicDisorder n) :=
  (anisotropicDisorderLaw n).tilted (fun ω => a*anisotropicMeasurePotential D μ (anisotropicDisorderInjection n ω))

instance anisotropicMeasureOuterLaw_probability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : IsProbabilityMeasure (anisotropicMeasureOuterLaw D μ a) :=
  isProbabilityMeasure_tilted (integrable_exp_anisotropicMeasurePotential D μ a)

theorem anisotropicMeasureOuterLaw_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    anisotropicMeasureOuterLaw D μ a=(anisotropicDisorderLaw n).withDensity
      (fun ω => ENNReal.ofReal (Real.exp (a*anisotropicMeasurePotential D μ (anisotropicDisorderInjection n ω))/
        anisotropicMeasureOuterPartition D μ a)) := rfl

end QuantitativeFollowup
