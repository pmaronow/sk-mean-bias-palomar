module
public import QuantitativeFollowup.AnisotropicMeasureDrift

@[expose] public section

/-! The actual arbitrary-profile anisotropic field is a measurable pathwise
Picard solution, with its literal diagonal Brownian noise and drift equation.
No finite-kernel or posterior-law identification is assumed here. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 800000

def anisotropicDriftCorrection (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r : ℝ) (sample : AnisotropicDisorderBrownianSample n) : Field n :=
  (VectorIntegralPicard.solution (h:=(0 : Field n)) (T:=1) zero_le_one
    (isBounded_anisotropicDrivenDrift D μ sample)).compProj r

def anisotropicMeasureState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r : ℝ) (sample : AnisotropicDisorderBrownianSample n) : Field n :=
  anisotropicDriftCorrection D μ r sample+anisotropicWienerNoise D r sample

theorem continuous_anisotropicMeasureState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (sample : AnisotropicDisorderBrownianSample n) : Continuous (fun r => anisotropicMeasureState D μ r sample) :=
  (ODE.FunSpace.continuous_compProj _).add (continuous_anisotropicWienerNoise D sample)

theorem measurable_uncurry_anisotropicMeasureState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) :
    Measurable (Function.uncurry (anisotropicMeasureState D μ)) :=
  (VectorIntegralPicard.measurable_uncurry_solution_compProj (T:=1) zero_le_one (0 : Field n)
    (anisotropicDrivenDrift D μ) (isBounded_anisotropicDrivenDrift D μ)
    (measurable_anisotropicDrivenDrift D μ)).add (measurable_uncurry_anisotropicWienerNoise D)

theorem anisotropicDriftCorrection_equation (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (sample : AnisotropicDisorderBrownianSample n) (r : ℝ) (hr : r∈Icc (0 : ℝ) 1) :
    anisotropicDriftCorrection D μ r sample=
      ∫ s in 0..r,anisotropicDrivenDrift D μ sample s (anisotropicDriftCorrection D μ s sample) := by
  have hh := VectorIntegralPicard.solution_equation (h:=(0 : Field n)) (T:=1) zero_le_one
    (isBounded_anisotropicDrivenDrift D μ sample) ⟨r,hr⟩
  rw [zero_add] at hh
  change (VectorIntegralPicard.solution (h:=(0 : Field n)) (T:=1) zero_le_one
    (isBounded_anisotropicDrivenDrift D μ sample)).compProj r=_
  rw [ODE.FunSpace.compProj_of_mem hr]
  exact hh

theorem anisotropicMeasureState_equation (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (sample : AnisotropicDisorderBrownianSample n) (r : ℝ) (hr : r∈Icc (0 : ℝ) 1) :
    anisotropicMeasureState D μ r sample=anisotropicNoiseMap D (vectorBrownian r.toNNReal sample.2)+
      ∫ s in 0..r,Paper.parisiCDF μ s • anisotropicVarianceMap D
        (anisotropicMeasureTailMagnetization D μ (projIcc (0 : ℝ) 1 zero_le_one s)
          (anisotropicDisorderInjection n sample.1+
            anisotropicFieldInjection n (anisotropicMeasureState D μ s sample))) := by
  rw [anisotropicMeasureState,anisotropicDriftCorrection_equation D μ sample r hr,add_comm]
  rfl

theorem anisotropicMeasureState_zero (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (sample : AnisotropicDisorderBrownianSample n) : anisotropicMeasureState D μ 0 sample=0 := by
  rw [anisotropicMeasureState,anisotropicDriftCorrection_equation D μ sample 0 (by norm_num)]
  simp [anisotropicWienerNoise]

theorem hasLaw_anisotropicMeasureInitialDisorder (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    HasLaw (Prod.fst : AnisotropicDisorderBrownianSample n→AnisotropicDisorder n)
      (anisotropicMeasureOuterLaw D μ a) (anisotropicMeasureSampleLaw D μ a) :=
  measurePreserving_fst.hasLaw

theorem hasLaw_anisotropicMeasureWienerSamples (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    HasLaw (Prod.snd : AnisotropicDisorderBrownianSample n→VectorBrownianSample n)
      (vectorBrownianMeasure n) (anisotropicMeasureSampleLaw D μ a) :=
  measurePreserving_snd.hasLaw

theorem indep_anisotropicMeasureInitialDisorder_Wiener (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    IndepFun (Prod.fst : AnisotropicDisorderBrownianSample n→AnisotropicDisorder n) Prod.snd
      (anisotropicMeasureSampleLaw D μ a) :=
  indepFun_prod (X:=id) (Y:=id) measurable_id measurable_id

end QuantitativeFollowup
