module
public import QuantitativeFollowup.AnisotropicTailResponseMeasurable
public import QuantitativeFollowup.AnisotropicMeasureOuterLaw
public import QuantitativePaper.VectorBrownian
public import FourPapersCommon.VectorPicardMeasurable

@[expose] public section

/-! The actual measurable bounded Lipschitz drift for every anisotropic
profile, driven by the literal independent coordinate Wiener processes.
The diagonal covariance map is constructed from the model's positive Lambda. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 800000

abbrev AnisotropicDisorderBrownianSample (n : ℕ) := AnisotropicDisorder n×VectorBrownianSample n

def anisotropicMeasureSampleLaw (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) :
    Measure (AnisotropicDisorderBrownianSample n) :=
  (anisotropicMeasureOuterLaw D μ a).prod (vectorBrownianMeasure n)

instance anisotropicMeasureSampleLaw_probability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : IsProbabilityMeasure (anisotropicMeasureSampleLaw D μ a) := by
  unfold anisotropicMeasureSampleLaw
  infer_instance

def anisotropicVarianceMap (D : AnisotropicSpinModel n) : Field n→L[ℝ]Field n :=
  (anisotropicNoiseMap D).comp (anisotropicNoiseMap D)

theorem anisotropicVarianceMap_apply (D : AnisotropicSpinModel n) (x : Field n) (i : Fin n) :
    anisotropicVarianceMap D x i=D.variance i*x i := by
  change Real.sqrt (D.variance i)*(Real.sqrt (D.variance i)*x i)=_
  rw [←mul_assoc,←pow_two,Real.sq_sqrt (D.variance_pos i).le]

def anisotropicWienerNoise (D : AnisotropicSpinModel n) (r : ℝ)
    (sample : AnisotropicDisorderBrownianSample n) : Field n :=
  anisotropicNoiseMap D (vectorBrownian r.toNNReal sample.2)

theorem measurable_uncurry_anisotropicWienerNoise (D : AnisotropicSpinModel n) :
    Measurable (Function.uncurry (anisotropicWienerNoise D)) :=
  (anisotropicNoiseMap D).continuous.measurable.comp
    ((measurable_uncurry_vectorBrownian n).comp ((by fun_prop : Measurable (fun z : ℝ×AnisotropicDisorderBrownianSample n =>
      (z.1.toNNReal,z.2.2)))))

theorem continuous_anisotropicWienerNoise (D : AnisotropicSpinModel n)
    (sample : AnisotropicDisorderBrownianSample n) : Continuous (fun r => anisotropicWienerNoise D r sample) :=
  (anisotropicNoiseMap D).continuous.comp ((continuous_vectorBrownian sample.2).comp continuous_real_toNNReal)

def anisotropicDrivenParameter (D : AnisotropicSpinModel n) (sample : AnisotropicDisorderBrownianSample n)
    (r : ℝ) (y : Field n) : AnisotropicParameter n :=
  anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n (y+anisotropicWienerNoise D r sample)

theorem anisotropicDrivenParameter_lipschitz (D : AnisotropicSpinModel n)
    (sample : AnisotropicDisorderBrownianSample n) (r : ℝ) :
    LipschitzWith ‖anisotropicFieldInjection n‖₊ (anisotropicDrivenParameter D sample r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,anisotropicDrivenParameter,add_sub_add_left_eq_sub,←map_sub,
    add_sub_add_right_eq_sub,coe_nnnorm]
  exact (anisotropicFieldInjection n).le_opNorm (x-y)

def anisotropicDrivenDrift (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (sample : AnisotropicDisorderBrownianSample n) (r : ℝ) (y : Field n) : Field n :=
  Paper.parisiCDF μ r • anisotropicVarianceMap D
    (anisotropicMeasureTailMagnetization D μ (projIcc (0 : ℝ) 1 zero_le_one r)
      (anisotropicDrivenParameter D sample r y))

def anisotropicDriftBound (D : AnisotropicSpinModel n) : ℝ≥0 :=
  ‖anisotropicVarianceMap D‖₊*(Real.sqrt (n : ℝ)).toNNReal

def anisotropicDriftLipschitz (D : AnisotropicSpinModel n) : ℝ≥0 :=
  ‖anisotropicVarianceMap D‖₊*(‖anisotropicResponseMap n‖₊*(‖anisotropicEnergyMap D‖₊^2)*‖anisotropicFieldInjection n‖₊)

theorem measurable_anisotropicDrivenDrift (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) :
    Measurable (fun z : (ℝ×Field n)×AnisotropicDisorderBrownianSample n =>
      anisotropicDrivenDrift D μ z.2 z.1.1 z.1.2) := by
  have hnoise : Measurable (fun z : (ℝ×Field n)×AnisotropicDisorderBrownianSample n =>
      anisotropicWienerNoise D z.1.1 z.2) := (measurable_uncurry_anisotropicWienerNoise D).comp
    (measurable_fst.fst.prodMk measurable_snd)
  have hP : Measurable (fun z : (ℝ×Field n)×AnisotropicDisorderBrownianSample n =>
      anisotropicDrivenParameter D z.2 z.1.1 z.1.2) := by
    exact ((anisotropicDisorderInjection n).continuous.measurable.comp measurable_snd.fst).add
      ((anisotropicFieldInjection n).continuous.measurable.comp (measurable_fst.snd.add hnoise))
  have hq : Measurable (fun z : (ℝ×Field n)×AnisotropicDisorderBrownianSample n =>
      projIcc (0 : ℝ) 1 zero_le_one z.1.1) := by fun_prop
  have hM := (measurable_anisotropicMeasureTailMagnetization D μ).comp (hq.prodMk hP)
  exact (((Paper.parisiCDF_monotone μ).measurable.comp measurable_fst.fst).smul
    ((anisotropicVarianceMap D).continuous.measurable.comp hM))

theorem isBounded_anisotropicDrivenDrift (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (sample : AnisotropicDisorderBrownianSample n) :
    IsBoundedVectorDrift (anisotropicDrivenDrift D μ sample) (anisotropicDriftBound D)
      (anisotropicDriftLipschitz D) where
  measurable := (measurable_anisotropicDrivenDrift D μ).comp (measurable_id.prodMk measurable_const)
  norm_le := by
    intro r y
    rw [anisotropicDrivenDrift,norm_smul,Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ r)]
    simp only [anisotropicDriftBound,NNReal.coe_mul,coe_nnnorm,
      Real.coe_toNNReal (Real.sqrt (n : ℝ)) (Real.sqrt_nonneg (n : ℝ))]
    change Paper.parisiCDF μ r*‖anisotropicVarianceMap D _‖ ≤
      ‖anisotropicVarianceMap D‖*Real.sqrt (n : ℝ)
    calc
      _ ≤ Paper.parisiCDF μ r*(‖anisotropicVarianceMap D‖*Real.sqrt (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Paper.parisiCDF_nonneg μ r)
        exact ((anisotropicVarianceMap D).le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (norm_anisotropicMeasureTailMagnetization_le D μ _ _) (norm_nonneg _))
      _ ≤ _ := mul_le_of_le_one_left (by positivity) (Paper.parisiCDF_le_one μ r)
  lipschitz := by
    intro r
    have hM := (anisotropicMeasureTailMagnetization_lipschitz D μ
      (projIcc (0 : ℝ) 1 zero_le_one r)).comp (anisotropicDrivenParameter_lipschitz D sample r)
    have hV := (anisotropicVarianceMap D).lipschitzWith.comp hM
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [anisotropicDrivenDrift,anisotropicDrivenDrift,dist_smul₀,
      Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ r)]
    calc
      _ ≤ Paper.parisiCDF μ r*((anisotropicDriftLipschitz D : ℝ)*dist x y) := by
        exact mul_le_mul_of_nonneg_left (hV.dist_le_mul x y) (Paper.parisiCDF_nonneg μ r)
      _ ≤ _ := mul_le_of_le_one_left (by positivity) (Paper.parisiCDF_le_one μ r)

end QuantitativeFollowup
