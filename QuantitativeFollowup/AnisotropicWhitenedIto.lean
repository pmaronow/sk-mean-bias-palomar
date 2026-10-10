module
public import QuantitativeFollowup.AnisotropicWhitening
public import QuantitativePaper.VectorAdditiveIto
public import QuantitativePaper.VectorAdditiveUniqueness

@[expose] public section

/-! The actual anisotropic diffusion, conditional on its initial disorder,
is exactly a standard-noise Picard process. The extra initial SK variable in
the existing vector Itô engine is unused, and no transition law is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000

def anisotropicWhitenedDrift (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (r : ℝ≥0) (_p : Couplings n×ℝ) (y : Field n) : Field n :=
  Paper.parisiCDF μ r • anisotropicNoiseMap D
    (anisotropicMeasureTailMagnetization D μ (projIcc (0 : ℝ) 1 zero_le_one r)
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D y)))

def anisotropicWhitenedDriftBound (D : AnisotropicSpinModel n) : ℝ≥0 :=
  ‖anisotropicNoiseMap D‖₊*(Real.sqrt (n : ℝ)).toNNReal

def anisotropicWhitenedDriftLip (D : AnisotropicSpinModel n) : ℝ≥0 :=
  ‖anisotropicNoiseMap D‖₊*(‖anisotropicResponseMap n‖₊*‖anisotropicEnergyMap D‖₊^2)*
    (‖anisotropicFieldInjection n‖₊*‖anisotropicNoiseMap D‖₊)

theorem measurable_anisotropicWhitenedDrift (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) :
    Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n)=>
      anisotropicWhitenedDrift D μ g z.1 z.2.1 z.2.2) := by
  have hm := (measurable_anisotropicMeasureTailMagnetization D μ).comp
    (show Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n)=>
      (projIcc (0 : ℝ) 1 zero_le_one z.1,
        anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D z.2.2))) from by fun_prop)
  exact (((Paper.parisiCDF_monotone μ).measurable.comp
    (NNReal.continuous_coe.measurable.comp measurable_fst)).smul
    ((anisotropicNoiseMap D).continuous.measurable.comp hm))

theorem norm_anisotropicWhitenedDrift_le (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (r : ℝ≥0) (p : Couplings n×ℝ) (y : Field n) :
    ‖anisotropicWhitenedDrift D μ g r p y‖≤anisotropicWhitenedDriftBound D := by
  rw [anisotropicWhitenedDrift,norm_smul,Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ r)]
  simp only [anisotropicWhitenedDriftBound,NNReal.coe_mul,coe_nnnorm,
    Real.coe_toNNReal _ (Real.sqrt_nonneg (n : ℝ))]
  calc
    _≤Paper.parisiCDF μ r*(‖anisotropicNoiseMap D‖*Real.sqrt (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Paper.parisiCDF_nonneg μ r)
      exact ((anisotropicNoiseMap D).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_anisotropicMeasureTailMagnetization_le D μ _ _) (norm_nonneg _))
    _≤_ := mul_le_of_le_one_left (by positivity) (Paper.parisiCDF_le_one μ r)

theorem anisotropicWhitenedDrift_lipschitz (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (r : ℝ≥0) (p : Couplings n×ℝ) :
    LipschitzWith (anisotropicWhitenedDriftLip D) (anisotropicWhitenedDrift D μ g r p) := by
  have hp : LipschitzWith (‖anisotropicFieldInjection n‖₊*‖anisotropicNoiseMap D‖₊)
      (fun y : Field n=>anisotropicDisorderInjection n g+
        anisotropicFieldInjection n (anisotropicNoiseMap D y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left,Function.comp_apply] using
      ((anisotropicFieldInjection n).lipschitzWith.comp (anisotropicNoiseMap D).lipschitzWith).dist_le_mul x y
  have hm := (anisotropicMeasureTailMagnetization_lipschitz D μ
    (projIcc (0 : ℝ) 1 zero_le_one r)).comp hp
  have hh := (anisotropicNoiseMap D).lipschitzWith.comp hm
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [anisotropicWhitenedDrift,anisotropicWhitenedDrift,dist_smul₀,
    Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ r)]
  calc
    _≤Paper.parisiCDF μ r*((anisotropicWhitenedDriftLip D : ℝ)*dist x y) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [anisotropicWhitenedDriftLip,Function.comp_apply,mul_assoc] using hh.dist_le_mul x y)
        (Paper.parisiCDF_nonneg μ r)
    _≤_ := mul_le_of_le_one_left (by positivity) (Paper.parisiCDF_le_one μ r)

def anisotropicWhitenedDriftData (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) : VectorAdditiveDriftData n where
  drift := anisotropicWhitenedDrift D μ g
  bound := anisotropicWhitenedDriftBound D
  spatialLip := anisotropicWhitenedDriftLip D
  measurable := measurable_anisotropicWhitenedDrift D μ g
  norm_le := norm_anisotropicWhitenedDrift_le D μ g
  lipschitz := anisotropicWhitenedDrift_lipschitz D μ g

theorem anisotropicWhitenedState_eq_vectorAdditiveState (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (sample : VectorDisorderBrownianSample n) (r : ℝ≥0) (hr : r≤1) :
    anisotropicWhitenedState D μ r (g,sample.2)=
      vectorAdditiveState (anisotropicWhitenedDriftData D μ g) 1 0 1 r sample := by
  apply vectorAdditiveState_unique (anisotropicWhitenedDriftData D μ g) 1 0 1 sample
    (fun s=>anisotropicWhitenedState D μ s (g,sample.2))
    ((continuous_anisotropicWhitenedState D μ (g,sample.2)).comp NNReal.continuous_coe) ?_ r hr
  intro s hs
  have he := anisotropicWhitenedState_equation D μ s ⟨s.coe_nonneg,hs⟩ (g,sample.2)
  rw [vectorIntegral_Ioc_eq_interval]
  simp only [Real.toNNReal_coe,zero_add,one_smul,disorderVectorBrownian] at he ⊢
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le s.coe_nonneg] at hv
  simp only [anisotropicWhitenedDriftData,anisotropicWhitenedDrift,
    Real.coe_toNNReal v hv.1,gradient_anisotropicWhitenedTailPotential]

theorem anisotropicMeasureState_eq_whitenedPicard (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (sample : VectorDisorderBrownianSample n) (r : ℝ≥0) (hr : r≤1) :
    anisotropicMeasureState D μ r (g,sample.2)=anisotropicNoiseMap D
      (vectorAdditiveState (anisotropicWhitenedDriftData D μ g) 1 0 1 r sample) := by
  rw [←anisotropicWhitenedState_eq_vectorAdditiveState D μ g sample r hr,
    anisotropicWhitenedState,anisotropicNoiseMap_inverseNoise]

theorem vectorItoCharacteristics_anisotropicWhitenedState (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) :
    VectorItoCharacteristics
      (vectorAdditiveState (anisotropicWhitenedDriftData D μ g) 1 0 1)
      (vectorAdditiveDrift (anisotropicWhitenedDriftData D μ g) 1 0 1) 1 :=
  vectorItoCharacteristics_vectorAdditiveState _ _ _ _

end QuantitativeFollowup
