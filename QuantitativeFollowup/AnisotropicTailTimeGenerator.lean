module
public import QuantitativeFollowup.AnisotropicTailContinuity
public import FourPapersCommon.GenericFiniteStateCascadeGeneratorField

@[expose] public section

/-! The genuine anisotropic spatial generator and its bounded measurable
all-profile time source. The time equation is not assumed here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128

def anisotropicTailTimeTrace (D : AnisotropicSpinModel n)
    (F : AnisotropicParameter n → ℝ) (P : AnisotropicParameter n) : ℝ :=
  ∑ i, fderiv ℝ (fderiv ℝ F) P
    (anisotropicUnitInput D (finiteStateGaussianBasis (Fin n) i))
    (anisotropicUnitInput D (finiteStateGaussianBasis (Fin n) i))

def anisotropicTailTimeGradientSquare (D : AnisotropicSpinModel n)
    (F : AnisotropicParameter n → ℝ) (P : AnisotropicParameter n) : ℝ :=
  ∑ i, (fderiv ℝ F P (anisotropicUnitInput D (finiteStateGaussianBasis (Fin n) i)))^2

theorem anisotropicTailTimeGenerator_eq (D : AnisotropicSpinModel n)
    (a : ℝ) (F : AnisotropicParameter n → ℝ) (P : AnisotropicParameter n) :
    finiteStateGaussianGeneratorField a (anisotropicUnitInput D) F P =
      (anisotropicTailTimeTrace D F P+a*anisotropicTailTimeGradientSquare D F P)/2 := by
  classical
  simp only [finiteStateGaussianGeneratorField,anisotropicTailTimeTrace,
    anisotropicTailTimeGradientSquare,Finset.sum_add_distrib,Finset.mul_sum]

def anisotropicFiniteTailTimeSource (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : ℝ) (P : AnisotropicParameter n) : ℝ :=
  -finiteStateGaussianGeneratorField (Paper.parisiCDF (Paper.parisiSchemeMeasure s) q)
    (anisotropicUnitInput D) (anisotropicFiniteTailPotential D s (projIcc 0 1 zero_le_one q)) P

def anisotropicMeasureTailTimeSource (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℝ) (P : AnisotropicParameter n) : ℝ :=
  -finiteStateGaussianGeneratorField (Paper.parisiCDF μ q) (anisotropicUnitInput D)
    (anisotropicMeasureTailPotential D μ (projIcc 0 1 zero_le_one q)) P

theorem norm_anisotropicFinitePotential_time_first_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (anisotropicFinitePotential D s j) P‖ ≤ ‖anisotropicEnergyMap D‖ :=
  norm_fderiv_le_of_lipschitz ℝ (anisotropicFinitePotential_lipschitz D s j)

theorem norm_anisotropicFinitePotential_time_second_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (fderiv ℝ (anisotropicFinitePotential D s j)) P‖ ≤ ‖anisotropicEnergyMap D‖^2 := by
  rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact norm_anisotropicFinitePotential_secondJet_le D s j P

theorem norm_anisotropicFiniteTail_time_first_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (anisotropicFiniteTailPotential D s q) P‖ ≤ ‖anisotropicEnergyMap D‖ := by
  unfold anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_clamped D s q q.property le_rfl]
  exact norm_anisotropicFinitePotential_time_first_le D _ _ P

theorem norm_anisotropicFiniteTail_time_second_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s q)) P‖ ≤ ‖anisotropicEnergyMap D‖^2 := by
  unfold anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_clamped D s q q.property le_rfl]
  exact norm_anisotropicFinitePotential_time_second_le D _ _ P

theorem norm_anisotropicMeasureTail_time_first_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (anisotropicMeasureTailPotential D μ q) P‖ ≤ ‖anisotropicEnergyMap D‖ := by
  apply le_of_tendsto (((tendstoUniformly_anisotropicDyadicTailDifferential D μ).tendsto_at (q,P)).norm)
  exact .of_forall fun j => norm_anisotropicFiniteTail_time_first_le D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q P

theorem norm_anisotropicMeasureTail_time_second_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P‖ ≤ ‖anisotropicEnergyMap D‖^2 := by
  apply le_of_tendsto (((tendstoUniformly_anisotropicDyadicTailSecondDifferential D μ).tendsto_at (q,P)).norm)
  exact .of_forall fun j => norm_anisotropicFiniteTail_time_second_le D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q P

private theorem continuous_timeTrace {F : Paper.Overlap → AnisotropicParameter n → ℝ}
    (D : AnisotropicSpinModel n)
    (h : Continuous (fun z : Paper.Overlap × AnisotropicParameter n => fderiv ℝ (fderiv ℝ (F z.1)) z.2))
    (P : AnisotropicParameter n) :
    Continuous (fun q : ℝ => anisotropicTailTimeTrace D (F (projIcc 0 1 zero_le_one q)) P) := by
  classical
  apply continuous_finsetSum
  intro i _
  have hp : Continuous (fun q : ℝ => (projIcc 0 1 zero_le_one q, P)) :=
    continuous_projIcc.prodMk continuous_const
  exact (((h.comp hp).clm_apply continuous_const).clm_apply continuous_const)

private theorem continuous_timeSquare {F : Paper.Overlap → AnisotropicParameter n → ℝ}
    (D : AnisotropicSpinModel n)
    (h : Continuous (fun z : Paper.Overlap × AnisotropicParameter n => fderiv ℝ (F z.1) z.2))
    (P : AnisotropicParameter n) :
    Continuous (fun q : ℝ => anisotropicTailTimeGradientSquare D (F (projIcc 0 1 zero_le_one q)) P) := by
  classical
  apply continuous_finsetSum
  intro i _
  have hp : Continuous (fun q : ℝ => (projIcc 0 1 zero_le_one q, P)) :=
    continuous_projIcc.prodMk continuous_const
  exact (((h.comp hp).clm_apply continuous_const).pow 2)

theorem anisotropicFiniteTailTimeSource_intervalIntegrable (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (P : AnisotropicParameter n) (a b : ℝ) :
    IntervalIntegrable (fun q => anisotropicFiniteTailTimeSource D s q P) volume a b := by
  simp only [anisotropicFiniteTailTimeSource,anisotropicTailTimeGenerator_eq]
  exact ((continuous_timeTrace D (continuous_anisotropicFiniteTailSecondDifferential_joint D s) P).intervalIntegrable a b |>.add
    ((Paper.parisiCDF_monotone _).intervalIntegrable.mul_continuousOn
      ((continuous_timeSquare D (continuous_anisotropicFiniteTailDifferential_joint D s) P).continuousOn))).div_const 2 |>.neg

theorem anisotropicMeasureTailTimeSource_intervalIntegrable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (a b : ℝ) :
    IntervalIntegrable (fun q => anisotropicMeasureTailTimeSource D μ q P) volume a b := by
  simp only [anisotropicMeasureTailTimeSource,anisotropicTailTimeGenerator_eq]
  exact ((continuous_timeTrace D (continuous_anisotropicMeasureTailSecondDifferential_joint D μ) P).intervalIntegrable a b |>.add
    ((Paper.parisiCDF_monotone _).intervalIntegrable.mul_continuousOn
      ((continuous_timeSquare D (continuous_anisotropicMeasureTailDifferential_joint D μ) P).continuousOn))).div_const 2 |>.neg

theorem continuousAt_anisotropicMeasureTailTimeSource (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (q : ℝ)
    (hCDF : ContinuousAt (Paper.parisiCDF μ) q) :
    ContinuousAt (fun t => anisotropicMeasureTailTimeSource D μ t P) q := by
  simp only [anisotropicMeasureTailTimeSource,anisotropicTailTimeGenerator_eq]
  exact (((continuous_timeTrace D (continuous_anisotropicMeasureTailSecondDifferential_joint D μ) P).continuousAt.add
    (hCDF.mul (continuous_timeSquare D (continuous_anisotropicMeasureTailDifferential_joint D μ) P).continuousAt)).div_const 2).neg


theorem measurable_anisotropicFiniteTailTimeSource (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (P : AnisotropicParameter n) :
    Measurable (fun q => anisotropicFiniteTailTimeSource D s q P) := by
  simp only [anisotropicFiniteTailTimeSource,anisotropicTailTimeGenerator_eq]
  exact (((continuous_timeTrace D (continuous_anisotropicFiniteTailSecondDifferential_joint D s) P).measurable.add
    ((Paper.parisiCDF_measurable _).mul
      (continuous_timeSquare D (continuous_anisotropicFiniteTailDifferential_joint D s) P).measurable)).div_const 2).neg

theorem measurable_anisotropicMeasureTailTimeSource (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) :
    Measurable (fun q => anisotropicMeasureTailTimeSource D μ q P) := by
  simp only [anisotropicMeasureTailTimeSource,anisotropicTailTimeGenerator_eq]
  exact (((continuous_timeTrace D (continuous_anisotropicMeasureTailSecondDifferential_joint D μ) P).measurable.add
    ((Paper.parisiCDF_measurable _).mul
      (continuous_timeSquare D (continuous_anisotropicMeasureTailDifferential_joint D μ) P).measurable)).div_const 2).neg

def anisotropicTailTimeSourceBound (D : AnisotropicSpinModel n) : ℝ :=
  (n:ℝ)*‖anisotropicEnergyMap D‖^2*‖anisotropicUnitInput D‖^2

theorem norm_anisotropic_generator_cdf_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℝ) (F : AnisotropicParameter n → ℝ)
    (hC : ∀P, ‖fderiv ℝ F P‖≤‖anisotropicEnergyMap D‖)
    (hB : ∀P, ‖fderiv ℝ (fderiv ℝ F) P‖≤‖anisotropicEnergyMap D‖^2)
    (P : AnisotropicParameter n) :
    ‖finiteStateGaussianGeneratorField (Paper.parisiCDF μ q) (anisotropicUnitInput D) F P‖≤
      anisotropicTailTimeSourceBound D := by
  have hB' : ∀P, ‖fderiv ℝ (fderiv ℝ F) P‖≤((‖anisotropicEnergyMap D‖₊^2 : ℝ≥0):ℝ) := by
    simpa only [NNReal.coe_pow,coe_nnnorm] using hB
  have hh := abs_finiteStateGaussianGeneratorField_le (Paper.parisiCDF μ q)
    (anisotropicUnitInput D) F ‖anisotropicEnergyMap D‖₊ (‖anisotropicEnergyMap D‖₊^2) hC hB' P
  rw [finiteStateGaussianGeneratorBound_coe,abs_of_nonneg (Paper.parisiCDF_nonneg μ q)] at hh
  simp only [Fintype.card_fin,NNReal.coe_pow,coe_nnnorm] at hh
  rw [Real.norm_eq_abs]
  apply hh.trans
  have hα := Paper.parisiCDF_le_one μ q
  have hprod := mul_le_mul_of_nonneg_right hα (sq_nonneg ‖anisotropicEnergyMap D‖)
  unfold anisotropicTailTimeSourceBound
  nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg ‖anisotropicUnitInput D‖)]

theorem norm_anisotropicFiniteTailTimeSource_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : ℝ) (P : AnisotropicParameter n) :
    ‖anisotropicFiniteTailTimeSource D s q P‖≤anisotropicTailTimeSourceBound D := by
  rw [anisotropicFiniteTailTimeSource,norm_neg]
  exact norm_anisotropic_generator_cdf_le D _ q _
    (norm_anisotropicFiniteTail_time_first_le D s _)
    (norm_anisotropicFiniteTail_time_second_le D s _) P

end QuantitativeFollowup
