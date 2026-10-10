module
public import QuantitativeFollowup.AnisotropicProcessResponse

@[expose] public section

/-! Actual selected-coordinate Hessian energies along the native anisotropic
process, with uniform bounds and genuine moving-grid convergence. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

private theorem continuous_parameter_quadratic_eval :
    Continuous (fun z : (AnisotropicParameter n →L[ℝ]
      (AnisotropicParameter n →L[ℝ] ℝ))×AnisotropicParameter n => z.1 z.2 z.2) :=
  (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd

def anisotropicSelectedParameterDirection (J : Finset (Fin n)) :
    Field n →L[ℝ] AnisotropicParameter n :=
  (anisotropicFieldInjection n).comp ((anisotropicSelectedInsertion J).comp
    (anisotropicSelectedProjection J))

def anisotropicProcessHessianEnergy (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (J : Finset (Fin n)) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  let v := anisotropicSelectedParameterDirection J (anisotropicProcessMagnetization D μ q sample)
  fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
    (anisotropicProcessParameter D μ q sample) v v

def anisotropicFiniteProcessHessianEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  let v := anisotropicSelectedParameterDirection J (anisotropicFiniteProcessMagnetization D s q sample)
  fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s q))
    (anisotropicFiniteProcessParameter D s q sample) v v

def anisotropicProcessEnergyBound (D : AnisotropicSpinModel n) (J : Finset (Fin n)) : ℝ :=
  ‖anisotropicEnergyMap D‖^2*‖anisotropicSelectedParameterDirection J‖^2*(n:ℝ)

theorem anisotropicProcessEnergyBound_nonneg (D : AnisotropicSpinModel n) (J : Finset (Fin n)) :
    0 ≤ anisotropicProcessEnergyBound D J := by unfold anisotropicProcessEnergyBound;positivity

theorem norm_anisotropicFiniteTailSecondDifferential_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s q)) P‖ ≤ ‖anisotropicEnergyMap D‖^2 := by
  rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  unfold anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_clamped D s q q.property le_rfl]
  exact norm_anisotropicFinitePotential_secondJet_le D _ _ P

theorem norm_anisotropicMeasureTailSecondDifferential_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P‖ ≤ ‖anisotropicEnergyMap D‖^2 := by
  apply le_of_tendsto (((tendstoUniformly_anisotropicDyadicTailSecondDifferential D μ).tendsto_at (q,P)).norm)
  exact .of_forall fun j => norm_anisotropicFiniteTailSecondDifferential_le D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q P

private theorem quadratic_energy_bound (D : AnisotropicSpinModel n) (J : Finset (Fin n))
    (T : AnisotropicParameter n →L[ℝ] (AnisotropicParameter n →L[ℝ] ℝ))
    (hT : ‖T‖ ≤ ‖anisotropicEnergyMap D‖^2) (m : Field n) (hm : ‖m‖ ≤ Real.sqrt (n:ℝ)) :
    ‖T (anisotropicSelectedParameterDirection J m) (anisotropicSelectedParameterDirection J m)‖ ≤
      anisotropicProcessEnergyBound D J := by
  let v := anisotropicSelectedParameterDirection J m
  have hv : ‖v‖ ≤ ‖anisotropicSelectedParameterDirection J‖*Real.sqrt (n:ℝ) :=
    ((anisotropicSelectedParameterDirection J).le_opNorm m).trans
      (mul_le_mul_of_nonneg_left hm (norm_nonneg _))
  calc
    _ ≤ ‖T‖*‖v‖^2 := by
      have hh := (T v).le_opNorm v
      have ht := T.le_opNorm v
      have hp := mul_le_mul_of_nonneg_right ht (norm_nonneg v)
      simpa only [v,pow_two,mul_assoc] using hh.trans hp
    _ ≤ ‖anisotropicEnergyMap D‖^2*(‖anisotropicSelectedParameterDirection J‖*Real.sqrt (n:ℝ))^2 :=
      mul_le_mul hT (pow_le_pow_left₀ (norm_nonneg _) hv 2) (sq_nonneg _) (sq_nonneg _)
    _ = anisotropicProcessEnergyBound D J := by
      rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (n:ℝ))]
      unfold anisotropicProcessEnergyBound
      ring

theorem norm_anisotropicProcessHessianEnergy_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (J : Finset (Fin n)) (q : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicProcessHessianEnergy D μ J q sample‖ ≤ anisotropicProcessEnergyBound D J :=
  quadratic_energy_bound D J _ (norm_anisotropicMeasureTailSecondDifferential_le D μ q _)
    _ (norm_anisotropicMeasureTailMagnetization_le D μ q _)

theorem norm_anisotropicFiniteProcessHessianEnergy_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (q : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicFiniteProcessHessianEnergy D s J q sample‖ ≤ anisotropicProcessEnergyBound D J :=
  quadratic_energy_bound D J _ (norm_anisotropicFiniteTailSecondDifferential_le D s q _)
    _ (norm_anisotropicFiniteTailMagnetization_le D s q _)

theorem measurable_uncurry_anisotropicProcessHessianEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (J : Finset (Fin n)) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicProcessHessianEnergy D μ J z.1 z.2) := by
  have hT := (continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp
    (measurable_fst.prodMk (measurable_uncurry_anisotropicProcessParameter D μ))
  have hv := (anisotropicSelectedParameterDirection J).continuous.measurable.comp
    (measurable_uncurry_anisotropicProcessMagnetization D μ)
  have h := continuous_parameter_quadratic_eval.measurable.comp (hT.prodMk hv)
  simpa only [Function.comp_def,anisotropicProcessHessianEnergy] using h

theorem measurable_uncurry_anisotropicFiniteProcessHessianEnergy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicFiniteProcessHessianEnergy D s J z.1 z.2) := by
  have hT := (continuous_anisotropicFiniteTailSecondDifferential_joint D s).measurable.comp
    (measurable_fst.prodMk (measurable_uncurry_anisotropicFiniteProcessParameter D s))
  have hv := (anisotropicSelectedParameterDirection J).continuous.measurable.comp
    (measurable_uncurry_anisotropicFiniteProcessMagnetization D s)
  have h := continuous_parameter_quadratic_eval.measurable.comp (hT.prodMk hv)
  simpa only [Function.comp_def,anisotropicFiniteProcessHessianEnergy] using h

theorem tendsto_anisotropicFiniteProcessHessianEnergy_moving_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (J : Finset (Fin n)) (sample : AnisotropicDisorderBrownianSample n)
    {qj : ℕ→Paper.Overlap} {q : Paper.Overlap} (hq : Tendsto qj atTop (𝓝 q)) :
    Tendsto (fun j => anisotropicFiniteProcessHessianEnergy D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) J (qj j) sample) atTop
      (𝓝 (anisotropicProcessHessianEnergy D μ J q sample)) := by
  have hT := (tendstoUniformly_anisotropicDyadicTailSecondDifferential D μ).tendsto_comp
    (continuous_anisotropicMeasureTailSecondDifferential_joint D μ).continuousAt
    (hq.prodMk_nhds (tendsto_anisotropicFiniteProcessParameter_moving_time D μ sample hq))
  have hv := (anisotropicSelectedParameterDirection J).continuous.continuousAt.tendsto.comp
    (tendsto_anisotropicFiniteProcessMagnetization_moving_time D μ sample hq)
  have h := continuous_parameter_quadratic_eval.continuousAt.tendsto.comp (hT.prodMk_nhds hv)
  simpa only [Function.comp_def,anisotropicFiniteProcessHessianEnergy,anisotropicProcessHessianEnergy,
    anisotropicDyadicTailPotential,anisotropicFiniteTailPotential] using h

end QuantitativeFollowup
