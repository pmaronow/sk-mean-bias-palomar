module
public import QuantitativeFollowup.AnisotropicMeasureState
public import QuantitativePaper.VectorAdditiveAdapted

@[expose] public section

/-! The actual anisotropic Picard process is adapted to its own initial
Gaussian disorder and its complete raw coordinate Wiener past. Causality of
Picard iteration supplies adaptation, without a filtration regularity premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def anisotropicBrownianRecord (r : ℝ≥0) (sample : AnisotropicDisorderBrownianSample n) :
    AnisotropicDisorder n×Field n := (sample.1,vectorBrownian r sample.2)

theorem measurable_anisotropicBrownianRecord (r : ℝ≥0) :
    Measurable (anisotropicBrownianRecord (n:=n) r) :=
  measurable_fst.prodMk ((measurable_vectorBrownian r).comp measurable_snd)

def anisotropicBrownianFiltration (n : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (AnisotropicDisorderBrownianSample n)) :=
  Filtration.natural anisotropicBrownianRecord
    (fun r=>(measurable_anisotropicBrownianRecord r).stronglyMeasurable)

theorem stronglyAdapted_anisotropicBrownianRecord :
    StronglyAdapted (anisotropicBrownianFiltration n) anisotropicBrownianRecord :=
  Filtration.stronglyAdapted_natural _

theorem stronglyAdapted_anisotropicBrownian :
    StronglyAdapted (anisotropicBrownianFiltration n)
      (fun r sample=>vectorBrownian r sample.2) :=
  fun r=>(stronglyAdapted_anisotropicBrownianRecord (n:=n) r).snd

theorem measurable_anisotropicInitialDisorder (r : ℝ≥0) :
    Measurable[anisotropicBrownianFiltration n r]
      (Prod.fst : AnisotropicDisorderBrownianSample n→AnisotropicDisorder n) :=
  (stronglyAdapted_anisotropicBrownianRecord (n:=n) r).fst.measurable

def anisotropicPastNoise (D : AnisotropicSpinModel n) (q : ℝ≥0) (r : ℝ)
    (sample : AnisotropicDisorderBrownianSample n) : Field n :=
  anisotropicNoiseMap D (vectorBrownian (min r.toNNReal q) sample.2)

theorem continuous_anisotropicPastNoise (D : AnisotropicSpinModel n) (q : ℝ≥0)
    (sample : AnisotropicDisorderBrownianSample n) :
    Continuous (fun r=>anisotropicPastNoise D q r sample) :=
  (anisotropicNoiseMap D).continuous.comp ((continuous_vectorBrownian sample.2).comp
    (continuous_real_toNNReal.min continuous_const))

theorem measurable_anisotropicPastNoise (D : AnisotropicSpinModel n) (q : ℝ≥0) :
    @Measurable (ℝ×AnisotropicDisorderBrownianSample n) (Field n)
      ((inferInstance : MeasurableSpace ℝ).prod (anisotropicBrownianFiltration n q)) inferInstance
      (Function.uncurry (anisotropicPastNoise D q)) := by
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n):=anisotropicBrownianFiltration n q
  apply measurable_uncurry_of_continuous_of_measurable (continuous_anisotropicPastNoise D q)
  intro r
  exact (anisotropicNoiseMap D).continuous.measurable.comp
    (((stronglyAdapted_anisotropicBrownian (n:=n) (min r.toNNReal q)).mono
      ((anisotropicBrownianFiltration n).mono (min_le_right _ _))).measurable)

def anisotropicPastDrivenDrift (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℝ≥0) (sample : AnisotropicDisorderBrownianSample n) (r : ℝ) (y : Field n) : Field n :=
  Paper.parisiCDF μ r • anisotropicVarianceMap D
    (anisotropicMeasureTailMagnetization D μ (projIcc (0 : ℝ) 1 zero_le_one r)
      (anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n
        (y+anisotropicPastNoise D q r sample)))

theorem isBounded_anisotropicPastDrivenDrift (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℝ≥0) (sample : AnisotropicDisorderBrownianSample n) :
    IsBoundedVectorDrift (anisotropicPastDrivenDrift D μ q sample) (anisotropicDriftBound D)
      (anisotropicDriftLipschitz D) where
  measurable := by
    have hq : Measurable (fun z : ℝ×Field n=>projIcc (0 : ℝ) 1 zero_le_one z.1) := by fun_prop
    have hN := (continuous_anisotropicPastNoise D q sample).measurable.comp
      (measurable_fst : Measurable (Prod.fst : ℝ×Field n→ℝ))
    have hP := ((anisotropicFieldInjection n).continuous.measurable.comp
      (measurable_snd.add hN)).const_add (anisotropicDisorderInjection n sample.1)
    have hM := (measurable_anisotropicMeasureTailMagnetization D μ).comp (hq.prodMk hP)
    have h := ((Paper.parisiCDF_monotone μ).measurable.comp measurable_fst).smul
      ((anisotropicVarianceMap D).continuous.measurable.comp hM)
    simpa only [Function.comp_def,anisotropicPastDrivenDrift,Pi.add_apply,Pi.smul_def',Function.uncurry_def] using h
  norm_le := by
    intro r y
    rw [anisotropicPastDrivenDrift,norm_smul,Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ r)]
    simp only [anisotropicDriftBound,NNReal.coe_mul,coe_nnnorm,
      Real.coe_toNNReal (Real.sqrt (n : ℝ)) (Real.sqrt_nonneg (n : ℝ))]
    calc
      _ ≤ Paper.parisiCDF μ r*(‖anisotropicVarianceMap D‖*Real.sqrt (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Paper.parisiCDF_nonneg μ r)
        exact ((anisotropicVarianceMap D).le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (norm_anisotropicMeasureTailMagnetization_le D μ _ _) (norm_nonneg _))
      _ ≤ _ := mul_le_of_le_one_left (by positivity) (Paper.parisiCDF_le_one μ r)
  lipschitz := by
    intro r
    have hP : LipschitzWith ‖anisotropicFieldInjection n‖₊ (fun y : Field n=>
        anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n
          (y+anisotropicPastNoise D q r sample)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_eq_norm,add_sub_add_left_eq_sub,←map_sub,add_sub_add_right_eq_sub,coe_nnnorm]
      exact (anisotropicFieldInjection n).le_opNorm (x-y)
    have hM := (anisotropicMeasureTailMagnetization_lipschitz D μ
      (projIcc (0 : ℝ) 1 zero_le_one r)).comp hP
    have hV := (anisotropicVarianceMap D).lipschitzWith.comp hM
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [anisotropicPastDrivenDrift,anisotropicPastDrivenDrift,dist_smul₀,
      Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ r)]
    calc
      _ ≤ Paper.parisiCDF μ r*((anisotropicDriftLipschitz D : ℝ)*dist x y) := by
        exact mul_le_mul_of_nonneg_left (hV.dist_le_mul x y) (Paper.parisiCDF_nonneg μ r)
      _ ≤ _ := mul_le_of_le_one_left (by positivity) (Paper.parisiCDF_le_one μ r)

theorem anisotropicDriftCorrection_eq_past (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℝ≥0) (hq : q≤1) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicDriftCorrection D μ q sample=
      (VectorIntegralPicard.solution (h:=(0 : Field n)) (T:=1) zero_le_one
        (isBounded_anisotropicPastDrivenDrift D μ q sample)).compProj q := by
  have hfg : ∀r∈Icc (0 : ℝ) q,∀y,anisotropicDrivenDrift D μ sample r y=
      anisotropicPastDrivenDrift D μ q sample r y := by
    intro r hr y
    have hrq : r.toNNReal≤q := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hr.1]
      exact hr.2
    simp only [anisotropicDrivenDrift,anisotropicDrivenParameter,anisotropicPastDrivenDrift,
      anisotropicWienerNoise,anisotropicPastNoise,min_eq_left hrq]
  exact VectorIntegralPicard.solution_causal (x0:=(0 : Field n)) zero_le_one q.coe_nonneg
    (show (q : ℝ)≤1 from hq) (isBounded_anisotropicDrivenDrift D μ sample)
    (isBounded_anisotropicPastDrivenDrift D μ q sample) hfg q ⟨q.coe_nonneg,le_rfl⟩

theorem adapted_anisotropicMeasureState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℝ≥0) (hq : q≤1) :
    Measurable[anisotropicBrownianFiltration n q] (anisotropicMeasureState D μ q) := by
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n):=anisotropicBrownianFiltration n q
  have hG := measurable_anisotropicInitialDisorder (n:=n) q
  have hW := measurable_anisotropicPastNoise D q
  have hf : Measurable (fun z : (ℝ×Field n)×AnisotropicDisorderBrownianSample n=>
      anisotropicPastDrivenDrift D μ q z.2 z.1.1 z.1.2) := by
    unfold anisotropicPastDrivenDrift
    have hP := ((anisotropicDisorderInjection n).continuous.measurable.comp
      (hG.comp measurable_snd)).add ((anisotropicFieldInjection n).continuous.measurable.comp
        (measurable_fst.snd.add (hW.comp (measurable_fst.fst.prodMk measurable_snd))))
    have hq : Measurable (fun z : (ℝ×Field n)×AnisotropicDisorderBrownianSample n=>
        projIcc (0 : ℝ) 1 zero_le_one z.1.1) := by fun_prop
    have hM := (measurable_anisotropicMeasureTailMagnetization D μ).comp (hq.prodMk hP)
    have h := ((Paper.parisiCDF_monotone μ).measurable.comp measurable_fst.fst).smul
      ((anisotropicVarianceMap D).continuous.measurable.comp hM)
    simpa only [Function.comp_def,Function.uncurry_def,Pi.add_apply,Pi.smul_def',Function.uncurry_def] using h
  have hm := VectorIntegralPicard.measurable_solution_compProj (T:=1) zero_le_one (0 : Field n)
    (anisotropicPastDrivenDrift D μ q) (isBounded_anisotropicPastDrivenDrift D μ q) hf (q : ℝ)
  have he : (fun sample=>anisotropicDriftCorrection D μ q sample)=
      (fun sample=>(VectorIntegralPicard.solution (h:=(0 : Field n)) (T:=1) zero_le_one
        (isBounded_anisotropicPastDrivenDrift D μ q sample)).compProj q) :=
    funext (anisotropicDriftCorrection_eq_past D μ q hq)
  have hcor : Measurable (fun sample=>anisotropicDriftCorrection D μ q sample) := by rw [he];exact hm
  have h := hcor.add ((anisotropicNoiseMap D).continuous.measurable.comp
    ((stronglyAdapted_anisotropicBrownian (n:=n) q).measurable))
  change Measurable (fun sample=>anisotropicDriftCorrection D μ q sample+
    anisotropicNoiseMap D (vectorBrownian (q:ℝ).toNNReal sample.2))
  simpa only [Real.toNNReal_coe,Pi.add_def,Function.comp_def] using h

end QuantitativeFollowup
