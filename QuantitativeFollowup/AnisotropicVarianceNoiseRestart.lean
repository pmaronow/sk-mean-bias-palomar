module
public import QuantitativePaper.VectorNoiseRestartConditional
public import QuantitativeFollowup.AnisotropicVarianceRestartMoments

@[expose] public section

/-! A jointly measurable actual anisotropic continuation in its initial
disorder, initial field and fresh continuous Wiener path. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

abbrev AnisotropicRestartNoiseData (n : ℕ) :=
  (AnisotropicDisorder n×Field n)×VectorWienerPath n

def anisotropicRestartNoiseDrift (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (z : AnisotropicRestartNoiseData n) (r : ℝ) (y : Field n) : Field n :=
  vectorContinuousNoiseDrift
    (vectorTimeShiftDriftData (anisotropicWhitenedDriftData D μ z.1.1) (q:ℝ).toNNReal)
      1 ((0,z.1.2),z.2) r y

theorem bounded_anisotropicRestartNoiseDrift (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (z : AnisotropicRestartNoiseData n) :
    IsBoundedVectorDrift (anisotropicRestartNoiseDrift D μ q z)
      (anisotropicWhitenedDriftBound D) (anisotropicWhitenedDriftLip D) :=
  bounded_vectorContinuousNoiseDrift _ 1 _

theorem measurable_anisotropicRestartNoiseDrift (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (fun z : (ℝ×Field n)×AnisotropicRestartNoiseData n=>
      anisotropicRestartNoiseDrift D μ q z.2 z.1.1 z.1.2) := by
  let t : (ℝ×Field n)×AnisotropicRestartNoiseData n→ℝ≥0 :=
    fun z=>(q:ℝ).toNNReal+z.1.1.toNNReal
  have ht : Measurable t := by unfold t;fun_prop
  have hX : Measurable (fun z : (ℝ×Field n)×AnisotropicRestartNoiseData n=>
      z.2.1.2+z.1.2+vectorContinuousNoise z.2.2 z.1.1) :=
    (measurable_snd.fst.snd.add measurable_fst.snd).add
      (continuous_vectorContinuousNoise.measurable.comp (measurable_fst.fst.prodMk measurable_snd.snd))
  have hP : Measurable (fun z : (ℝ×Field n)×AnisotropicRestartNoiseData n=>
      anisotropicDisorderInjection n z.2.1.1+anisotropicFieldInjection n
        (anisotropicNoiseMap D (z.2.1.2+z.1.2+vectorContinuousNoise z.2.2 z.1.1))) :=
    ((anisotropicDisorderInjection n).measurable.comp measurable_snd.fst.fst).add
      ((anisotropicFieldInjection n).measurable.comp ((anisotropicNoiseMap D).measurable.comp hX))
  have hq : Measurable (fun z : (ℝ×Field n)×AnisotropicRestartNoiseData n=>
      projIcc (0:ℝ) 1 zero_le_one (t z)) := by fun_prop
  have hM:=(measurable_anisotropicMeasureTailMagnetization D μ).comp (hq.prodMk hP)
  have hC:=(Paper.parisiCDF_monotone μ).measurable.comp (NNReal.continuous_coe.measurable.comp ht)
  have hh:=hC.smul ((anisotropicNoiseMap D).measurable.comp hM)
  convert hh using 1
  funext z
  simp only [anisotropicRestartNoiseDrift,vectorContinuousNoiseDrift,vectorTimeShiftDriftData,
    anisotropicWhitenedDriftData,anisotropicWhitenedDrift,t,Function.comp_def,one_smul,
    Pi.smul_def']

def anisotropicRestartNoiseStatePath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (z : AnisotropicRestartNoiseData n) (r : ℝ) : Field n :=
  vectorNoiseRestartStatePath (anisotropicWhitenedDriftData D μ z.1.1) 1 q ((0,z.1.2),z.2) r

theorem measurable_uncurry_anisotropicRestartNoiseStatePath (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (fun z : ℝ×AnisotropicRestartNoiseData n=>
      anisotropicRestartNoiseStatePath D μ q z.2 z.1) := by
  have hC:=VectorIntegralPicard.measurable_uncurry_solution_compProj
    (vectorRestartHorizon q).coe_nonneg (0:Field n)
    (anisotropicRestartNoiseDrift D μ q) (bounded_anisotropicRestartNoiseDrift D μ q)
    (measurable_anisotropicRestartNoiseDrift D μ q)
  have hh:=(measurable_snd.fst.snd.add hC).add
    (continuous_vectorContinuousNoise.measurable.comp (measurable_fst.prodMk measurable_snd.snd))
  convert hh using 1
  funext z
  simp only [anisotropicRestartNoiseStatePath,vectorNoiseRestartStatePath,vectorNoiseStatePath,
    one_smul,Pi.add_apply,Function.comp_def]
  rfl

theorem anisotropicRestartNoiseStatePath_canonical (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (r : ℝ≥0) (hr : r≤vectorRestartHorizon q)
    (sample : VectorDisorderBrownianSample n) :
    anisotropicRestartNoiseStatePath D μ q ((g,x),vectorCanonicalBrownianPath sample.2) r=
      anisotropicRestartState D μ g q x r sample :=
  vectorNoiseRestartStatePath_canonical (anisotropicWhitenedDriftData D μ g) 1 q 0 x sample r hr

theorem anisotropicMeasureState_restart (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q r : Paper.Overlap) (hqr : q≤r) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicMeasureState D μ r sample=anisotropicNoiseMap D
      (anisotropicRestartNoiseStatePath D μ q
        ((sample.1,anisotropicInverseNoiseMap D (anisotropicMeasureState D μ q sample)),
          fun i=>canonicalFutureBrownianPath (q:ℝ).toNNReal (sample.2 i))
            ((r:ℝ)-(q:ℝ))) := by
  let p : VectorDisorderBrownianSample n := (0,sample.2)
  let v : ℝ≥0 := ((r:ℝ)-(q:ℝ)).toNNReal
  have hv : v≤vectorRestartHorizon q := Real.toNNReal_le_toNNReal
    (sub_le_sub_right r.property.2 _)
  have htime : (q:ℝ).toNNReal+v=(r:ℝ).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal _ q.property.1,
      Real.coe_toNNReal _ (sub_nonneg.mpr (show (q:ℝ)≤(r:ℝ) from hqr)),
      Real.coe_toNNReal _ r.property.1]
    ring
  have hq1 : (q:ℝ).toNNReal≤1 := by simpa using Real.toNNReal_le_toNNReal q.property.2
  have hr1 : (r:ℝ).toNNReal≤1 := by simpa using Real.toNNReal_le_toNNReal r.property.2
  have he:=vectorAdditiveState_restart (anisotropicWhitenedDriftData D μ sample.1) 1 0 q p v hv
  rw [htime] at he
  have hqstate:=anisotropicMeasureState_eq_whitenedPicard D μ sample.1 p (q:ℝ).toNNReal hq1
  have hrstate:=anisotropicMeasureState_eq_whitenedPicard D μ sample.1 p (r:ℝ).toNNReal hr1
  rw [Real.coe_toNNReal _ q.property.1] at hqstate
  rw [Real.coe_toNNReal _ r.property.1] at hrstate
  change anisotropicMeasureState D μ q sample=_ at hqstate
  change anisotropicMeasureState D μ r sample=_ at hrstate
  rw [hrstate,he]
  rw [hqstate,anisotropicInverseNoiseMap_noise]
  simp only [anisotropicRestartNoiseStatePath,p,vectorFutureBrownianPath,v,
    Real.coe_toNNReal _ (sub_nonneg.mpr (show (q:ℝ)≤(r:ℝ) from hqr))]
  rfl

end QuantitativeFollowup
