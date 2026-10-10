module
public import QuantitativeFollowup.StandardSKAnisotropicRecursion
public import QuantitativePaper.VectorMeasureState

@[expose] public section

/-! The anisotropic and completed SK diffusions are the same pathwise
Picard solution after compressing only the initial disorder coordinates. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
variable {n : ℕ}

def standardSKSampleCompression (sample : AnisotropicDisorderBrownianSample n) :
    VectorDisorderBrownianSample n := (standardSKDisorderCompression sample.1,sample.2)

theorem measurable_standardSKSampleCompression : Measurable (standardSKSampleCompression (n:=n)) :=
  (measurable_standardSKDisorderCompression.comp measurable_fst).prodMk measurable_snd

theorem standardSKAnisotropicNoise (β t : ℝ) (hβ : β ≠ 0) (ht : t<1)
    (r : ℝ) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicWienerNoise (standardSKAnisotropicModel n β t hβ ht) r sample=
      vectorAdditiveNoiseReal (Real.sqrt ((1-t)*β^2)) r (standardSKSampleCompression sample) := by
  ext i
  rfl

theorem standardSKAnisotropicVarianceMap (β t : ℝ) (hβ : β ≠ 0) (ht : t<1)
    (x : Field n) :
    anisotropicVarianceMap (standardSKAnisotropicModel n β t hβ ht) x=((1-t)*β^2) • x := by
  ext i
  rw [anisotropicVarianceMap_apply]
  rfl

theorem standardSKAnisotropicDrivenDrift (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (sample : AnisotropicDisorderBrownianSample n)
    (r : ℝ) (hr : 0≤r) (y : Field n) :
    anisotropicDrivenDrift (standardSKAnisotropicModel n β t hβ ht) μ sample r y=
      vectorNoiseCorrectionDrift (vectorMeasureDriftData μ β t ht.le)
        (vectorAdditiveNoiseReal (Real.sqrt ((1-t)*β^2))) (standardSKSampleCompression sample) r y := by
  unfold anisotropicDrivenDrift anisotropicDrivenParameter
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    standardSKAnisotropicMeasureMagnetization,standardSKAnisotropicVarianceMap,
    standardSKAnisotropicNoise]
  unfold vectorNoiseCorrectionDrift
  change Paper.parisiCDF μ r • (((1-t)*β^2) • _)=
    ((1-t)*β^2*Paper.parisiCDF μ (r.toNNReal:ℝ)) •
      vectorMeasureGradient μ β t (projIcc (0:ℝ) 1 zero_le_one (r.toNNReal:ℝ))
        (standardSKDisorderCompression sample.1)
        (y+vectorAdditiveNoiseReal (Real.sqrt ((1-t)*β^2)) r (standardSKSampleCompression sample))
  rw [Real.coe_toNNReal r hr,smul_smul,mul_comm]

theorem standardSKAnisotropicMeasureState (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (r : ℝ) (hr : r∈Icc (0:ℝ) 1)
    (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicMeasureState (standardSKAnisotropicModel n β t hβ ht) μ r sample=
      vectorMeasureState μ β t ht.le r.toNNReal (standardSKSampleCompression sample) := by
  let d : VectorAdditiveDriftData n:=vectorMeasureDriftData μ β t ht.le
  let σ:=Real.sqrt ((1-t)*β^2)
  let p:=standardSKSampleCompression sample
  let Y:=fun r : ℝ=>(vectorAdditiveCorrection d σ 0 1 p).compProj r
  have hY : Continuous Y := ODE.FunSpace.continuous_compProj _
  have hYe (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
      Y r=0+∫s in 0..r,anisotropicDrivenDrift
        (standardSKAnisotropicModel n β t hβ ht) μ sample s (Y s) := by
    have he:=VectorIntegralPicard.solution_compProj_equation (show (0:ℝ)≤(1:ℝ) by norm_num)
      (isBounded_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
        (continuous_vectorAdditiveNoiseReal σ) p) (x0:=(0:Field n)) hr
    change Y r=0+∫s in 0..r,vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ) p s (Y s) at he
    refine he.trans ?_
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    exact (standardSKAnisotropicDrivenDrift μ β t hβ ht sample s hs.1 (Y s)).symm
  have he:=VectorIntegralPicard.real_solution_unique
    (h:=(0:Field n)) (T:=(1:ℝ)) zero_le_one
    (isBounded_anisotropicDrivenDrift (standardSKAnisotropicModel n β t hβ ht) μ sample)
    Y hY hYe r hr
  have hc : anisotropicDriftCorrection (standardSKAnisotropicModel n β t hβ ht) μ r sample=Y r := he.symm
  unfold anisotropicMeasureState
  rw [hc,standardSKAnisotropicNoise]
  change Y r+vectorAdditiveNoiseReal σ r p=
    (vectorAdditiveCorrection d σ 0 1 p).compProj (r.toNNReal:ℝ)+
      σ • disorderVectorBrownian r.toNNReal p
  rw [Real.coe_toNNReal r hr.1]
  rfl

theorem standardSKAnisotropicProcessMagnetization (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (q : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicProcessMagnetization (standardSKAnisotropicModel n β t hβ ht) μ q sample=
      vectorMeasureGradient μ β t q (standardSKDisorderCompression sample.1)
        (vectorMeasureState μ β t ht.le (q:ℝ).toNNReal (standardSKSampleCompression sample)) := by
  unfold anisotropicProcessMagnetization anisotropicProcessParameter
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    standardSKAnisotropicMeasureMagnetization,standardSKAnisotropicMeasureState μ β t hβ ht q q.property]

end QuantitativeFollowup
