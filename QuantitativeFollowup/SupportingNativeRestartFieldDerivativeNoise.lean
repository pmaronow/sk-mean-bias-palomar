module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeMeanScore
public import QuantitativeFollowup.AnisotropicProcessEnergy
public import QuantitativeFollowup.AnisotropicRecordedProfileFuture

@[expose] public section

/-! Genuine continuous-noise realizations of the restarted field score.
Both canonical fresh Wiener samples and the native whole future Brownian
path identify the same actual Picard continuation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 180000
set_option maxSynthPendingDepth 128

def cavityRestartNoiseParameter (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q r : Paper.Overlap) (z : AnisotropicRestartNoiseData n) : AnisotropicParameter n :=
  anisotropicDisorderInjection n z.1.1+anisotropicUnitInput D
    (anisotropicRestartNoiseStatePath D μ q
      ((z.1.1,anisotropicInverseNoiseMap D z.1.2),z.2) ((r:ℝ)-(q:ℝ)))

theorem measurable_uncurry_cavityRestartNoiseParameter (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>cavityRestartNoiseParameter D μ q z.1 z.2) := by
  have ht : Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>
      ((z.1:ℝ)-(q:ℝ),((z.2.1.1,anisotropicInverseNoiseMap D z.2.1.2),z.2.2))) := by fun_prop
  have hX:=(measurable_uncurry_anisotropicRestartNoiseStatePath D μ q).comp ht
  dsimp only [Function.comp_def] at hX
  have hh:=((anisotropicDisorderInjection n).measurable.comp measurable_snd.fst.fst).add
    ((anisotropicUnitInput D).measurable.comp hX)
  change Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>
    anisotropicDisorderInjection n z.2.1.1+anisotropicUnitInput D
      (anisotropicRestartNoiseStatePath D μ q
        ((z.2.1.1,anisotropicInverseNoiseMap D z.2.1.2),z.2.2) ((z.1:ℝ)-(q:ℝ))))
  convert hh using 1
  funext z
  rfl


theorem cavityRestartNoiseParameter_canonical (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap) (hqr : q≤r)
    (x : Field n) (sample : VectorDisorderBrownianSample n) :
    cavityRestartNoiseParameter D μ q r ((g,x),vectorCanonicalBrownianPath sample.2)=
      anisotropicRestartPhysicalParameter D μ g q x ((r:ℝ)-(q:ℝ)).toNNReal sample := by
  have hv : ((r:ℝ)-(q:ℝ)).toNNReal≤vectorRestartHorizon q :=
    Real.toNNReal_le_toNNReal (sub_le_sub_right r.property.2 _)
  have h:=anisotropicRestartNoiseStatePath_canonical D μ g q (anisotropicInverseNoiseMap D x)
    ((r:ℝ)-(q:ℝ)).toNNReal hv sample
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr (show (q:ℝ)≤(r:ℝ) from hqr))] at h
  change anisotropicDisorderInjection n g+anisotropicUnitInput D
    (anisotropicRestartNoiseStatePath D μ q ((g,anisotropicInverseNoiseMap D x),vectorCanonicalBrownianPath sample.2) ((r:ℝ)-(q:ℝ)))=
    anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicRestartState D μ g q (anisotropicInverseNoiseMap D x) ((r:ℝ)-(q:ℝ)).toNNReal sample)
  exact congrArg (fun y : Field n=>anisotropicDisorderInjection n g+anisotropicUnitInput D y) h

theorem cavityRestartNoiseParameter_native (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r)
    (sample : AnisotropicDisorderBrownianSample n) :
    cavityRestartNoiseParameter D μ q r
      ((sample.1,anisotropicMeasureState D μ q sample),anisotropicFutureBrownianPath (q:ℝ).toNNReal sample)=
      anisotropicProcessParameter D μ r sample := by
  have h:=anisotropicMeasureState_restart D μ q r hqr sample
  change anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n
    (anisotropicNoiseMap D (anisotropicRestartNoiseStatePath D μ q
      ((sample.1,anisotropicInverseNoiseMap D (anisotropicMeasureState D μ q sample)),
        anisotropicFutureBrownianPath (q:ℝ).toNNReal sample) ((r:ℝ)-(q:ℝ))))=
    anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n (anisotropicMeasureState D μ r sample)
  exact congrArg (fun y : Field n=>anisotropicDisorderInjection n sample.1+anisotropicFieldInjection n y) h.symm


def cavityRestartNoiseMean (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q r : Paper.Overlap) (z : AnisotropicRestartNoiseData n) : Field n :=
  anisotropicMeasureTailMagnetization D μ r (cavityRestartNoiseParameter D μ q r z)

def cavityRestartInitialMean (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (z : AnisotropicDisorder n×Field n) : Field n :=
  anisotropicMeasureTailMagnetization D μ q
    (anisotropicDisorderInjection n z.1+anisotropicFieldInjection n z.2)

def cavityRestartNoiseResidual (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q r : Paper.Overlap) (z : AnisotropicRestartNoiseData n) : ℝ :=
  if q<r then inner ℝ (cavityRestartInitialMean D μ q z.1)
    (cavityRestartNoiseMean D μ q r z-cavityRestartInitialMean D μ q z.1) else 0

def cavityRestartNoiseSquareResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q r : Paper.Overlap) (i : Fin n) (z : AnisotropicRestartNoiseData n) : ℝ :=
  2*(cavityRestartNoiseMean D μ q r z i)*
    (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ r))
      (cavityRestartNoiseParameter D μ q r z)
      (anisotropicFieldInjection n (cavityRestartInitialMean D μ q z.1)) (anisotropicCoordinateDirection n i))+
  (cavityRestartNoiseMean D μ q r z i)^2*
    (inner ℝ (cavityRestartInitialMean D μ q z.1)
      (cavityRestartNoiseMean D μ q 1 z-cavityRestartInitialMean D μ q z.1)-
      ∫u,cavityRestartNoiseResidual D μ q u z ∂(μ:Measure Paper.Overlap))

theorem cavityRestartSpinVector_initial (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    cavityRestartSpinVector D μ g q x sample q=cavityRestartInitialMean D μ q (g,x) := by
  simp only [cavityRestartSpinVector,sub_self,Real.toNNReal_zero,anisotropicRestartPhysicalParameter,
    anisotropicRestartState_zero,anisotropicUnitInput,ContinuousLinearMap.comp_apply,anisotropicNoiseMap_inverseNoise,
    cavityRestartInitialMean]

theorem cavityRestartNoiseSquareResponse_canonical (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap) (hqr : q≤r)
    (x : Field n) (i : Fin n) (sample : VectorDisorderBrownianSample n) :
    cavityRestartNoiseSquareResponse D μ q r i ((g,x),vectorCanonicalBrownianPath sample.2)=
      cavityRestartSquareFieldResponse D μ g q x (cavityRestartInitialMean D μ q (g,x)) r sample i := by
  have hm (u : Paper.Overlap) (hqu : q≤u) : cavityRestartNoiseMean D μ q u
      ((g,x),vectorCanonicalBrownianPath sample.2)=cavityRestartSpinVector D μ g q x sample u := by
    unfold cavityRestartNoiseMean cavityRestartSpinVector
    rw [cavityRestartNoiseParameter_canonical D μ g q u hqu]
  have hr (u : Paper.Overlap) : cavityRestartNoiseResidual D μ q u
      ((g,x),vectorCanonicalBrownianPath sample.2)=
      cavityRestartStrictFutureResidual D μ g q x (cavityRestartInitialMean D μ q (g,x)) sample u := by
    rw [cavityRestartStrictFutureResidual_eq]
    unfold cavityRestartNoiseResidual
    by_cases hqu : q<u
    · rw [if_pos hqu,if_pos hqu,hm u hqu.le,cavityRestartSpinVector_initial]
    · rw [if_neg hqu,if_neg hqu]
  unfold cavityRestartNoiseSquareResponse cavityRestartSquareFieldResponse cavityRestartFieldHessian
  rw [hm r hqr,hm 1 q.property.2,cavityRestartNoiseParameter_canonical D μ g q r hqr,
    cavityRestartSpinVector_initial]
  simp_rw [hr]

end QuantitativeFollowup
