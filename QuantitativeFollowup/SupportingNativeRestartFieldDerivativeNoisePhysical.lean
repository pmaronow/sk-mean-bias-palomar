module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNoiseIntegral
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePhysicalDefinition

@[expose] public section

/-! Whole-past transport of the native restart derivative to its genuine
physical Hessian and strict-future score under the actual tilted sample law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

def cavitySignedResponseWienerScore (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  inner ℝ (anisotropicProcessMagnetization D μ q sample)
    (anisotropicProcessMagnetization D μ 1 sample-anisotropicProcessMagnetization D μ q sample)-
  ∫u,if q<u then inner ℝ (anisotropicProcessMagnetization D μ q sample)
    (anisotropicProcessMagnetization D μ u sample-anisotropicProcessMagnetization D μ q sample)
    else 0 ∂(μ:Measure Paper.Overlap)

def cavitySignedResponseNativeSquareResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q r : Paper.Overlap) (i : Fin n) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  2*(anisotropicProcessMagnetization D μ r sample i)*
    (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ r)) (anisotropicProcessParameter D μ r sample)
      (anisotropicFieldInjection n (anisotropicProcessMagnetization D μ q sample)) (anisotropicCoordinateDirection n i))+
  (anisotropicProcessMagnetization D μ r sample i)^2*cavitySignedResponseWienerScore D μ q sample

theorem cavityRestartInitialMean_native (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    cavityRestartInitialMean D μ q (sample.1,anisotropicMeasureState D μ q sample)=
      anisotropicProcessMagnetization D μ q sample := rfl

theorem cavityRestartNoiseSquareResponse_native (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) :
    cavityRestartNoiseSquareResponse D μ q r i
      ((sample.1,anisotropicMeasureState D μ q sample),anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal sample)=
      cavitySignedResponseNativeSquareResponse D μ q r i sample := by
  have hp (u : Paper.Overlap) (hqu : q≤u) : cavityRestartNoiseParameter D μ q u
      ((sample.1,anisotropicMeasureState D μ q sample),anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal sample)=
      anisotropicProcessParameter D μ u sample := by
    have he : anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal sample=
        anisotropicFutureBrownianPath (q:ℝ).toNNReal sample := rfl
    rw [he]
    exact cavityRestartNoiseParameter_native D μ q u hqu sample
  have hm (u : Paper.Overlap) (hqu : q≤u) : cavityRestartNoiseMean D μ q u
      ((sample.1,anisotropicMeasureState D μ q sample),anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal sample)=
      anisotropicProcessMagnetization D μ u sample := by
    unfold cavityRestartNoiseMean
    rw [hp u hqu]
    rfl
  have hr (u : Paper.Overlap) : cavityRestartNoiseResidual D μ q u
      ((sample.1,anisotropicMeasureState D μ q sample),anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal sample)=
      if q<u then inner ℝ (anisotropicProcessMagnetization D μ q sample)
        (anisotropicProcessMagnetization D μ u sample-anisotropicProcessMagnetization D μ q sample) else 0 := by
    unfold cavityRestartNoiseResidual
    rw [cavityRestartInitialMean_native]
    by_cases hqu : q<u
    · rw [if_pos hqu,if_pos hqu,hm u hqu.le]
    · rw [if_neg hqu,if_neg hqu]
  unfold cavityRestartNoiseSquareResponse cavitySignedResponseNativeSquareResponse cavitySignedResponseWienerScore
  rw [hm r hqr,hm 1 q.property.2,hp r hqr,cavityRestartInitialMean_native]
  simp_rw [hr]

theorem integral_native_restart_coordinate_field_score (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap) (hqr : q≤r) (i : Fin n) :
    (∫sample,(fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ sample.1 q x i r)
      (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample)
        ∂anisotropicMeasureSampleLaw D μ a)=
      ∫sample,cavitySignedResponseNativeSquareResponse D μ q r i sample ∂anisotropicMeasureSampleLaw D μ a := by
  let Z:=fun sample : AnisotropicDisorderBrownianSample n=>(sample.1,anisotropicMeasureState D μ q sample)
  have hq1 : (q:ℝ).toNNReal≤1:=by simpa using Real.toNNReal_le_toNNReal q.property.2
  have hx : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample=>anisotropicMeasureState D μ q sample) := by
    simpa only [Real.coe_toNNReal _ q.property.1] using adapted_anisotropicMeasureState D μ (q:ℝ).toNNReal hq1
  have hZ : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Z:=
    (measurable_anisotropicInitialDisorder _).prodMk hx
  have he sample : (fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ sample.1 q x i r)
      (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample)=
      ∫V,cavityRestartNoiseSquareResponse D μ q r i (Z sample,V) ∂vectorWienerMeasure n := by
    rw [←cavityRestartInitialMean_native D μ q sample]
    exact fderiv_anisotropicRestartSpinSquare_field_native_noise D μ sample.1 q r hqr _ i
  simp_rw [he]
  rw [anisotropic_full_past_noise_integral D μ a (q:ℝ).toNNReal Z hZ
    (cavityRestartNoiseSquareResponse D μ q r i) (measurable_cavityRestartNoiseSquareResponse D μ q r i)
    (cavityRestartNoiseSquareBound D i) (norm_cavityRestartNoiseSquareResponse_le D μ q r i)]
  exact integral_congr_ae (.of_forall fun sample=>cavityRestartNoiseSquareResponse_native D μ q r hqr i sample)

end QuantitativeFollowup
