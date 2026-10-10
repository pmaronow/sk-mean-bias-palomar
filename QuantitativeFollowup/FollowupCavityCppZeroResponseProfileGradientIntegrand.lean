module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileIntegral
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePhysicalIdentity

@[expose] public section

/-! Measurability and a model-uniform bound for the literal native
restart-field derivative contracted with the actual earlier mean.
The integrand is identified with a genuine fresh-Wiener noise integral. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 650000
set_option maxSynthPendingDepth 128

private def coordinateIntegrand (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q r : Paper.Overlap) (i : Fin n) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  (fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ sample.1 q x i r)
    (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample)

private theorem coordinateIntegrand_noise (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) :
    coordinateIntegrand D μ q r i sample=
      ∫W,cavityRestartNoiseSquareResponse D μ q r i
        ((sample.1,anisotropicMeasureState D μ q sample),W) ∂vectorWienerMeasure n := by
  unfold coordinateIntegrand
  rw [←cavityRestartInitialMean_native D μ q sample]
  exact fderiv_anisotropicRestartSpinSquare_field_native_noise D μ sample.1 q r hqr _ i

private theorem coordinateIntegrand_measurable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r) (i : Fin n) :
    Measurable (coordinateIntegrand D μ q r i) := by
  have hX := (measurable_uncurry_anisotropicMeasureState D μ).comp
    ((measurable_const (a:=(q:ℝ))).prodMk
      (measurable_id (α:=AnisotropicDisorderBrownianSample n)))
  dsimp only [Function.comp_def] at hX
  have hmZ := measurable_fst.prodMk hX
  have hm := ((measurable_cavityRestartNoiseSquareResponse D μ q r i).stronglyMeasurable.integral_prod_right'
    (ν:=vectorWienerMeasure n)).measurable.comp hmZ
  have he : coordinateIntegrand D μ q r i=fun sample=>
      ∫W,cavityRestartNoiseSquareResponse D μ q r i
        ((sample.1,anisotropicMeasureState D μ q sample),W) ∂vectorWienerMeasure n :=
    funext (coordinateIntegrand_noise D μ q r hqr i)
  rw [he]
  exact hm

private theorem coordinateIntegrand_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖coordinateIntegrand D μ q r i sample‖≤cavityRestartNoiseSquareBound D i := by
  rw [coordinateIntegrand_noise D μ q r hqr i]
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=vectorWienerMeasure n)
      (.of_forall fun W=>norm_cavityRestartNoiseSquareResponse_le D μ q r i _)

private theorem meanIntegrand_sum (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r)
    (sample : AnisotropicDisorderBrownianSample n) :
    (fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 q x r)
      (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample)=
      (∑i : Fin n,coordinateIntegrand D μ q r i sample)/(n:ℝ) := by
  classical
  have hs := HasFDerivAt.fun_sum (u:=Finset.univ) (fun i _=>
    ((contDiff_anisotropicRestartSpinSquare_field D μ sample.1 q r hqr i).differentiable_one
      (anisotropicMeasureState D μ q sample)).hasFDerivAt)
  have hh := (hs.const_mul ((n:ℝ)⁻¹)).fderiv
  have he : fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 q x r)
      (anisotropicMeasureState D μ q sample)=((n:ℝ)⁻¹) •∑i : Fin n,
      fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ sample.1 q x i r)
        (anisotropicMeasureState D μ q sample) := by
    simpa only [anisotropicRestartMeanSquare,div_eq_mul_inv,mul_comm] using hh
  rw [he]
  simp only [coordinateIntegrand,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    smul_eq_mul,div_eq_mul_inv,mul_comm]

def cavityNativeFutureGradientBound (D : AnisotropicSpinModel n) : ℝ :=
  (∑i : Fin n,cavityRestartNoiseSquareBound D i)/|(n:ℝ)|

theorem cavityNativeFutureGradientBound_nonneg (D : AnisotropicSpinModel n) :
    0≤cavityNativeFutureGradientBound D := by
  unfold cavityNativeFutureGradientBound cavityRestartNoiseSquareBound cavityRestartNoiseHessianBound
  positivity

theorem measurable_cavityNativeFutureGradientIntegrand (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r) :
    Measurable (fun sample : AnisotropicDisorderBrownianSample n=>
      (fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 q x r)
        (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample)) := by
  simp_rw [meanIntegrand_sum D μ q r hqr]
  exact (Finset.measurable_sum _ fun i _=>coordinateIntegrand_measurable D μ q r hqr i).div_const _

theorem norm_cavityNativeFutureGradientIntegrand_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖(fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 q x r)
      (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample)‖≤
      cavityNativeFutureGradientBound D := by
  rw [meanIntegrand_sum D μ q r hqr,norm_div]
  change ‖∑i : Fin n,coordinateIntegrand D μ q r i sample‖/|(n:ℝ)|≤
    (∑i : Fin n,cavityRestartNoiseSquareBound D i)/|(n:ℝ)|
  exact div_le_div_of_nonneg_right
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>coordinateIntegrand_bound D μ q r hqr i sample))
    (abs_nonneg _)

end QuantitativeFollowup
