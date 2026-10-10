module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestProductMoments
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNoiseRegularity

@[expose] public section

/-! Time jointly measurable genuine restart field derivatives. Fresh-noise
representations and native derivatives are proved identities, never inputs. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped BigOperators
namespace HexagonPaper
variable {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem measurable_cavityRestartNoiseSquareResponse_time_joint (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (i : Fin n) :
    Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>cavityRestartNoiseSquareResponse D μ q z.1 i z.2) := by
  have hm:=measurable_uncurry_cavityRestartNoiseMean D μ q
  have hmc:=(EuclideanSpace.proj i).measurable.comp hm
  have hw : Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>cavityRestartInitialMean D μ q z.2.1):=
    (measurable_cavityRestartInitialMean D μ q).comp measurable_snd.fst
  have hp:=measurable_uncurry_cavityRestartNoiseParameter D μ q
  have hT:=(continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp
    (measurable_fst.prodMk hp)
  have hev : Continuous (fun z : ((AnisotropicParameter n→L[ℝ](AnisotropicParameter n→L[ℝ]ℝ))×
      AnisotropicParameter n)×AnisotropicParameter n=>z.1.1 z.1.2 z.2) :=
    (continuous_fst.fst.clm_apply continuous_fst.snd).clm_apply continuous_snd
  have hH:=hev.measurable.comp ((hT.prodMk ((anisotropicFieldInjection n).measurable.comp hw)).prodMk (measurable_const (a:=anisotropicCoordinateDirection n i)))
  have h1 : Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>cavityRestartNoiseMean D μ q 1 z.2) := by
    simpa only [Function.comp_def] using (measurable_uncurry_cavityRestartNoiseMean D μ q).comp
      ((measurable_const (a:=(1:Paper.Overlap))).prodMk measurable_snd)
  have hI : Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>
      ∫u,cavityRestartNoiseResidual D μ q u z.2 ∂(μ:Measure Paper.Overlap)) := by
    simpa only [Function.comp_def] using ((measurable_uncurry_cavityRestartNoiseResidual D μ q).stronglyMeasurable.integral_prod_left'
      (μ:=(μ:Measure Paper.Overlap))).measurable.comp (measurable_snd (α:=Paper.Overlap))
  have h:=((hmc.const_mul 2).mul hH).add ((hmc.pow_const 2).mul ((hw.inner (𝕜:=ℝ) (h1.sub hw)).sub hI))
  convert h using 1
  funext z
  rfl

private theorem nativeFutureGradient_noise_sum (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r)
    (sample : AnisotropicDisorderBrownianSample n) :
    (fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 q x r)
      (anisotropicMeasureState D μ q sample)) (anisotropicProcessMagnetization D μ q sample)=
      (∑i : Fin n,∫W,cavityRestartNoiseSquareResponse D μ q r i
        ((sample.1,anisotropicMeasureState D μ q sample),W) ∂vectorWienerMeasure n)/(n:ℝ) := by
  classical
  have hs:=HasFDerivAt.fun_sum (u:=Finset.univ) (fun i _=>
    ((contDiff_anisotropicRestartSpinSquare_field D μ sample.1 q r hqr i).differentiable_one
      (anisotropicMeasureState D μ q sample)).hasFDerivAt)
  have hh:=(hs.const_mul ((n:ℝ)⁻¹)).fderiv
  have he : fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 q x r)
      (anisotropicMeasureState D μ q sample)=((n:ℝ)⁻¹) •∑i : Fin n,
      fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ sample.1 q x i r)
        (anisotropicMeasureState D μ q sample) := by
    simpa only [anisotropicRestartMeanSquare,div_eq_mul_inv,mul_comm] using hh
  rw [he]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,smul_eq_mul,div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [←cavityRestartInitialMean_native D μ q sample]
  exact fderiv_anisotropicRestartSpinSquare_field_native_noise D μ sample.1 q r hqr _ i

theorem measurable_cavityZeroRestFutureFieldDerivative_strict_time_joint
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      if q<z.1 then cavityZeroRestFutureFieldDerivative D μ q z.1 z.2 else 0) := by
  classical
  have hX : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      anisotropicMeasureState D μ q z.2) := by
    simpa only [Function.comp_def,Function.uncurry_def] using (measurable_uncurry_anisotropicMeasureState D μ).comp
      (measurable_const.prodMk measurable_snd)
  have hmZ : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      (z.1,(z.2.1,anisotropicMeasureState D μ q z.2))) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk hX)
  have hi (i : Fin n) : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      ∫W,cavityRestartNoiseSquareResponse D μ q z.1 i
        ((z.2.1,anisotropicMeasureState D μ q z.2),W) ∂vectorWienerMeasure n) := by
    have hn : Measurable (fun z : (Paper.Overlap×(AnisotropicDisorder n×Field n))×VectorWienerPath n=>
        cavityRestartNoiseSquareResponse D μ q z.1.1 i (z.1.2,z.2)) := by
      simpa only [Function.comp_def] using (measurable_cavityRestartNoiseSquareResponse_time_joint D μ q i).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    simpa only [Function.comp_def] using (hn.stronglyMeasurable.integral_prod_right' (ν:=vectorWienerMeasure n)).measurable.comp hmZ
  have hs := (Finset.measurable_sum Finset.univ fun i _=>hi i).div_const (n:ℝ)
  have hm : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      if q<z.1 then ((∑i : Fin n,∫W,cavityRestartNoiseSquareResponse D μ q z.1 i
        ((z.2.1,anisotropicMeasureState D μ q z.2),W) ∂vectorWienerMeasure n)/(n:ℝ))/(n:ℝ) else 0) := by
    apply Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    · simpa only [Finset.sum_apply] using hs.div_const (n:ℝ)
    · exact measurable_const
  convert hm using 1
  funext z
  by_cases hz:q<z.1
  · simp only [if_pos hz,cavityZeroRestFutureFieldDerivative]
    rw [nativeFutureGradient_noise_sum D μ q z.1 hz.le]
  · simp only [if_neg hz]

end HexagonPaper
