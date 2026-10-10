module
public import FourPapersCommon.FiniteStateGaussianConvolutionCovariance
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

/-! Genuine composition of normalized same-mass Gaussian transitions. The
child potential is normalized before the outer transition; the two normalizers
cancel pointwise, leaving the single independent-input exponential tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace FourPapersCommon
variable {S I J K : Type*} [Fintype S] [Fintype I] [Fintype J] [Fintype K]
set_option maxHeartbeats 1500000

theorem integral_finiteStateGaussianStepLaw_gaussian (a : ℝ)
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (F G : FiniteStateField S→ℝ) (hF : Measurable F) (hG : Measurable G) (H : FiniteStateField S) :
    (∫y,G y ∂finiteStateGaussianStepLaw a L F H)=
      (∫z,Real.exp (a*F (H+L z))*G (H+L z) ∂stdGaussian (FiniteStateGaussianInput I))/
      (∫z,Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I)) := by
  rw [finiteStateGaussianStepLaw_eq_map_tilted a L F hF H,
    integral_map (by fun_prop : Measurable (fun z=>H+L z)).aemeasurable hG.aestronglyMeasurable,
    integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]

theorem finiteStateGaussianStepLaw_convolution_mean (a : ℝ) (ha : 0 ≤ a)
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F)
    (G : FiniteStateField S→ℝ) (hG : Measurable G) (B : ℝ) (hb : ∀y,‖G y‖ ≤ B)
    (H : FiniteStateField S) :
    (∫y,(∫w,G w ∂finiteStateGaussianStepLaw a M F y)
      ∂finiteStateGaussianStepLaw a L (finiteStateGaussianStep a M F) H)=
      ∫y,G y ∂finiteStateGaussianStepLaw a (finiteStateGaussianSumMap L M) F H := by
  let U:=finiteStateGaussianStep a M F
  let Q:=fun y=>∫w,G w ∂finiteStateGaussianStepLaw a M F y
  have hFc:=hF.continuous
  have hFm:=hFc.measurable
  have hUm : Measurable U:=(finiteStateGaussianStep_lipschitz F hF a ha M).continuous.measurable
  have hQm : Measurable Q := by
    have h:=(hG.stronglyMeasurable.integral_kernel
      (κ:=finiteStateGaussianStepKernel a M F)).measurable
    simpa only [finiteStateGaussianStepKernel_apply a M F hFm,Q] using h
  have hp:=integrable_exp_finiteStateGaussian_product_lipschitz L M F hF H a
  have hnum : Integrable (fun z : FiniteStateGaussianInput I×FiniteStateGaussianInput J=>
      Real.exp (a*F (H+L z.1+M z.2))*G (H+L z.1+M z.2))
      ((stdGaussian (FiniteStateGaussianInput I)).prod (stdGaussian (FiniteStateGaussianInput J))) := by
    apply (hp.mul_const B).mono' (by fun_prop)
    exact .of_forall fun z=>by
      rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le
  have hn := (hasLaw_finiteGaussianSplit (I:=I) (J:=J)).integral_comp
    (f:=fun z : FiniteStateGaussianInput I×FiniteStateGaussianInput J=>
      Real.exp (a*F (H+L z.1+M z.2))*G (H+L z.1+M z.2)) (by fun_prop)
  have hden : (∫z,Real.exp (a*U (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I))=
      ∫z,Real.exp (a*F (H+finiteStateGaussianSumMap L M z))
        ∂stdGaussian (FiniteStateGaussianInput (I⊕J)) := by
    rw [←exp_mul_finiteStateGaussianStep a L U
      (finiteStateGaussianStep_lipschitz F hF a ha M),
      finiteStateGaussianStep_convolution a L M F hF H,
      exp_mul_finiteStateGaussianStep a (finiteStateGaussianSumMap L M) F hF H]
  have hcancel (z : FiniteStateGaussianInput I) : Real.exp (a*U (H+L z))*Q (H+L z)=
      ∫w,Real.exp (a*F (H+L z+M w))*G (H+L z+M w)
        ∂stdGaussian (FiniteStateGaussianInput J) := by
    rw [show Q (H+L z)=∫w,G w ∂finiteStateGaussianStepLaw a M F (H+L z) from rfl,
      integral_finiteStateGaussianStepLaw_gaussian a M F G hFm hG,
      exp_mul_finiteStateGaussianStep a M F hF]
    exact mul_div_cancel₀ _ (integral_exp_pos
      (integrable_exp_finiteStateGaussian_lipschitz F hF M (H+L z) a)).ne'
  rw [show (∫y,(∫w,G w ∂finiteStateGaussianStepLaw a M F y)
      ∂finiteStateGaussianStepLaw a L U H)=∫y,Q y ∂finiteStateGaussianStepLaw a L U H from rfl,
    integral_finiteStateGaussianStepLaw_gaussian a L U Q hUm hQm,
    integral_finiteStateGaussianStepLaw_gaussian a (finiteStateGaussianSumMap L M) F G hFm hG,
    hden]
  congr 1
  simp_rw [hcancel]
  rw [←integral_prod _ hnum,←hn]
  simp only [Function.comp_def,finiteGaussianSplit,finiteStateGaussianSumMap_apply,add_assoc]

theorem finiteStateGaussianStepKernel_convolution_mean (a : ℝ) (ha : 0 ≤ a)
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F)
    (G : FiniteStateField S→ℝ) (hG : Measurable G) (B : ℝ) (hb : ∀y,‖G y‖ ≤ B)
    (H : FiniteStateField S) :
    (∫y,(∫w,G w ∂finiteStateGaussianStepKernel a M F y)
      ∂finiteStateGaussianStepKernel a L (finiteStateGaussianStep a M F) H)=
      ∫y,G y ∂finiteStateGaussianStepKernel a (finiteStateGaussianSumMap L M) F H := by
  simp_rw [finiteStateGaussianStepKernel_apply a M F hF.continuous.measurable,
    finiteStateGaussianStepKernel_apply a L _
      (finiteStateGaussianStep_lipschitz F hF a ha M).continuous.measurable,
    finiteStateGaussianStepKernel_apply a (finiteStateGaussianSumMap L M) F hF.continuous.measurable]
  exact finiteStateGaussianStepLaw_convolution_mean a ha L M F hF G hG B hb H

theorem finiteStateGaussianStepKernel_convolution (a : ℝ) (ha : 0 ≤ a)
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F) :
    finiteStateGaussianStepKernel a M F ∘ₖ
        finiteStateGaussianStepKernel a L (finiteStateGaussianStep a M F)=
      finiteStateGaussianStepKernel a (finiteStateGaussianSumMap L M) F := by
  haveI:=isMarkovKernel_finiteStateGaussianStepKernel a M F hF
  haveI:=isMarkovKernel_finiteStateGaussianStepKernel a L (finiteStateGaussianStep a M F)
    (finiteStateGaussianStep_lipschitz F hF a ha M)
  haveI:=isMarkovKernel_finiteStateGaussianStepKernel a (finiteStateGaussianSumMap L M) F hF
  apply Kernel.ext
  intro H
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro G
  have hi : Integrable G ((finiteStateGaussianStepKernel a M F ∘ₖ
      finiteStateGaussianStepKernel a L (finiteStateGaussianStep a M F)) H) :=
    (integrable_const ‖G‖).mono' G.continuous.aestronglyMeasurable
      (.of_forall fun y=>G.norm_coe_le_norm y)
  rw [Kernel.integral_comp hi]
  exact finiteStateGaussianStepKernel_convolution_mean a ha L M F hF G G.continuous.measurable
    ‖G‖ G.norm_coe_le_norm H

section Covariance
variable [DecidableEq S] [DecidableEq I] [DecidableEq J] [DecidableEq K]

theorem finiteStateGaussianStepKernel_convolution_of_covariance (a : ℝ) (ha : 0 ≤ a)
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (A : FiniteStateGaussianInput K→L[ℝ]FiniteStateField S)
    (hcov : ∀σ τ,finiteStateSpectralCovariance A σ τ=
      finiteStateSpectralCovariance L σ τ+finiteStateSpectralCovariance M σ τ)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F) :
    finiteStateGaussianStepKernel a M F ∘ₖ
        finiteStateGaussianStepKernel a L (finiteStateGaussianStep a M F)=
      finiteStateGaussianStepKernel a A F := by
  rw [finiteStateGaussianStepKernel_convolution a ha L M F hF]
  apply Kernel.ext
  intro H
  simp only [finiteStateGaussianStepKernel_apply a _ F hF.continuous.measurable]
  apply finiteStateGaussianStepLaw_eq_of_spectral_covariance _ A _ a F H
  intro σ τ
  rw [finiteStateSpectralCovariance_sumMap,hcov]

theorem finiteStateGaussianStepLaw_convolution_mean_of_covariance (a : ℝ) (ha : 0 ≤ a)
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (A : FiniteStateGaussianInput K→L[ℝ]FiniteStateField S)
    (hcov : ∀σ τ,finiteStateSpectralCovariance A σ τ=
      finiteStateSpectralCovariance L σ τ+finiteStateSpectralCovariance M σ τ)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F)
    (G : FiniteStateField S→ℝ) (hG : Measurable G) (B : ℝ) (hb : ∀y,‖G y‖ ≤ B)
    (H : FiniteStateField S) :
    (∫y,(∫w,G w ∂finiteStateGaussianStepLaw a M F y)
      ∂finiteStateGaussianStepLaw a L (finiteStateGaussianStep a M F) H)=
      ∫y,G y ∂finiteStateGaussianStepLaw a A F H := by
  rw [finiteStateGaussianStepLaw_convolution_mean a ha L M F hF G hG B hb H,
    finiteStateGaussianStepLaw_eq_of_spectral_covariance _ A _ a F H]
  intro σ τ
  rw [finiteStateSpectralCovariance_sumMap,hcov]

end Covariance
end FourPapersCommon
