module
public import QuantitativeFollowup.FollowupCavityRootNormalizerTransport
public import QuantitativeFollowup.FollowupCavityRootNormalizerExpJets

@[expose] public section

/-! Genuine spatial root-density response and Gaussian domination for every
arbitrary profile. The pair directions are transported through actual
unit-coupling coordinates, including vanishing coupling coefficients. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def anisotropicRootDensity (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (g : AnisotropicDisorder n) : ℝ :=
  Real.exp (a*anisotropicMeasurePotential D μ (anisotropicDisorderInjection n g))

theorem anisotropicRootDensity_C2_gaussian_jets (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    ContDiff ℝ 2 (anisotropicRootDensity D μ a) ∧
    ∃ B K : ℝ,0≤B ∧ 0≤K ∧
      (∀g,‖fderiv ℝ (anisotropicRootDensity D μ a) g‖≤B*Real.exp (K*‖g‖)) ∧
      (∀g,‖fderiv ℝ (fderiv ℝ (anisotropicRootDensity D μ a)) g‖≤B*Real.exp (K*‖g‖)) := by
  letI : IsBoundedSMul ℝ (AnisotropicDisorder n) := .of_norm_smul_le norm_smul_le
  letI : ContinuousSMul ℝ (AnisotropicDisorder n) := IsBoundedSMul.continuousSMul
  letI : IsBoundedSMul ℝ (AnisotropicParameter n) := .of_norm_smul_le norm_smul_le
  letI : ContinuousSMul ℝ (AnisotropicParameter n) := IsBoundedSMul.continuousSMul
  let L:=anisotropicDisorderInjection n
  let U:=anisotropicMeasurePotential D μ
  let F:=U∘ L
  have hU : ContDiff ℝ 2 U:=contDiff_two_anisotropicMeasurePotential D μ
  have hF : ContDiff ℝ 2 F:=hU.comp L.contDiff
  have hLip : LipschitzWith (‖anisotropicEnergyMap D‖₊*‖L‖₊) F:=
    (anisotropicMeasurePotential_lipschitz D μ).comp L.lipschitz
  let R : (AnisotropicParameter n→L[ℝ]ℝ)→L[ℝ](AnisotropicDisorder n→L[ℝ]ℝ):=
    (ContinuousLinearMap.compL ℝ (AnisotropicDisorder n) (AnisotropicParameter n) ℝ).flip L
  have hgrad : fderiv ℝ F=R∘((fderiv ℝ U)∘ L) := by
    funext g
    simpa only [ContinuousLinearMap.fderiv,Function.comp_def,R,F,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply] using
      fderiv_comp g (hU.differentiable (by norm_num) _) L.differentiableAt
  have hgradLip : LipschitzWith (‖R‖₊*((‖anisotropicEnergyMap D‖₊^2)*‖L‖₊)) (fderiv ℝ F) := by
    rw [hgrad]
    exact R.lipschitz.comp ((anisotropicMeasurePotential_fderiv_lipschitz D μ).comp L.lipschitz)
  have hH (g : AnisotropicDisorder n) : ‖fderiv ℝ (fderiv ℝ F) g‖≤
      (‖R‖₊*((‖anisotropicEnergyMap D‖₊^2)*‖L‖₊):ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ hgradLip
  refine ⟨?_,?_⟩
  · exact (contDiff_const.mul hF).exp
  · exact exponential_C2_gaussian_jets F hF
      (‖anisotropicEnergyMap D‖₊*‖L‖₊ : ℝ)
      (‖R‖₊*((‖anisotropicEnergyMap D‖₊^2)*‖L‖₊) : ℝ)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))) hLip hH a

theorem anisotropicDisorderInjection_basis (e : AnisotropicCouplingIndex n) :
    anisotropicDisorderInjection n (EuclideanSpace.basisFun (AnisotropicCouplingIndex n) ℝ e)=
      anisotropicCouplingDirection e := by
  classical
  ext i
  cases i <;> simp [anisotropicDisorderInjection,anisotropicCouplingDirection,
    EuclideanSpace.basisFun_apply,PiLp.single_apply]

theorem anisotropicRootDensity_pair_hessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (g : AnisotropicDisorder n)
    (e : AnisotropicCouplingIndex n) :
    fderiv ℝ (fderiv ℝ (anisotropicRootDensity D μ a)) g
      (EuclideanSpace.basisFun (AnisotropicCouplingIndex n) ℝ e)
      (EuclideanSpace.basisFun (AnisotropicCouplingIndex n) ℝ e)=
      anisotropicRootDensity D μ a g*(D.coupling e)^2*
        (a*anisotropicTailPairSecond D μ ⟨0,by norm_num⟩ (anisotropicDisorderInjection n g) e+
          a^2*(anisotropicTailPairResponse D μ ⟨0,by norm_num⟩ (anisotropicDisorderInjection n g) e)^2) := by
  letI : IsBoundedSMul ℝ (AnisotropicParameter n) := .of_norm_smul_le norm_smul_le
  letI : ContinuousSMul ℝ (AnisotropicParameter n) := IsBoundedSMul.continuousSMul
  let U:=anisotropicMeasurePotential D μ
  letI : IsBoundedSMul ℝ (AnisotropicDisorder n) := .of_norm_smul_le norm_smul_le
  letI : ContinuousSMul ℝ (AnisotropicDisorder n) := IsBoundedSMul.continuousSMul
  let L:=anisotropicDisorderInjection n
  let V:=fun P : AnisotropicParameter n=>a*U P
  have hU : ContDiff ℝ 2 U:=contDiff_two_anisotropicMeasurePotential D μ
  have hV : ContDiff ℝ 2 V:=contDiff_const.mul hU
  have hE : ContDiff ℝ 2 (fun P=>Real.exp (V P)):=hV.exp
  have he : anisotropicRootDensity D μ a=(fun P=>Real.exp (V P))∘ L:=rfl
  have hL : fderiv ℝ (⇑L)=fun _=>L:=funext fun P=>L.fderiv
  rw [he,second_fderiv_comp_apply _ _ g _ hE.contDiffAt L.contDiff.contDiffAt]
  simp only [ContinuousLinearMap.fderiv,hL,fderiv_const_apply,ContinuousLinearMap.zero_apply,map_zero,add_zero]
  change exponentialDensityHessian (fun P=>Real.exp (V P)) (L g)
    (L (EuclideanSpace.basisFun (AnisotropicCouplingIndex n) ℝ e))
    (L (EuclideanSpace.basisFun (AnisotropicCouplingIndex n) ℝ e))=_
  rw [anisotropicDisorderInjection_basis,exponentialDensityHessian_exp_potential V hV]
  have hVV : V=a • U:=rfl
  simp only [exponentialDensityHessian,hVV,fderiv_const_smul_field,Pi.smul_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [anisotropicMeasurePotential_pair_first,anisotropicMeasurePotential_pair_second]
  change Real.exp (a*U (L g))*_=_
  dsimp only [anisotropicRootDensity,U,L,Function.comp_apply]
  ring

end QuantitativeFollowup
