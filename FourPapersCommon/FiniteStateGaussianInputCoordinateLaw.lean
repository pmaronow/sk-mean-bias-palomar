module
public import FourPapersCommon.FiniteStateGaussianInputCoordinateIBP
public import FourPapersCommon.GenericFiniteStateCascadeTiltIntegrability

@[expose] public section

/-! Integrability and literal normalized-noise-law form of the coordinate
Stein identity. The probability measure is the actual Gaussian exponential
tilt of the actual finite-state potential. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {S I : Type*} [Fintype S] [Fintype I]

theorem continuous_finiteStateGaussianInput_coordinate (i : Fin (Fintype.card I)) :
    Continuous (fun z : FiniteStateGaussianInput I=>(finiteStateGaussianBasis I).repr z i):=
  (PiLp.continuous_apply 2 (fun _ : Fin (Fintype.card I)=>ℝ) i).comp
    (finiteStateGaussianBasis I).repr.continuous

theorem abs_finiteStateGaussianInput_coordinate_le (i : Fin (Fintype.card I))
    (z : FiniteStateGaussianInput I) : |(finiteStateGaussianBasis I).repr z i|≤‖z‖ := by
  simpa only [Real.norm_eq_abs,LinearIsometryEquiv.norm_map] using
    PiLp.norm_apply_le ((finiteStateGaussianBasis I).repr z) i

theorem integrable_finiteStateGaussianInput_coordinate_tilt
    (mass : ℝ) (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : ℝ≥0} (hF : LipschitzWith C F)
    (H : FiniteStateField S) (i : Fin (Fintype.card I)) :
    Integrable (fun z=>(finiteStateGaussianBasis I).repr z i)
      ((stdGaussian (FiniteStateGaussianInput I)).tilted (fun z=>mass*F (H+L z))) := by
  exact integrable_finiteStateGaussian_tilt_linear_growth mass L F hF H _
    (continuous_finiteStateGaussianInput_coordinate i).measurable 0 1
    (fun z=>by simpa only [NNReal.coe_zero,NNReal.coe_one,zero_add,one_mul] using
      abs_finiteStateGaussianInput_coordinate_le i z)

theorem integrable_finiteStateGaussianInput_coordinate_derivative_tilt
    (mass : ℝ) (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) (hF : ContDiff ℝ 2 F)
    (C : ℝ≥0) (hC : ∀H,‖fderiv ℝ F H‖≤C)
    (H K : FiniteStateField S) (i : Fin (Fintype.card I)) :
    Integrable (fun z=>(finiteStateGaussianBasis I).repr z i*fderiv ℝ F (H+L z) K)
      ((stdGaussian (FiniteStateGaussianInput I)).tilted (fun z=>mass*F (H+L z))) := by
  have hF1 : ContDiff ℝ 1 F:=hF.of_le (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ F):=hF.fderiv_right (by norm_num)
  have hLip : LipschitzWith C F:=lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y=>NNReal.coe_le_coe.mp (hC y))
  have hm : Measurable (fun z=>(finiteStateGaussianBasis I).repr z i*fderiv ℝ F (H+L z) K):=
    ((continuous_finiteStateGaussianInput_coordinate i).mul
      ((hD.continuous.comp (continuous_const.add L.continuous)).clm_apply continuous_const)).measurable
  apply integrable_finiteStateGaussian_tilt_linear_growth mass L F hLip H _ hm 0 (C*‖K‖₊)
  intro z
  simp only [NNReal.coe_zero,NNReal.coe_mul,coe_nnnorm,zero_add,abs_mul]
  have hG : |fderiv ℝ F (H+L z) K|≤C*‖K‖:=by
    exact ((fderiv ℝ F (H+L z)).le_opNorm K).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  exact (mul_le_mul (abs_finiteStateGaussianInput_coordinate_le i z) hG
    (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)

theorem finiteStateGaussianInput_coordinate_ibp_law
    (mass : ℝ) (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀H,‖fderiv ℝ F H‖≤C)
    (hB : ∀H,‖fderiv ℝ (fderiv ℝ F) H‖≤B)
    (H K : FiniteStateField S) (i : Fin (Fintype.card I)) :
    (∫z,(finiteStateGaussianBasis I).repr z i*fderiv ℝ F (H+L z) K
      ∂(stdGaussian (FiniteStateGaussianInput I)).tilted (fun z=>mass*F (H+L z)))=
    ∫y,fderiv ℝ (fderiv ℝ F) y (L (finiteStateGaussianBasis I i)) K+
      mass*fderiv ℝ F y K*fderiv ℝ F y (L (finiteStateGaussianBasis I i))
      ∂finiteStateGaussianStepLaw mass L F H := by
  have hD : ContDiff ℝ 1 (fderiv ℝ F):=hF.fderiv_right (by norm_num)
  have hLm:=L.continuous
  have hleft : Measurable (fun z=>(finiteStateGaussianBasis I).repr z i*fderiv ℝ F (H+L z) K):=
    ((continuous_finiteStateGaussianInput_coordinate i).mul
      ((hD.continuous.comp (continuous_const.add hLm)).clm_apply continuous_const)).measurable
  have hright : Measurable (fun y : FiniteStateField S=>
      fderiv ℝ (fderiv ℝ F) y (L (finiteStateGaussianBasis I i)) K+
      mass*fderiv ℝ F y K*fderiv ℝ F y (L (finiteStateGaussianBasis I i))):=
    (((hD.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.clm_apply continuous_const).add
      (((hD.continuous.clm_apply continuous_const).const_mul mass).mul
        (hD.continuous.clm_apply continuous_const))).measurable
  have hh:=finiteStateGaussianInput_coordinate_ibp mass L F hF C B hC hB H K i
  have hFm : Measurable (fun z : FiniteStateGaussianInput I=>F (H+L z)):=
    (hF.continuous.comp (continuous_const.add hLm)).measurable
  rw [finiteStateGaussianInputMean_eq_integral_tilted mass (fun z=>F (H+L z))
    (fun z=>(finiteStateGaussianBasis I).repr z i*fderiv ℝ F (H+L z) K) hFm hleft,
    finiteStateGaussianInputMean_shift mass L F
      (fun y=>fderiv ℝ (fderiv ℝ F) y (L (finiteStateGaussianBasis I i)) K+
        mass*fderiv ℝ F y K*fderiv ℝ F y (L (finiteStateGaussianBasis I i)))
      hF.continuous.measurable hright H] at hh
  exact hh

end FourPapersCommon
