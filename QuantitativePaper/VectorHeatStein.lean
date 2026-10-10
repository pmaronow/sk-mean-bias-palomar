module
public import QuantitativePaper.VectorHeatScaleDerivative
public import QuantitativePaper.VectorWeightedDrift

@[expose] public section

/-! Actual Gaussian integration by parts for first spatial heat derivatives.
The required growth bounds and integrability are proved from the analytic
heat datum, including the zero-dimensional field space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorHeatShiftFirst (F : Field n → ℝ) (v : ℝ) (x : Field n) (i : Fin n)
    (z : Field n) : ℝ := fderiv ℝ F (fieldShift v x z) (EuclideanSpace.single i 1)

theorem hasFDerivAt_vectorHeatShiftFirst {F : Field n → ℝ} (d : VectorHeatDatum F)
    (v : ℝ) (x : Field n) (i : Fin n) (z : Field n) :
    HasFDerivAt (vectorHeatShiftFirst F v x i)
      (((vectorHessian F (fieldShift v x z)).flip (EuclideanSpace.single i 1)).comp
        (Real.sqrt v • ContinuousLinearMap.id ℝ (Field n))) z := by
  have hdF := (d.regularity.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdg : HasFDerivAt (fun y=>fderiv ℝ F y (EuclideanSpace.single i 1))
      ((vectorHessian F (fieldShift v x z)).flip (EuclideanSpace.single i 1))
      (fieldShift v x z) := by
    simpa only [ContinuousLinearMap.comp_zero,zero_add,vectorHessian] using
      (hdF (fieldShift v x z)).hasFDerivAt.clm_apply
        (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) (fieldShift v x z))
  have hshift : HasFDerivAt (fun w=>fieldShift v x w)
      (Real.sqrt v • ContinuousLinearMap.id ℝ (Field n)) z := by
    simpa only [fieldShift,zero_add,Pi.smul_apply,id_eq] using
      (hasFDerivAt_const x z).fun_add ((hasFDerivAt_id z).const_smul (Real.sqrt v))
  exact hdg.comp z hshift

theorem VectorHeatDatum.shift_first_growth {F : Field n → ℝ} (d : VectorHeatDatum F)
    (v : ℝ) (x : Field n) (i : Fin n) :
    let C := (1+Real.sqrt v)*d.growthBound*Real.exp (d.rate*‖x‖)
    let c := d.rate*Real.sqrt v
    (∀ z,|vectorHeatShiftFirst F v x i z| ≤ C*Real.exp (c*‖z‖)) ∧
    (∀ z,‖gradient (vectorHeatShiftFirst F v x i) z‖ ≤ C*Real.exp (c*‖z‖)) := by
  have he : ‖EuclideanSpace.single i (1 : ℝ)‖=1 := by simp
  have hn (z : Field n) : ‖fieldShift v x z‖ ≤ ‖x‖+Real.sqrt v*‖z‖ := by
    simpa only [fieldShift,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using norm_add_le x (Real.sqrt v • z)
  have hbd (z : Field n) : d.growthBound*Real.exp (d.rate*‖fieldShift v x z‖) ≤
      d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*Real.sqrt v)*‖z‖) := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hn z) d.rate.coe_nonneg)) d.growthBound.coe_nonneg
    simpa only [mul_add,Real.exp_add,mul_assoc] using hh
  have hA : ‖Real.sqrt v • ContinuousLinearMap.id ℝ (Field n)‖ ≤ Real.sqrt v := by
    rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Field n)) (Real.sqrt_nonneg v)
  constructor
  · intro z
    have hnorm := (fderiv ℝ F (fieldShift v x z)).le_opNorm (EuclideanSpace.single i 1)
    rw [he,mul_one,Real.norm_eq_abs] at hnorm
    have hb := hnorm.trans ((d.first_bound _).trans (hbd z))
    apply hb.trans
    have h1 : 1 ≤ 1+Real.sqrt v := by linarith [Real.sqrt_nonneg v]
    have hp : 0 ≤ d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*Real.sqrt v)*‖z‖) := by positivity
    simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right h1 hp
  · intro z
    have hg : ‖gradient (vectorHeatShiftFirst F v x i) z‖=
        ‖fderiv ℝ (vectorHeatShiftFirst F v x i) z‖ := by
      rw [gradient]
      exact LinearIsometryEquiv.norm_map _ _
    rw [hg,(hasFDerivAt_vectorHeatShiftFirst d v x i z).fderiv]
    have hf := ((vectorHessian F (fieldShift v x z)).flip).le_opNorm (EuclideanSpace.single i 1)
    rw [ContinuousLinearMap.opNorm_flip,he,mul_one] at hf
    have hcomp := (ContinuousLinearMap.opNorm_comp_le
      (h := (vectorHessian F (fieldShift v x z)).flip (EuclideanSpace.single i 1))
      (Real.sqrt v • ContinuousLinearMap.id ℝ (Field n)))
    have hh := hcomp.trans (mul_le_mul hf hA (norm_nonneg _) (norm_nonneg _))
    apply (hh.trans (mul_le_mul_of_nonneg_right ((d.second_bound _).trans (hbd z)) (Real.sqrt_nonneg _))).trans
    nlinarith [mul_nonneg (mul_nonneg d.growthBound.coe_nonneg (Real.exp_pos (d.rate*‖x‖)).le)
      (Real.exp_pos ((d.rate*Real.sqrt v)*‖z‖)).le]

theorem vectorHeatShiftFirst_stein {F : Field n → ℝ} (d : VectorHeatDatum F)
    (v : ℝ) (x : Field n) (i : Fin n) :
    Integrable (fun z=>z i*vectorHeatShiftFirst F v x i z) (fieldGaussian n) ∧
    Integrable (fun z=>gradient (vectorHeatShiftFirst F v x i) z i) (fieldGaussian n) ∧
    (∫ z,z i*vectorHeatShiftFirst F v x i z ∂fieldGaussian n)=
      Real.sqrt v*(∫ z,vectorHessian F (fieldShift v x z)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) ∂fieldGaussian n) := by
  have hs : ContDiff ℝ 1 (vectorHeatShiftFirst F v x i) :=
    ((d.regularity.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).comp
      (by unfold fieldShift;fun_prop)
  have hg := d.shift_first_growth v x i
  let C := (1+Real.sqrt v)*d.growthBound*Real.exp (d.rate*‖x‖)
  let c := d.rate*Real.sqrt v
  have hint := SYK.gaussian_ibp_integrable (vectorHeatShiftFirst F v x i) i hs C c hg.1 hg.2
  refine ⟨hint.1,hint.2,?_⟩
  have hh := SYK.gaussian_ibp_coord (vectorHeatShiftFirst F v x i) i hs C c hg.1 hg.2
  change (∫ z,z i*vectorHeatShiftFirst F v x i z ∂fieldGaussian n)=
    ∫ z,gradient (vectorHeatShiftFirst F v x i) z i ∂fieldGaussian n at hh
  rw [hh,← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  change gradient (vectorHeatShiftFirst F v x i) z i =
    Real.sqrt v*vectorHessian F (fieldShift v x z) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
  rw [SYK.gradient_coord_eq,(hasFDerivAt_vectorHeatShiftFirst d v x i z).fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]

end QuantitativePaper
