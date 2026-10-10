module
public import QuantitativePaper.VectorShiftCalculus

@[expose] public section

/-! Differential Hessian-shift identity for a genuine field response.
The concrete anisotropic Gaussian history supplies its derivative identity. -/
noncomputable section
open Set
namespace QuantitativeFollowup
open QuantitativePaper
set_option maxHeartbeats 1500000
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def normalizedMeanSquare (m : E→F) (N : ℝ) (x : E) : ℝ := ‖m x‖^2/N

theorem fderiv_normalizedMeanSquare (m : E→F) (N : ℝ)
    (hm : Differentiable ℝ m) (x z : E) :
    fderiv ℝ (normalizedMeanSquare m N) x z=2*inner ℝ (fderiv ℝ m x z) (m x)/N := by
  have hd := ((hm x).hasFDerivAt.norm_sq).const_smul N⁻¹
  have hd' : HasFDerivAt (normalizedMeanSquare m N)
      (N⁻¹ • (2 : ℕ) • (innerSL ℝ (m x)).comp (fderiv ℝ m x)) x := by
    convert! hd using 1
    funext y
    simp only [normalizedMeanSquare,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [hd'.fderiv]
  simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,innerSL_apply_apply,two_nsmul,add_apply]
  rw [real_inner_comm (m x) (fderiv ℝ m x z)]
  ring

theorem normalizedMeanSquare_hessian_shift (U : E→ℝ) (m : E→F) (L : F→L[ℝ]E)
    (hU : ContDiff ℝ 2 U) (hm : ContDiff ℝ 1 m)
    (hfield : ∀x w,fderiv ℝ U x (L w)=inner ℝ (m x) w)
    (N : ℝ) (hN : N≠0) (x : E) :
    hessianOperator U x (L (m x))=(N/2) • gradient (normalizedMeanSquare m N) x := by
  let w := m x
  have hdf : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hc := ((hdf.differentiable (by norm_num) x).hasFDerivAt).clm_apply
    (hasFDerivAt_const (L w) x)
  have hi := (hm.differentiable (by norm_num) x).hasFDerivAt.inner ℝ
    (hasFDerivAt_const w x)
  have he : (fun y => fderiv ℝ U y (L w))=(fun y => inner ℝ (m y) w) :=
    funext fun y => hfield y w
  rw [he] at hc
  have hsecond (z : E) : fderiv ℝ (fderiv ℝ U) x z (L w)=inner ℝ (fderiv ℝ m x z) w := by
    have hh := congrArg (fun A : E→L[ℝ]ℝ => A z) (hc.unique hi)
    simpa only [add_apply,ContinuousLinearMap.comp_apply,zero_apply,map_zero,zero_add,
      ContinuousLinearMap.flip_apply,fderivInnerCLM_apply,ContinuousLinearMap.prod_apply,
      inner_zero_right] using hh
  apply ext_inner_right ℝ
  intro z
  rw [inner_hessianOperator,(hU.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (L w) z,
    hsecond,real_inner_smul_left,inner_gradient_left,
    fderiv_normalizedMeanSquare _ _ (hm.differentiable (by norm_num))]
  dsimp [w]
  field_simp

end QuantitativeFollowup
