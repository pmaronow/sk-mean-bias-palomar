module
public import FourPapersCommon.AffineLineDerivatives

@[expose] public section

/-! Actual mixed second directional derivatives along an affine line. -/
noncomputable section
open scoped ContDiff
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_fderiv_affine_line_direction (f : E→ℝ) (hf : ContDiff ℝ 2 f)
    (x v w : E) (y : ℝ) :
    HasDerivAt (fun r => fderiv ℝ f (x+r • v) w)
      (fderiv ℝ (fderiv ℝ f) (x+y • v) v w) y := by
  let A : (E→L[ℝ]ℝ)→L[ℝ]ℝ := ContinuousLinearMap.apply ℝ ℝ w
  have hl : HasDerivAt (fun r : ℝ => x+r • v) v y := by
    convert HasDerivAt.add (hasDerivAt_const y x) ((hasDerivAt_id y).smul_const v) using 1
    · rfl
    · simp only [one_smul,zero_add]
  have hd := (((hf.fderiv_right (m:=1) (by norm_num)).differentiable_one (x+y • v)).hasFDerivAt)
  have h := (A.hasFDerivAt.comp (x+y • v) hd).comp_hasDerivAt y hl
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,A,ContinuousLinearMap.apply_apply] using h

end FourPapersCommon
