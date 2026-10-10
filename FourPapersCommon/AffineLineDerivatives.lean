module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section

/-! Actual first and second directional derivatives on a fixed affine line. -/
noncomputable section
open scoped ContDiff
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_affine_line (f : E→ℝ) (hf : Differentiable ℝ f) (x w : E) (y : ℝ) :
    HasDerivAt (fun r => f (x+r • w)) (fderiv ℝ f (x+y • w) w) y := by
  have hl : HasDerivAt (fun r : ℝ => x+r • w) w y := by
    convert HasDerivAt.add (hasDerivAt_const y x) ((hasDerivAt_id y).smul_const w) using 1
    · rfl
    · simp only [one_smul,zero_add]
  exact (hf (x+y • w)).hasFDerivAt.comp_hasDerivAt y hl

theorem hasDerivAt_fderiv_affine_line (f : E→ℝ) (hf : ContDiff ℝ 2 f) (x w : E) (y : ℝ) :
    HasDerivAt (fun r => fderiv ℝ f (x+r • w) w)
      (fderiv ℝ (fderiv ℝ f) (x+y • w) w w) y := by
  let A : (E→L[ℝ]ℝ)→L[ℝ]ℝ := ContinuousLinearMap.apply ℝ ℝ w
  have hl : HasDerivAt (fun r : ℝ => x+r • w) w y := by
    convert HasDerivAt.add (hasDerivAt_const y x) ((hasDerivAt_id y).smul_const w) using 1
    · rfl
    · simp only [one_smul,zero_add]
  have hd := (((hf.fderiv_right (m:=1) (by norm_num)).differentiable_one (x+y • w)).hasFDerivAt)
  have h := (A.hasFDerivAt.comp (x+y • w) hd).comp_hasDerivAt y hl
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,A,ContinuousLinearMap.apply_apply] using h

end FourPapersCommon
