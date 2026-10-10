module
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-! Exact second derivatives after adding a genuine affine function. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon

theorem deriv_deriv_affine_add (f : ℝ→ℝ) (x c d e : ℝ)
    (hf : ContDiffAt ℝ ∞ f x) :
    deriv (deriv (fun r=>c*f r+d*r+e)) x=c*deriv (deriv f) x := by
  have he : deriv (fun r=>c*f r+d*r+e)=ᶠ[𝓝 x](fun r=>c*deriv f r+d):=by
    filter_upwards [(hf.of_le (by norm_num : (2 : ℕ∞ω)≤∞)).eventually (by norm_num)] with r hr
    have hd:=((hr.differentiableAt (by norm_num)).hasDerivAt.const_mul c).add
      ((hasDerivAt_id r).const_mul d)
    convert (hd.add_const e).deriv using 1 <;> first | rfl | simp
  rw [he.deriv_eq]
  have hdf : ContDiffAt ℝ ∞ (deriv f) x:=hf.derivWithin (by simp)
  exact ((((hdf.differentiableAt (by simp)).hasDerivAt).const_mul c).add_const d).deriv

end FourPapersCommon
