module
public import FourPapersCommon.CompactNegativeComparison
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! True time and spatial jets of an exponentially weighted difference. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon
set_option backward.isDefEq.respectTransparency false

def weightedParabolicDifference (K : ℝ) (W V : ℝ×ℝ→ℝ) (p : ℝ×ℝ) : ℝ:=
  Real.exp (-K*p.1)*(W p-V p)

theorem hasDerivWithinAt_weightedParabolicDifference_time
    (K : ℝ) (W V : ℝ×ℝ→ℝ) (T t x wt vt : ℝ)
    (hW : HasDerivWithinAt (fun r=>W (r,x)) wt (Icc 0 T) t)
    (hV : HasDerivWithinAt (fun r=>V (r,x)) vt (Icc 0 T) t) :
    HasDerivWithinAt (fun r=>weightedParabolicDifference K W V (r,x))
      (Real.exp (-K*t)*(wt-vt-K*(W (t,x)-V (t,x)))) (Icc 0 T) t := by
  have hd:=(((hasDerivAt_id t).const_mul (-K)).exp).hasDerivWithinAt.mul (hW.sub hV)
  convert hd using 1
  · rfl
  · dsimp only [Pi.sub_apply,id_eq];ring

theorem hasDerivAt_weightedParabolicDifference_field
    (K : ℝ) (W V : ℝ×ℝ→ℝ) (t x wx vx : ℝ)
    (hW : HasDerivAt (fun y=>W (t,y)) wx x)
    (hV : HasDerivAt (fun y=>V (t,y)) vx x) :
    HasDerivAt (fun y=>weightedParabolicDifference K W V (t,y))
      (Real.exp (-K*t)*(wx-vx)) x := by
  simpa only [weightedParabolicDifference,Pi.sub_apply] using
    (hW.sub hV).const_mul (Real.exp (-K*t))

theorem weightedParabolicDifference_second_deriv
    (K : ℝ) (W V W₁ V₁ : ℝ×ℝ→ℝ) (t l r x wxx vxx : ℝ) (hx : x∈Ioo l r)
    (hW : ∀y∈Ioo l r,HasDerivAt (fun z=>W (t,z)) (W₁ (t,y)) y)
    (hV : ∀y∈Ioo l r,HasDerivAt (fun z=>V (t,z)) (V₁ (t,y)) y)
    (hW₂ : HasDerivAt (fun y=>W₁ (t,y)) wxx x)
    (hV₂ : HasDerivAt (fun y=>V₁ (t,y)) vxx x) :
    deriv (deriv (fun y=>weightedParabolicDifference K W V (t,y))) x=
      Real.exp (-K*t)*(wxx-vxx) := by
  have he : deriv (fun y=>weightedParabolicDifference K W V (t,y))=ᶠ[𝓝 x]
      (fun y=>Real.exp (-K*t)*(W₁ (t,y)-V₁ (t,y))):=by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hasDerivAt_weightedParabolicDifference_field K W V t y _ _ (hW y hy) (hV y hy)).deriv
  rw [he.deriv_eq]
  simpa only [Pi.sub_apply] using ((hW₂.sub hV₂).const_mul (Real.exp (-K*t))).deriv

end FourPapersCommon
