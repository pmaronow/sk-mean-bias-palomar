module
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section

/-! Local joint smoothness of the genuine Riesz gradient in the second
variable. This uses the actual total derivative and fixed coordinate
inclusion, rather than imposing smoothness on a chosen derivative field. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem partial_gradient_eq (U : A×E→ℝ) (a : A) (x : E)
    (hU : DifferentiableAt ℝ U (a,x)) :
    gradient (fun y=>U (a,y)) x=(InnerProductSpace.toDual ℝ E).symm
      ((fderiv ℝ U (a,x)).comp (ContinuousLinearMap.inr ℝ A E)) := by
  have hd:HasFDerivAt (fun y=>U (a,y))
      ((fderiv ℝ U (a,x)).comp (ContinuousLinearMap.inr ℝ A E)) x := by
    convert hU.hasFDerivAt.comp x ((hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)) using 1 <;>
      first | rfl | (ext w; simp)
  change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y=>U (a,y)) x)=_
  rw [hd.fderiv]

theorem contDiffAt_partial_gradient (U : A×E→ℝ) (p : A×E)
    (hU : ContDiffAt ℝ ∞ U p) :
    ContDiffAt ℝ ∞ (fun z : A×E=>gradient (fun y=>U (z.1,y)) z.2) p := by
  let L : (A×E→L[ℝ]ℝ)→L[ℝ](E→L[ℝ]ℝ):=
    (ContinuousLinearMap.compL ℝ E (A×E) ℝ).flip (ContinuousLinearMap.inr ℝ A E)
  have hD:ContDiffAt ℝ ∞ (fun z=>L (fderiv ℝ U z)) p:=
    L.contDiff.contDiffAt.comp p (hU.fderiv_right (by simp))
  have hR:ContDiffAt ℝ ∞ (fun z=>(InnerProductSpace.toDual ℝ E).symm
      (L (fderiv ℝ U z))) p:=
    (InnerProductSpace.toDual ℝ E).symm.contDiff.contDiffAt.comp p hD
  apply hR.congr_of_eventuallyEq
  filter_upwards [(hU.of_le (by norm_num : (1 : ℕ∞ω)≤∞)).eventually (by norm_num)] with z hz
  exact partial_gradient_eq U z.1 z.2 (hz.differentiableAt (by norm_num))

end FourPapersCommon
