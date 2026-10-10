module
public import FourPapersCommon.PartialGradientSmooth
public import FourPapersCommon.LocalGradientCalculus

@[expose] public section

/-! Actual joint smoothness of spatial derivatives and Hessians extracted
from a locally smooth parameter-dependent function. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem partial_fderiv_eq (U : A×E→F) (a : A) (x : E)
    (hU : DifferentiableAt ℝ U (a,x)) :
    fderiv ℝ (fun y=>U (a,y)) x=
      (fderiv ℝ U (a,x)).comp (ContinuousLinearMap.inr ℝ A E) := by
  have hd:HasFDerivAt (fun y=>U (a,y))
      ((fderiv ℝ U (a,x)).comp (ContinuousLinearMap.inr ℝ A E)) x := by
    convert hU.hasFDerivAt.comp x ((hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)) using 1 <;>
      first | rfl | (ext w; simp)
  exact hd.fderiv

theorem contDiffAt_partial_fderiv (U : A×E→F) (p : A×E)
    (hU : ContDiffAt ℝ ∞ U p) :
    ContDiffAt ℝ ∞ (fun z : A×E=>fderiv ℝ (fun y=>U (z.1,y)) z.2) p := by
  let L : (A×E→L[ℝ]F)→L[ℝ](E→L[ℝ]F):=
    (ContinuousLinearMap.compL ℝ E (A×E) F).flip (ContinuousLinearMap.inr ℝ A E)
  have hD:ContDiffAt ℝ ∞ (fun z=>L (fderiv ℝ U z)) p:=
    L.contDiff.contDiffAt.comp p (hU.fderiv_right (by simp))
  apply hD.congr_of_eventuallyEq
  filter_upwards [(hU.of_le (by norm_num : (1 : ℕ∞ω)≤∞)).eventually (by norm_num)] with z hz
  exact partial_fderiv_eq U z.1 z.2 (hz.differentiableAt (by norm_num))

theorem contDiffAt_partial_hessian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (U : A×E→ℝ) (p : A×E)
    (hU : ContDiffAt ℝ ∞ U p) :
    ContDiffAt ℝ ∞ (fun z : A×E=>
      QuantitativeFollowup.hessianOperator (fun y=>U (z.1,y)) z.2) p := by
  let G : A×E→E:=fun z=>gradient (fun y=>U (z.1,y)) z.2
  have hG:ContDiffAt ℝ ∞ G p:=contDiffAt_partial_gradient U p hU
  have hD:=contDiffAt_partial_fderiv G p hG
  apply hD.congr_of_eventuallyEq
  filter_upwards [(hU.of_le (by norm_num : (2 : ℕ∞ω)≤∞)).eventually (by norm_num)] with z hz
  have hy:ContDiffAt ℝ 2 (fun y=>U (z.1,y)) z.2:=
    hz.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
  exact (hasFDerivAt_gradient_of_contDiffAt (fun y=>U (z.1,y)) z.2 hy).fderiv.symm

end FourPapersCommon
