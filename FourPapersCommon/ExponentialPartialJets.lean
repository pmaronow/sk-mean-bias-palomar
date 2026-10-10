module
public import FourPapersCommon.ExponentialSmoothAlgebra
public import FourPapersCommon.PartialFDerivSmooth

@[expose] public section

/-! Literal parameter and spatial derivatives preserve genuine exponential
jet envelopes on open parameter domains. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ExponentialSmoothOn.directional {f : E→F} {s : Set E}
    (hf : ExponentialSmoothOn f s) (v : E) :
    ExponentialSmoothOn (fun x=>_root_.fderiv ℝ f x v) s := by
  exact hf.fderiv.compCLM (ContinuousLinearMap.apply ℝ F v)

theorem ExponentialSmoothOn.partialFDeriv {f : A×E→F} {s : Set (A×E)}
    (hf : ExponentialSmoothOn f s) (hs : IsOpen s) :
    ExponentialSmoothOn (fun z=>_root_.fderiv ℝ (fun x=>f (z.1,x)) z.2) s := by
  let L : ((A×E)→L[ℝ]F)→L[ℝ](E→L[ℝ]F):=
    (ContinuousLinearMap.compL ℝ E (A×E) F).flip (ContinuousLinearMap.inr ℝ A E)
  apply (hf.fderiv.compCLM L).congr
  intro z hz
  filter_upwards [hs.mem_nhds hz] with w hw
  exact (partial_fderiv_eq f w.1 w.2 ((hf.smooth w hw).differentiableAt (by simp))).symm

theorem ExponentialSmoothOn.partialGradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : A×E→ℝ} {s : Set (A×E)}
    (hf : ExponentialSmoothOn f s) (hs : IsOpen s) :
    ExponentialSmoothOn (fun z=>gradient (fun x=>f (z.1,x)) z.2) s := by
  exact (hf.partialFDeriv hs).compCLM
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem ExponentialSmoothOn.partialHessian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : A×E→ℝ} {s : Set (A×E)}
    (hf : ExponentialSmoothOn f s) (hs : IsOpen s) :
    ExponentialSmoothOn (fun z=>QuantitativeFollowup.hessianOperator
      (fun x=>f (z.1,x)) z.2) s := by
  apply ((hf.partialGradient hs).partialFDeriv hs).congr
  intro z hz
  filter_upwards [hs.mem_nhds hz] with w hw
  have hC : ContDiffAt ℝ 2 (fun y=>f (w.1,y)) w.2:=
    ((hf.smooth w hw).comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
  exact (hasFDerivAt_gradient_of_contDiffAt _ w.2 hC).fderiv

end FourPapersCommon
