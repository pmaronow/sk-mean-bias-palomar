module
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

/-! A selected inverse of a genuinely smooth parameter family inherits
local smoothness from the implicit function theorem. No continuity of the
selected inverse is assumed. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem contDiffAt_parameter_inverse (F : A×E→E) (Y : A×E→E)
    (a : A) (m x : E) (hF : ContDiffAt ℝ ∞ F (a,x))
    (hx : F (a,x)=m)
    (hH : (fderiv ℝ F (a,x) ∘L ContinuousLinearMap.inr ℝ A E).IsInvertible)
    (hinj : ∀ᶠ b in 𝓝 a,Function.Injective (fun y=>F (b,y)))
    (hY : ∀ᶠ z in 𝓝 (a,m),F (z.1,Y z)=z.2) :
    ContDiffAt ℝ ∞ Y (a,m):=by
  let K:((A×E)×E)→L[ℝ](A×E):=
    ((ContinuousLinearMap.fst ℝ A E).comp (ContinuousLinearMap.fst ℝ (A×E) E)).prod
      (ContinuousLinearMap.snd ℝ (A×E) E)
  let M:((A×E)×E)→L[ℝ]E:=
    (ContinuousLinearMap.snd ℝ A E).comp (ContinuousLinearMap.fst ℝ (A×E) E)
  let G:((A×E)×E)→E:=fun z=>F (K z)-M z
  let u:((A×E)×E):=((a,m),x)
  have hGu:ContDiffAt ℝ ∞ G u:=
    (hF.comp u K.contDiff.contDiffAt).sub M.contDiff.contDiffAt
  have hd:HasFDerivAt G ((fderiv ℝ F (a,x)).comp K-M) u:=
    (hF.differentiableAt (by simp) |>.hasFDerivAt.comp u K.hasFDerivAt).sub M.hasFDerivAt
  have hEq:(fderiv ℝ G u ∘L ContinuousLinearMap.inr ℝ (A×E) E)=
      (fderiv ℝ F (a,x) ∘L ContinuousLinearMap.inr ℝ A E):=by
    rw [hd.fderiv]
    ext w
    simp [K,M]
  have hInv:(fderiv ℝ G u ∘L ContinuousLinearMap.inr ℝ (A×E) E).IsInvertible:=
    hEq ▸ hH
  let ψ:=hGu.implicitFunction (by simp) hInv
  have hψ:ContDiffAt ℝ ∞ ψ (a,m):=hGu.contDiffAt_implicitFunction (by simp) hInv
  have hGzero:G u=0:=by simp [G,u,K,M,hx]
  have he: Y=ᶠ[𝓝 (a,m)]ψ:=by
    have hInj : ∀ᶠ z : A×E in 𝓝 (a,m),Function.Injective (fun y=>F (z.1,y)):=
      (continuous_fst.tendsto (a,m)).eventually hinj
    filter_upwards [hGu.eventually_apply_implicitFunction (by simp) hInv,hY,hInj] with z hz hzy hzi
    apply hzi
    change F (z.1,Y z)=F (z.1,ψ z)
    rw [hzy]
    have hψEq:F (z.1,ψ z)=z.2:=by
      change G (z,ψ z)=G u at hz
      rw [hGzero] at hz
      change F (z.1,ψ z)-z.2=0 at hz
      exact sub_eq_zero.mp hz
    exact hψEq.symm
  exact hψ.congr_of_eventuallyEq he

end FourPapersCommon
