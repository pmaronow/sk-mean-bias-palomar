module
public import FourPapersCommon.SmoothParameterInverse

@[expose] public section

/-! A genuine local smooth inverse agrees with a selected inverse on the
actual parameter domain, including a boundary parameter. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1600000
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_smooth_parameter_inverse_within (F : A×E→E) (Y : A×E→E)
    (s : Set A) (V : Set E) (hV : IsOpen V) (a : A) (m x : E)
    (ha : a∈s) (hm : m∈V) (hF : ContDiffAt ℝ ∞ F (a,x)) (hx : F (a,x)=m)
    (hH : (fderiv ℝ F (a,x) ∘L ContinuousLinearMap.inr ℝ A E).IsInvertible)
    (hinj : ∀b∈s,Function.Injective (fun y=>F (b,y)))
    (hY : ∀z∈s×ˢV,F (z.1,Y z)=z.2) :
    ∃ψ : A×E→E,ContDiffAt ℝ ∞ ψ (a,m) ∧
      Y=ᶠ[𝓝[s×ˢV] (a,m)]ψ := by
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
  have hInv:(fderiv ℝ G u ∘L ContinuousLinearMap.inr ℝ (A×E) E).IsInvertible:=hEq ▸ hH
  let ψ:=hGu.implicitFunction (by simp) hInv
  refine ⟨ψ,hGu.contDiffAt_implicitFunction (by simp) hInv,?_⟩
  have hGzero:G u=0:=by simp [G,u,K,M,hx]
  have he:=hGu.eventually_apply_implicitFunction (by simp) hInv
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hzs
  apply hinj z.1 hzs.1
  change F (z.1,Y z)=F (z.1,ψ z)
  rw [hY z hzs]
  have hψEq:F (z.1,ψ z)=z.2:=by
    change G (z,ψ z)=G u at hz
    rw [hGzero] at hz
    change F (z.1,ψ z)-z.2=0 at hz
    exact sub_eq_zero.mp hz
  exact hψEq.symm

end FourPapersCommon
