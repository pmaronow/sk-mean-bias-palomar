module
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Commutation of genuine constant-direction derivatives of a locally
smooth function. All derivatives are extracted from the actual function. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionDerivative (v : E) (f : E→F) (x : E) : F:=fderiv ℝ f x v

theorem contDiffAt_directionDerivative (f : E→F) (x v : E)
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (directionDerivative v f) x := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem fderiv_directionDerivative (f : E→F) (x v w : E)
    (hf : ContDiffAt ℝ ∞ f x) :
    fderiv ℝ (directionDerivative v f) x w=fderiv ℝ (fderiv ℝ f) x w v := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ f) x:=hf.fderiv_right (by simp)
  have hd:=(hD.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x)
  have he:=congrArg (fun L : E→L[ℝ]F=>L w) hd.fderiv
  change fderiv ℝ (fun y=>(fderiv ℝ f y) v) x w=_
  simpa only [directionDerivative,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,map_zero,zero_add,add_zero,ContinuousLinearMap.flip_apply] using he

theorem directionDerivative_commute (f : E→F) (x v w : E)
    (hf : ContDiffAt ℝ ∞ f x) :
    directionDerivative w (directionDerivative v f) x=
      directionDerivative v (directionDerivative w f) x := by
  change fderiv ℝ (directionDerivative v f) x w=
    fderiv ℝ (directionDerivative w f) x v
  rw [fderiv_directionDerivative f x v w hf,fderiv_directionDerivative f x w v hf]
  exact (hf.isSymmSndFDerivAt (by simp)).eq w v

theorem directionDerivative_commute_eventually (f : E→F) (x v w : E)
    (hf : ContDiffAt ℝ ∞ f x) :
    directionDerivative w (directionDerivative v f)=ᶠ[𝓝 x]
      directionDerivative v (directionDerivative w f) := by
  filter_upwards [(hf.of_le (by norm_num : (3 : ℕ∞ω)≤∞)).eventually (by norm_num)] with y hy
  have hd := ((hy.fderiv_right (by norm_num : (2 : ℕ∞ω)+1≤3)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hv:=hd.clm_apply (hasFDerivAt_const v y)
  have hw:=hd.clm_apply (hasFDerivAt_const w y)
  have hev:=congrArg (fun L : E→L[ℝ]F=>L w) hv.fderiv
  have hew:=congrArg (fun L : E→L[ℝ]F=>L v) hw.fderiv
  change fderiv ℝ (fun z=>(fderiv ℝ f z) v) y w=
    fderiv ℝ (fun z=>(fderiv ℝ f z) w) y v
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,map_zero,zero_add,add_zero,ContinuousLinearMap.flip_apply] at hev hew
  rw [hev,hew]
  exact (hy.isSymmSndFDerivAt (by norm_num)).eq w v

theorem directionDerivative_commute_third (f : E→F) (x a v w : E)
    (hf : ContDiffAt ℝ ∞ f x) :
    directionDerivative a (directionDerivative v (directionDerivative w f)) x=
      directionDerivative v (directionDerivative w (directionDerivative a f)) x := by
  rw [directionDerivative_commute (directionDerivative w f) x v a
    (contDiffAt_directionDerivative f x w hf)]
  have he:=directionDerivative_commute_eventually f x w a hf
  exact congrArg (fun L : E→L[ℝ]F=>L v) he.fderiv_eq

end FourPapersCommon
