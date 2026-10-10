module
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

@[expose] public section

/-! The actual second Fréchet chain rule, evaluated in one direction. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem second_fderiv_comp_apply (f : F→G) (g : E→F) (x v : E)
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (f∘g)) x v v=
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x v)+
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v v) := by
  have hdf:=(hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1≤2)).differentiableAt
    (by norm_num)
  have hdg:=(hg.fderiv_right (by norm_num : (1 : ℕ∞ω)+1≤2)).differentiableAt
    (by norm_num)
  have hd:=(hdf.hasFDerivAt.comp x (hg.differentiableAt (by norm_num)).hasFDerivAt).clm_comp
    hdg.hasFDerivAt
  have he : fderiv ℝ (f∘g)=ᶠ[𝓝 x]
      (fun y=>(fderiv ℝ f (g y)).comp (fderiv ℝ g y)) := by
    have hgn:=(hg.eventually (by norm_num : (2 : ℕ∞ω)≠∞))
    have hfn:=((hg.continuousAt).tendsto.eventually
      (hf.eventually (by norm_num : (2 : ℕ∞ω)≠∞)))
    filter_upwards [hgn,hfn] with y hy hfy
    exact fderiv_comp y (hfy.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num))
  have he':=congrArg (fun L : E→L[ℝ]E→L[ℝ]G=>L v v) he.fderiv_eq
  simp only [Function.comp_def] at hd
  rw [hd.fderiv] at he'
  simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,add_comm] using he'

end FourPapersCommon
