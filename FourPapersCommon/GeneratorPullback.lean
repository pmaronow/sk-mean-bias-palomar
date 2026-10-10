module
public import FourPapersCommon.SecondDerivativeComposition
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! Genuine change of variables for a diffusion generator. The hypotheses
describe actual derivatives; the chain rule and cancellation are proved. -/
noncomputable section
open Filter
open scoped Topology ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_time_composition (Z : ℝ×F→ℝ) (G : ℝ×E→F) (q : ℝ) (x : E)
    (hZ : ContDiffAt ℝ 1 Z (q,G (q,x))) (hG : ContDiffAt ℝ 1 G (q,x)) :
    deriv (fun r=>Z (r,G (r,x))) q=
      deriv (fun r=>Z (r,G (q,x))) q+
        fderiv ℝ (fun m=>Z (q,m)) (G (q,x)) (deriv (fun r=>G (r,x)) q) := by
  have hdZ:=(hZ.differentiableAt (by norm_num)).hasFDerivAt
  have hdG:=((hG.comp q (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
    (by norm_num)).hasDerivAt
  have htotal:=(hdZ.comp_hasDerivAt q ((hasDerivAt_id q).prodMk hdG)).deriv
  have htime:=(hdZ.comp_hasDerivAt q
    ((hasDerivAt_id q).prodMk (hasDerivAt_const q (G (q,x))))).deriv
  have hspace:=(hdZ.comp (G (q,x))
    ((hasFDerivAt_const q (G (q,x))).prodMk (hasFDerivAt_id (G (q,x))))).fderiv
  simp only [Function.comp_def,id_eq] at htotal htime hspace
  rw [htotal,htime,hspace]
  change (fderiv ℝ Z (q,G (q,x))) (1,deriv (fun r=>G (r,x)) q)=
    (fderiv ℝ Z (q,G (q,x))) (1,0)+
      (fderiv ℝ Z (q,G (q,x))) (0,deriv (fun r=>G (r,x)) q)
  rw [←map_add]
  simp

theorem diffusion_generator_pullback
    {ι : Type*} [Fintype ι] (e : ι→E) (Z : ℝ×F→ℝ) (G : ℝ×E→F)
    (q : ℝ) (x b : E) (c : ℝ)
    (hZ : ContDiffAt ℝ 2 Z (q,G (q,x))) (hG : ContDiffAt ℝ 2 G (q,x))
    (hcancel : deriv (fun r=>G (r,x)) q+fderiv ℝ (fun y=>G (q,y)) x b+
      (c/2) • (∑i,fderiv ℝ (fderiv ℝ (fun y=>G (q,y))) x (e i) (e i))=0) :
    deriv (fun r=>Z (r,G (r,x))) q+
      fderiv ℝ (fun y=>Z (q,G (q,y))) x b+
      c/2*(∑i,fderiv ℝ (fderiv ℝ (fun y=>Z (q,G (q,y)))) x (e i) (e i))=
      deriv (fun r=>Z (r,G (q,x))) q+
        c/2*(∑i,fderiv ℝ (fderiv ℝ (fun m=>Z (q,m))) (G (q,x))
          (fderiv ℝ (fun y=>G (q,y)) x (e i))
          (fderiv ℝ (fun y=>G (q,y)) x (e i))) := by
  let f : F→ℝ:=fun m=>Z (q,m)
  let g : E→F:=fun y=>G (q,y)
  have hf : ContDiffAt ℝ 2 f (g x):=hZ.comp (g x) (contDiffAt_const.prodMk contDiffAt_id)
  have hg : ContDiffAt ℝ 2 g x:=hG.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have htime:=deriv_time_composition Z G q x (hZ.of_le (by norm_num))
    (hG.of_le (by norm_num))
  have hfirst:=congrArg (fun L : E→L[ℝ]ℝ=>L b)
    (fderiv_comp x (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num)))
  simp only [ContinuousLinearMap.comp_apply,Function.comp_def] at hfirst
  have hsecond (i : ι):=second_fderiv_comp_apply f g x (e i) hf hg
  dsimp only [Function.comp_def,f,g] at hsecond
  rw [htime,hfirst]
  simp_rw [hsecond]
  rw [Finset.sum_add_distrib]
  have hs : (∑i,fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x (e i) (e i)))=
      fderiv ℝ f (g x) (∑i,fderiv ℝ (fderiv ℝ g) x (e i) (e i)):=by
    rw [map_sum]
  dsimp only [f,g] at hs
  rw [hs]
  have hc:=congrArg (fderiv ℝ f (g x)) hcancel
  simp only [map_add,map_smul,map_zero,smul_eq_mul] at hc
  change fderiv ℝ f (g x) (deriv (fun r=>G (r,x)) q)+
    fderiv ℝ f (g x) (fderiv ℝ g x b)+
    c/2*fderiv ℝ f (g x) (∑i,fderiv ℝ (fderiv ℝ g) x (e i) (e i))=0 at hc
  change _=deriv (fun r=>Z (r,g x)) q+_
  dsimp only [f,g] at hc
  linarith

end FourPapersCommon
