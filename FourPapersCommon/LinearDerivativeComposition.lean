module
public import FourPapersCommon.SecondDerivativeComposition

@[expose] public section

/-! Linear coordinate projections commute with actual first and second
Fréchet derivatives, including vector-valued second derivatives. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fderiv_linear_postcomp (L : F→L[ℝ]G) (f : E→F) (x v : E)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y=>L (f y)) x v=L (fderiv ℝ f x v) := by
  have hd:=L.hasFDerivAt.comp x hf.hasFDerivAt
  exact congrArg (fun A : E→L[ℝ]G=>A v) hd.fderiv

theorem second_fderiv_linear_postcomp (L : F→L[ℝ]G) (f : E→F) (x v : E)
    (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ (fun y=>L (f y))) x v v=
      L (fderiv ℝ (fderiv ℝ f) x v v) := by
  have hd:=second_fderiv_comp_apply (L : F→G) f x v L.contDiff.contDiffAt hf
  have he : fderiv ℝ (L : F→G)=(fun _ : F=>L):=funext fun y=>L.fderiv
  rw [he] at hd
  have hc : fderiv ℝ (fun _ : F=>L) (f x)=0:=(hasFDerivAt_const L (f x)).fderiv
  rw [hc] at hd
  simpa only [Function.comp_def,ContinuousLinearMap.zero_apply,
    zero_add] using hd

end FourPapersCommon
