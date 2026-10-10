module
public import FourPapersCommon.GeneratorPullback

@[expose] public section

/-! The genuine time/space split for a smooth function along a time curve. -/
noncomputable section
open scoped ContDiff
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv_time_curve_composition (f : ℝ×E→ℝ) (Y : ℝ→E) (a : ℝ)
    (hf : ContDiffAt ℝ 1 f (a,Y a)) (hY : ContDiffAt ℝ 1 Y a) :
    deriv (fun q=>f (q,Y q)) a=deriv (fun q=>f (q,Y a)) a+
      fderiv ℝ (fun x=>f (a,x)) (Y a) (deriv Y a) := by
  exact deriv_time_composition f (fun z : ℝ×ℝ=>Y z.1) a 0 hf
    (hY.comp (a,0) contDiffAt_fst)

end FourPapersCommon
