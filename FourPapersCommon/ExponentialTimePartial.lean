module
public import FourPapersCommon.ExponentialPartialJets
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! Actual time partials on open joint parameter domains preserve
exponential bounds for every derivative. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ExponentialSmoothOn.timePartial {f : (ℝ×P)×E→F} {s : Set ((ℝ×P)×E)}
    (hf : ExponentialSmoothOn f s) (hs : IsOpen s) :
    ExponentialSmoothOn (fun z=>deriv (fun q=>f ((q,z.1.2),z.2)) z.1.1) s := by
  apply (hf.directional (((1,0),0) : (ℝ×P)×E)).congr
  intro z hz
  filter_upwards [hs.mem_nhds hz] with w hw
  have hLine : HasDerivAt (fun q : ℝ=>((q,w.1.2),w.2)) ((1,0),0) w.1.1:=
    ((hasDerivAt_id w.1.1).prodMk (hasDerivAt_const w.1.1 w.1.2)).prodMk
      (hasDerivAt_const w.1.1 w.2)
  exact (((hf.smooth w hw).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    w.1.1 hLine).deriv.symm

end FourPapersCommon
