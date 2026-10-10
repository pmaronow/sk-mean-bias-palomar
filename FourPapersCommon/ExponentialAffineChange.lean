module
public import FourPapersCommon.ExponentialLinearChange

@[expose] public section

/-! Actual affine restriction bounds for local smooth jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_precomp_affine_le_at (L : E→L[ℝ]F) (v : F)
    (f : F→G) (x : E) (hf : ContDiffAt ℝ ∞ f (v+L x)) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun y=>f (v+L y)) x‖≤
      ‖iteratedFDeriv ℝ r f (v+L x)‖*‖L‖^r := by
  have hT : ContDiffAt ℝ ∞ (fun z=>f (v+z)) (L x):=
    hf.comp (L x) (contDiffAt_const.add contDiffAt_id)
  simpa only [Function.comp_def,iteratedFDeriv_comp_add_left] using
    norm_iteratedFDeriv_precomp_clm_le_at L (fun z=>f (v+z)) x hT r

end FourPapersCommon
