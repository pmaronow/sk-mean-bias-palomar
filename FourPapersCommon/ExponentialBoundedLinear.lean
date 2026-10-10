module
public import FourPapersCommon.ExponentialSmoothAlgebra

@[expose] public section

/-! A genuine linear map bounded on the chosen domain has exponential
envelopes with zero exponential rate, even on an unbounded domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1500000
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exponentialSmoothOn_bounded_linear (L : E→L[ℝ]F) (s : Set E)
    (D : ℝ) (hD : 0≤D) (hb : ∀x∈s,‖L x‖≤D) : ExponentialSmoothOn (L : E→F) s := by
  refine ⟨fun _ _=>L.contDiff.contDiffAt,fun r=>⟨D+‖L‖,0,by positivity,le_rfl,?_⟩⟩
  intro x hx
  rw [zero_mul,Real.exp_zero,mul_one]
  cases r with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact (hb x hx).trans (by linarith [norm_nonneg L])
  | succ r =>
    rw [←norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (L : E→F)=(fun _ : E=>L):=funext fun y=>L.fderiv
    rw [he]
    cases r with
    | zero => simpa only [norm_iteratedFDeriv_zero] using (show ‖L‖≤D+‖L‖ by linarith)
    | succ r => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero] using
        (show 0≤D+‖L‖ by positivity)

end FourPapersCommon
