module
public import FourPapersCommon.SmoothCellLocalization

@[expose] public section

/-! A genuine smooth extension obtained by a time cutoff supported
strictly inside an open cell, without imposing growth bounds on joint jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1000000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [HasContDiffBump E]

def timeLocalizedFunction (ρ : ℝ→ℝ) (f : ℝ×E→ℝ) : ℝ×E→ℝ:=fun w=>ρ w.1*f w

theorem contDiff_timeLocalizedFunction (ρ : ℝ→ℝ) (f : ℝ×E→ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hρ : ContDiff ℝ ∞ ρ)
    (hs : tsupport ρ⊆U) (hf : ContDiffOn ℝ ∞ f (Prod.fst ⁻¹' U)) :
    ContDiff ℝ ∞ (timeLocalizedFunction ρ f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro w
  obtain ⟨j,hj⟩:=(expandingSmoothCutoff_eventually_one w.2).exists
  apply (contDiff_cellLocalizedFunction ρ j f U hU hρ hs hf).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hj.comp_tendsto continuous_snd.continuousAt] with v hv
  dsimp only [Function.comp_def] at hv
  simp only [timeLocalizedFunction,cellLocalizedFunction,hv,mul_one]

theorem timeLocalizedFunction_eventually_eq (ρ : ℝ→ℝ) (f : ℝ×E→ℝ)
    (q : ℝ) (x : E) (hρ : ρ=ᶠ[𝓝 q] (fun _=>1)) :
    timeLocalizedFunction ρ f=ᶠ[𝓝 (q,x)]f := by
  filter_upwards [hρ.comp_tendsto continuous_fst.continuousAt] with w hw
  dsimp only [Function.comp_def] at hw
  simp only [timeLocalizedFunction,hw,one_mul]

theorem timeLocalizedFunction_eventually_zero (ρ : ℝ→ℝ) (f : ℝ×E→ℝ)
    (q : ℝ) (x : E) (hq : q∉tsupport ρ) :
    timeLocalizedFunction ρ f=ᶠ[𝓝 (q,x)] (fun _=>0) := by
  have hz : ρ=ᶠ[𝓝 q] (fun _=>0):=notMem_tsupport_iff_eventuallyEq.mp hq
  filter_upwards [hz.comp_tendsto continuous_fst.continuousAt] with w hw
  dsimp only [Function.comp_def] at hw
  simp only [timeLocalizedFunction,hw,zero_mul]

theorem hasDerivAt_timeLocalizedFunction
    (ρ : ℝ→ℝ) (f : ℝ×E→ℝ) (q : ℝ) (x : E) (v d : ℝ)
    (hρ : HasDerivAt ρ d q) (hf : HasDerivAt (fun r=>f (r,x)) v q) :
    HasDerivAt (fun r=>timeLocalizedFunction ρ f (r,x))
      (d*f (q,x)+ρ q*v) q := hρ.mul hf

end FourPapersCommon
