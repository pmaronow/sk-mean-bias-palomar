module
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Genuine Hilbert-valued integral Cauchy--Schwarz, and the averaged
quadratic reaction bound without division by a possibly zero random norm. -/
noncomputable section
open MeasureTheory Set Filter
namespace FourPapersCommon
set_option maxHeartbeats 500000
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {P : Measure Ω} {b v : Ω → E}

theorem integral_inner_eq_L2_inner (hb : MemLp b 2 P) (hv : MemLp v 2 P) :
    (∫ ω, inner ℝ (b ω) (v ω) ∂P) = inner ℝ (hb.toLp b) (hv.toLp v) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toLp, hv.coeFn_toLp] with ω hω hω'
  rw [hω, hω']

theorem integral_inner_sq_le (hb : MemLp b 2 P) (hv : MemLp v 2 P) :
    (∫ ω, inner ℝ (b ω) (v ω) ∂P)^2 ≤
      (∫ ω, ‖b ω‖^2 ∂P) * (∫ ω, ‖v ω‖^2 ∂P) := by
  have h := real_inner_mul_inner_self_le (hb.toLp b) (hv.toLp v)
  rw [← integral_inner_eq_L2_inner hb hv, ← integral_inner_eq_L2_inner hb hb,
    ← integral_inner_eq_L2_inner hv hv] at h
  simpa only [pow_two, real_inner_self_eq_norm_sq] using h

theorem averaged_hilbert_reaction {C : Ω → ℝ} {α : ℝ}
    (hb : MemLp b 2 P) (hv : MemLp v 2 P) (hC : Integrable C P)
    (hCn : ∀ᵐ ω ∂P, 0 ≤ C ω) (hα : 0 ≤ α)
    (hbound : ∀ᵐ ω ∂P, α * C ω ≤ inner ℝ (b ω) (v ω)) :
    α^2 * (∫ ω, C ω ∂P)^2 ≤
      (∫ ω, ‖b ω‖^2 ∂P) * (∫ ω, ‖v ω‖^2 ∂P) := by
  have hn := hb.norm.integrable_mul hv.norm
  change Integrable (fun ω => ‖b ω‖ * ‖v ω‖) P at hn
  have hi : Integrable (fun ω => inner ℝ (b ω) (v ω)) P :=
    hn.mono' (hb.aestronglyMeasurable.inner hv.aestronglyMeasurable)
      (.of_forall fun ω => norm_inner_le_norm (b ω) (v ω))
  have hle : α * (∫ ω, C ω ∂P) ≤ ∫ ω, inner ℝ (b ω) (v ω) ∂P := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hC.const_mul α) hi hbound
  have hnonneg : 0 ≤ ∫ ω, C ω ∂P := integral_nonneg_of_ae hCn
  have hs := integral_inner_sq_le hb hv
  nlinarith [mul_nonneg hα hnonneg]

end FourPapersCommon
