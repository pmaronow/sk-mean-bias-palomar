module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Differentiation under a genuine within-set filter, including closed
parameter endpoints. The proof integrates the actual first-order remainder;
no extension outside the parameter set is introduced. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FourPapersCommon

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem hasDerivWithinAt_integral_of_dominated_lip
    (F : ℝ → Ω → ℝ) (F' b : Ω → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hx₀ : x₀ ∈ s)
    (hFm : ∀ x ∈ s, AEStronglyMeasurable (F x) P)
    (hFi : Integrable (F x₀) P) (hF'i : Integrable F' P)
    (hbi : Integrable b P)
    (hlip : ∀ᵐ ω ∂P, ∀ x ∈ s, ‖F x ω-F x₀ ω‖ ≤ b ω*‖x-x₀‖)
    (hd : ∀ᵐ ω ∂P, HasDerivWithinAt (fun x => F x ω) (F' ω) s x₀) :
    HasDerivWithinAt (fun x => ∫ω, F x ω ∂P) (∫ω, F' ω ∂P) s x₀ := by
  let B : Ω → ℝ := fun ω => |b ω|
  have hBi : Integrable B P := hbi.norm
  have hlip' : ∀ᵐ ω ∂P, ∀ x ∈ s,
      ‖F x ω-F x₀ ω‖ ≤ B ω*‖x-x₀‖ :=
    hlip.mono fun ω hω x hx => (hω x hx).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hFint (x : ℝ) (hx : x ∈ s) : Integrable (F x) P := by
    apply integrable_of_norm_sub_le (hFm x hx) hFi (hBi.const_mul ‖x-x₀‖)
    filter_upwards [hlip'] with ω hω
    simpa only [norm_sub_rev, mul_comm] using hω x hx
  have hknown : ∀ᶠ x in 𝓝[s] x₀, x ∈ s := self_mem_nhdsWithin
  have he : ∀ᶠ x in 𝓝[s] x₀,
      ‖x-x₀‖⁻¹*‖(∫ω, F x ω ∂P)-(∫ω, F x₀ ω ∂P)-(x-x₀) • (∫ω, F' ω ∂P)‖ =
      ‖∫ω, ‖x-x₀‖⁻¹ • (F x ω-F x₀ ω-(x-x₀) • F' ω) ∂P‖ := by
    filter_upwards [hknown] with x hx
    rw [←norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), integral_smul,
      integral_sub, integral_sub, integral_smul]
    exacts [hFint x hx, hFi, (hFint x hx).sub hFi, hF'i.const_mul _]
  rw [hasDerivWithinAt_iff_tendsto, tendsto_congr' he,
    ←tendsto_zero_iff_norm_tendsto_zero,
    ←show (∫ω : Ω, ‖x₀-x₀‖⁻¹ • (F x₀ ω-F x₀ ω-(x₀-x₀) • F' ω) ∂P)=0 by simp]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun ω => B ω+‖F' ω‖)
  · filter_upwards [hknown] with x hx
    convert (((hFm x hx).sub (hFm x₀ hx₀)).sub
      (hF'i.aestronglyMeasurable.const_smul (x-x₀))).const_smul ‖x-x₀‖⁻¹ using 1
  · filter_upwards [hknown] with x hx
    filter_upwards [hlip'] with ω hω
    have hn : 0 ≤ ‖x-x₀‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    calc
      ‖‖x-x₀‖⁻¹ • (F x ω-F x₀ ω-(x-x₀) • F' ω)‖
          ≤ ‖x-x₀‖⁻¹*(‖F x ω-F x₀ ω‖+‖(x-x₀) • F' ω‖) := by
            rw [norm_smul_of_nonneg hn]
            exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hn
      _ ≤ ‖x-x₀‖⁻¹*(B ω*‖x-x₀‖+‖x-x₀‖*‖F' ω‖) := by
            rw [norm_smul]
            gcongr
            exact hω x hx
      _ ≤ B ω+‖F' ω‖ := by
            by_cases hzero : x-x₀=0
            · simp only [hzero, norm_zero, inv_zero, zero_mul]
              exact add_nonneg (abs_nonneg _) (norm_nonneg _)
            · rw [show B ω*‖x-x₀‖+‖x-x₀‖*‖F' ω‖ =
                ‖x-x₀‖*(B ω+‖F' ω‖) by ring,
                ←mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzero), one_mul]
  · exact hBi.add hF'i.norm
  · filter_upwards [hd] with ω hω
    simp only [sub_self, norm_zero, inv_zero, zero_smul]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
      hasDerivWithinAt_iff_tendsto.mp hω

theorem hasDerivWithinAt_integral_of_uniform_derivative
    (F F' : ℝ → Ω → ℝ) (b : Ω → ℝ) (s : Set ℝ) (hs : Convex ℝ s)
    (x₀ : ℝ) (hx₀ : x₀ ∈ s)
    (hFm : ∀ x ∈ s, AEStronglyMeasurable (F x) P)
    (hFi : Integrable (F x₀) P)
    (hF'm : ∀ x ∈ s, AEStronglyMeasurable (F' x) P)
    (hbi : Integrable b P)
    (hb : ∀ᵐ ω ∂P, ∀ x ∈ s, ‖F' x ω‖ ≤ b ω)
    (hd : ∀ᵐ ω ∂P, ∀ x ∈ s,
      HasDerivWithinAt (fun t => F t ω) (F' x ω) s x) :
    HasDerivWithinAt (fun x => ∫ω, F x ω ∂P) (∫ω, F' x₀ ω ∂P) s x₀ := by
  have hF'i : Integrable (F' x₀) P := hbi.mono' (hF'm x₀ hx₀)
    (hb.mono fun ω hω => hω x₀ hx₀)
  apply hasDerivWithinAt_integral_of_dominated_lip F (F' x₀) b s x₀ hx₀
    hFm hFi hF'i hbi
  · filter_upwards [hd,hb] with ω hω hbound
    intro x hx
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hω hbound hs hx₀ hx
  · exact hd.mono fun ω hω => hω x₀ hx₀

end FourPapersCommon
