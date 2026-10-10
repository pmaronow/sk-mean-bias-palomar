module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic

@[expose] public section

/-! Genuine truncation of an integrable nonnegative weight, including bounded
observable pairings and the vanishing mass of the discarded tail. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

def truncateWeight (W : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := min (k : ℝ) (W ω)

theorem measurable_truncateWeight (W : Ω → ℝ) (hW : Measurable W) (k : ℕ) :
    Measurable (truncateWeight W k) := measurable_const.min hW

theorem truncateWeight_nonneg (W : Ω → ℝ) (hW : ∀ω,0 ≤ W ω) (k : ℕ) (ω : Ω) :
    0 ≤ truncateWeight W k ω := le_min (Nat.cast_nonneg _) (hW ω)

theorem truncateWeight_le (W : Ω → ℝ) (k : ℕ) (ω : Ω) :
    truncateWeight W k ω ≤ W ω := min_le_right _ _

theorem norm_truncateWeight_le (W : Ω → ℝ) (hW : ∀ω,0 ≤ W ω) (k : ℕ) (ω : Ω) :
    ‖truncateWeight W k ω‖ ≤ (k : ℝ) := by
  rw [Real.norm_of_nonneg (truncateWeight_nonneg W hW k ω)]
  exact min_le_left _ _

theorem tendsto_truncateWeight (W : Ω → ℝ) (ω : Ω) :
    Tendsto (fun k => truncateWeight W k ω) atTop (𝓝 (W ω)) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (W ω)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with j hj
  exact (min_eq_right (hk.le.trans (Nat.cast_le.mpr hj))).symm

theorem integrable_weight_mul_bounded (W g : Ω → ℝ) (hi : Integrable W P)
    (hg : Measurable g) (M : ℝ) (hM : ∀ω,‖g ω‖ ≤ M) :
    Integrable (fun ω => W ω*g ω) P := by
  apply (hi.norm.const_mul M).mono' (hi.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards [] with ω
  dsimp only [Pi.mul_apply]
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hM ω) (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem integrable_truncateWeight (W : Ω → ℝ) (hW : Measurable W)
    (hn : ∀ω,0 ≤ W ω) (hi : Integrable W P) (k : ℕ) :
    Integrable (truncateWeight W k) P := by
  apply hi.mono' (measurable_truncateWeight W hW k).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_of_nonneg (truncateWeight_nonneg W hn k ω)]
  exact truncateWeight_le W k ω

theorem tendsto_integral_truncateWeight_mul (W g : Ω → ℝ) (hW : Measurable W)
    (hn : ∀ω,0 ≤ W ω) (hi : Integrable W P) (hg : Measurable g)
    (M : ℝ) (hM : ∀ω,‖g ω‖ ≤ M) :
    Tendsto (fun k => ∫ω,truncateWeight W k ω*g ω ∂P) atTop (𝓝 (∫ω,W ω*g ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω => M*W ω)
  · intro k
    exact ((measurable_truncateWeight W hW k).mul hg).aestronglyMeasurable
  · exact hi.const_mul M
  · intro k
    filter_upwards [] with ω
    rw [norm_mul,Real.norm_of_nonneg (truncateWeight_nonneg W hn k ω)]
    calc
      _ ≤ truncateWeight W k ω*M := mul_le_mul_of_nonneg_left (hM ω) (truncateWeight_nonneg W hn k ω)
      _ ≤ W ω*M := mul_le_mul_of_nonneg_right (truncateWeight_le W k ω)
        ((norm_nonneg (g ω)).trans (hM ω))
      _ = _ := mul_comm _ _
  · filter_upwards [] with ω
    exact (tendsto_truncateWeight W ω).mul_const (g ω)

theorem tendsto_integral_truncation_tail (W : Ω → ℝ) (hW : Measurable W)
    (hn : ∀ω,0 ≤ W ω) (hi : Integrable W P) :
    Tendsto (fun k => ∫ω,W ω-truncateWeight W k ω ∂P) atTop (𝓝 0) := by
  have hh := tendsto_integral_truncateWeight_mul W (fun _ => 1) hW hn hi measurable_const 1 (by simp)
  simp only [mul_one] at hh
  have he : (fun k => ∫ω,W ω-truncateWeight W k ω ∂P)=
      fun k => (∫ω,W ω ∂P)-(∫ω,truncateWeight W k ω ∂P) := by
    funext k
    exact integral_sub hi (integrable_truncateWeight W hW hn hi k)
  rw [he]
  simpa only [sub_self] using (tendsto_const_nhds (x := ∫ω,W ω ∂P)).sub hh

end FourPapersCommon
