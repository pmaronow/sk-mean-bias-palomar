module
public import QuantitativePaper.NormalizedMoments
public import FourPapersCommon.LogMGFUniformComparison

@[expose] public section

/-! The literal soft-max logarithmic-moment comparison and its limit for
arbitrary real inverse temperature tending to infinity. The scalar
zero-temperature variational identification is a separate obligation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper

theorem energy_ground_cgf_bound (n : ℕ) (β lam : ℝ) (hβ : 0<β) :
    |cgf (energyFreeEnergy n β) (couplingLaw n) lam-
      cgf (groundState n) (couplingLaw n) lam| ≤ |lam| * ((n:ℝ)*Real.log 2/β) := by
  have ha : 0≤(n:ℝ)*Real.log 2/β:=by positivity
  have hh:=FourPapersCommon.cgf_uniform_increment_bound (couplingLaw n)
    (energyFreeEnergy n β) (groundState n) lam ((n:ℝ)*Real.log 2/β)
    (integrable_exp_energyFreeEnergy n β lam) (integrable_exp_groundState n lam)
    (.of_forall fun g=>by
      have h:=energyFreeEnergy_sub_groundState n β hβ g
      exact ⟨by linarith [h.1],by linarith [h.2]⟩)
  simpa only [abs_of_nonneg ha] using hh

theorem soft_max_log_moment_comparison (n : ℕ) (β lam : ℝ) (hβ : 0<β)
    (hlam : lam≠0) :
    0≤cgf (energyFreeEnergy n β) (couplingLaw n) lam/lam-
      cgf (groundState n) (couplingLaw n) lam/lam ∧
    cgf (energyFreeEnergy n β) (couplingLaw n) lam/lam-
      cgf (groundState n) (couplingLaw n) lam/lam≤(n:ℝ)*Real.log 2/β := by
  let a:=(n:ℝ)*Real.log 2/β
  have ha : 0≤a:=by dsimp [a];positivity
  have hh:=FourPapersCommon.cgf_comparison_of_bounded_increment (couplingLaw n)
    (energyFreeEnergy n β) (groundState n) lam a
    (integrable_exp_energyFreeEnergy n β lam) (integrable_exp_groundState n lam)
    (.of_forall fun g=>by
      have h:=energyFreeEnergy_sub_groundState n β hβ g
      exact ⟨by linarith [h.1],by dsimp [a];linarith [h.2]⟩)
  rw [←sub_div]
  rcases lt_or_gt_of_ne hlam with hl|hl
  · have hla : lam*a≤0:=mul_nonpos_of_nonpos_of_nonneg hl.le ha
    simp only [min_eq_right hla,max_eq_left hla] at hh
    exact ⟨div_nonneg_of_nonpos hh.2 hl.le,
      (div_le_iff_of_neg hl).mpr (by simpa only [mul_comm] using hh.1)⟩
  · have hla : 0≤lam*a:=mul_nonneg hl.le ha
    simp only [min_eq_left hla,max_eq_right hla] at hh
    exact ⟨div_nonneg hh.1 hl.le,
      (div_le_iff₀ hl).mpr (by simpa only [mul_comm] using hh.2)⟩

theorem tendsto_cgf_energyFreeEnergy_groundState_real (n : ℕ) (lam : ℝ) :
    Tendsto (fun β:ℝ=>cgf (energyFreeEnergy n β) (couplingLaw n) lam) atTop
      (𝓝 (cgf (groundState n) (couplingLaw n) lam)) := by
  rw [←tendsto_sub_nhds_zero_iff,Metric.tendsto_nhds]
  intro ε hε
  have hz : Tendsto (fun β:ℝ=>|lam| * ((n:ℝ)*Real.log 2/β)) atTop (𝓝 0) := by
    convert! (tendsto_const_nhds.div_atTop tendsto_id).const_mul |lam| using 1 <;> simp
  filter_upwards [hz (Metric.ball_mem_nhds 0 hε),eventually_gt_atTop (0:ℝ)] with β hb hβ
  change |lam| * ((n:ℝ)*Real.log 2/β) ∈ Metric.ball 0 ε at hb
  rw [Metric.mem_ball,dist_zero_right] at hb
  rw [dist_zero_right,Real.norm_eq_abs]
  have hnon : 0 ≤ |lam| * ((n:ℝ)*Real.log 2/β) := by positivity
  have hb' : |lam| * ((n:ℝ)*Real.log 2/β)<ε := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hnon] using hb
  exact (energy_ground_cgf_bound n β lam hβ).trans_lt hb'

end QuantitativePaper
