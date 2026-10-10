module
public import QuantitativePaper.EnergyMomentProposition
public import QuantitativePaper.CompletedEnergyLaplaceLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Actual zero-temperature passage for the finite SK mean and variance.
The uniform soft maximum bound provides the pointwise limit and a genuine
integrable square envelope; no moment convergence premise is required. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1600000

def groundMeanDeficit (n : ℕ) : ℝ := groundScalarValue-groundMean n

theorem tendsto_energyFreeEnergy_groundState (n : ℕ) (g : Couplings n) :
    Tendsto (fun β : ℝ=>energyFreeEnergy n β g) atTop (𝓝 (groundState n g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g:=fun β:ℝ=>(n:ℝ)*Real.log 2/β) (.of_forall fun β=>norm_nonneg _)
    ((eventually_gt_atTop (0:ℝ)).mono fun β hβ=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (energyFreeEnergy_sub_groundState n β hβ g).1]
      exact (energyFreeEnergy_sub_groundState n β hβ g).2)
  exact tendsto_const_nhds.div_atTop tendsto_id

theorem tendsto_integral_energyFreeEnergy_groundState (n : ℕ) :
    Tendsto (fun β : ℝ=>∫g,energyFreeEnergy n β g ∂couplingLaw n) atTop
      (𝓝 (∫g,groundState n g ∂couplingLaw n)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g:=fun β:ℝ=>(n:ℝ)*Real.log 2/β) (.of_forall fun β=>norm_nonneg _)
    ((eventually_gt_atTop (0:ℝ)).mono fun β hβ=>by
      rw [Real.norm_eq_abs,←normalizedEnergyMoment_zero,←normalizedGroundMoment_zero]
      exact normalizedEnergyMoment_ground_distance n β 0 hβ)
  exact tendsto_const_nhds.div_atTop tendsto_id

theorem tendsto_integral_energyFreeEnergy_sq_groundState (n : ℕ) :
    Tendsto (fun β : ℝ=>∫g,energyFreeEnergy n β g^2 ∂couplingLaw n) atTop
      (𝓝 (∫g,groundState n g^2 ∂couplingLaw n)) := by
  let a : ℝ := (n:ℝ)*Real.log 2
  have ha : 0≤a := by dsimp only [a];positivity
  have hiG : Integrable (fun g=>groundState n g^2) (couplingLaw n) :=
    (memLp_two_iff_integrable_sq (continuous_groundState n).aestronglyMeasurable).mp
      (memLp_two_groundState n)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun g=>2*(groundState n g^2+a^2))
  · exact .of_forall fun β=>((continuous_logPartition n β).div_const β).pow 2
      |>.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with β hβ
    exact .of_forall fun g=>by
      have hβp : 0<β := zero_lt_one.trans_le hβ
      have hh:=energyFreeEnergy_sub_groundState n β hβp g
      have hdiv : a/β≤a := (div_le_iff₀ hβp).2 (by nlinarith)
      have hdiff : |energyFreeEnergy n β g-groundState n g|≤a := by
        rw [abs_of_nonneg hh.1]
        exact hh.2.trans hdiv
      have habs : |energyFreeEnergy n β g|≤|groundState n g|+a := by
        have ht:=abs_add_le (energyFreeEnergy n β g-groundState n g) (groundState n g)
        rw [sub_add_cancel] at ht
        linarith
      have hsq:=pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs] at hsq
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (|groundState n g|-a),sq_abs (groundState n g)]
  · exact (hiG.add (integrable_const _)).const_mul 2
  · exact .of_forall fun g=>(tendsto_energyFreeEnergy_groundState n g).pow 2

theorem tendsto_energyVariance_groundStateVariance (n : ℕ) :
    Tendsto (fun β : ℝ=>variance (energyFreeEnergy n β) (couplingLaw n)) atTop
      (𝓝 (groundStateVariance n)) := by
  have hh := (tendsto_integral_energyFreeEnergy_sq_groundState n).sub
    ((tendsto_integral_energyFreeEnergy_groundState n).pow 2)
  simpa only [variance_eq_sub (memLp_two_energyFreeEnergy n _),groundStateVariance,
    variance_eq_sub (memLp_two_groundState n),Pi.pow_apply] using hh

theorem tendsto_energyMeanDeficit_groundMeanDeficit (n : ℕ) :
    Tendsto (energyMeanDeficit n) atTop (𝓝 (groundMeanDeficit n)) := by
  unfold energyMeanDeficit groundMeanDeficit groundMean
  exact scalar_zero_temperature_limit_at_zero.sub
    ((tendsto_integral_energyFreeEnergy_groundState n).div_const (n:ℝ))

end QuantitativePaper
