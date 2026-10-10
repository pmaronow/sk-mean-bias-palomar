module
public import QuantitativePaper.UniformEnergyPowerCalculus
public import QuantitativePaper.UniformQuantitativeParisi
public import QuantitativePaper.EnergyMomentIdentity
public import QuantitativePaper.VarianceSensitiveTail

@[expose] public section

/-! The genuine SK mean and variance-sensitive tail give the lower
fluctuation exponent once the actual sixth-window tail is applied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
set_option maxHeartbeats 1400000

theorem energyMeanDeficit_eq_pressure_gap (n : ℕ) (β : ℝ) :
    energyMeanDeficit n β=(Paper.parisiPDEValue β 0-pressure n β)/β := by
  unfold energyMeanDeficit scalarEnergyValue
  rw [zero_div,constrainedParisiValue_zero]
  unfold energyFreeEnergy pressure
  rw [integral_div]
  ring

theorem energyMeanDeficit_nonneg (n : ℕ) (hn : 0<n) (β : ℝ) (hβ : 0<β) :
    0≤energyMeanDeficit n β := by
  rw [energyMeanDeficit_eq_pressure_gap]
  exact div_nonneg (uniform_quantitative_parisi_pressure n hn β hβ).1 hβ.le

theorem energy_variance_lower_of_window_tail (n : ℕ) (hn : 0<n) (β A K : ℝ)
    (hβ : 1≤β) (hA : 0<A) (hK : 0<K)
    (htail : Real.exp (-A*(n:ℝ)^(1/5:ℝ))≤(couplingLaw n).real
      {g | (n:ℝ)*(scalarEnergyValue β 0+K*(n:ℝ)^(-(2/3:ℝ)))≤energyFreeEnergy n β g})
    (hlog : Real.log 3≤A*(n:ℝ)^(1/5:ℝ))
    (hsize : 2≤(varianceTailRate*K/A)^2*(n:ℝ)^(4/15:ℝ)) :
    (varianceTailRate*K/A)^2/2*(n:ℝ)^(4/15:ℝ)≤
      variance (energyFreeEnergy n β) (couplingLaw n) := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hβp : 0<β := zero_lt_one.trans_le hβ
  have hm := energyMeanDeficit_nonneg n hn β hβp
  have hm' : (∫g,energyFreeEnergy n β g ∂couplingLaw n)≤(n:ℝ)*scalarEnergyValue β 0 := by
    unfold energyMeanDeficit at hm
    have hh := (div_le_iff₀ hnR).mp (show
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)/(n:ℝ)≤ scalarEnergyValue β 0 by linarith)
    nlinarith
  have he : (n:ℝ)*(K*(n:ℝ)^(-(2/3:ℝ)))=K*(n:ℝ)^(1/3:ℝ) := by
    calc
      _=K*((n:ℝ)^(1:ℝ)*(n:ℝ)^(-(2/3:ℝ))) := by rw [Real.rpow_one];ring
      _=_ := by rw [←Real.rpow_add hnR];norm_num
  have hsubset : {g : Couplings n | (n:ℝ)*(scalarEnergyValue β 0+K*(n:ℝ)^(-(2/3:ℝ)))≤energyFreeEnergy n β g} ⊆
      {g | K*(n:ℝ)^(1/3:ℝ)≤energyFreeEnergy n β g-(∫η,energyFreeEnergy n β η ∂couplingLaw n)} := by
    intro g hg
    have hs := hg
    change (n:ℝ)*(scalarEnergyValue β 0+K*(n:ℝ)^(-(2/3:ℝ)))≤energyFreeEnergy n β g at hs
    rw [mul_add,he] at hs
    change K*(n:ℝ)^(1/3:ℝ)≤energyFreeEnergy n β g-(∫η,energyFreeEnergy n β η ∂couplingLaw n)
    linarith
  have hs := (htail.trans (measureReal_mono hsubset)).trans
    (variance_sensitive_energy_tail n hn β hβp (K*(n:ℝ)^(1/3:ℝ)) (by positivity))
  have hb : 0<varianceTailRate := by unfold varianceTailRate;positivity
  have hscale := tail_scale_lower (n:ℝ) (varianceTailScale n β) A (2*varianceTailRate*K)
    hnR (varianceTailScale_pos n β hβp) hA (by positivity)
    (by convert hs using 1;congr 2 <;> ring) hlog
  have hd : 0<varianceTailRate*K/A := by positivity
  have hscale' : (varianceTailRate*K/A)*(n:ℝ)^(2/15:ℝ)≤varianceTailScale n β := by
    convert hscale using 1
    ring
  have hinv : β⁻¹^2≤1 := by
    have hi : 0≤β⁻¹ := inv_nonneg.mpr hβp.le
    have hj : β⁻¹≤1 := (inv_le_one₀ hβp).2 hβ
    nlinarith
  exact variance_lower_of_tail_scale (n:ℝ) (varianceTailScale n β)
    (variance (energyFreeEnergy n β) (couplingLaw n)) (varianceTailRate*K/A) (β⁻¹^2)
    hnR hd (varianceTailScale_pos n β hβp).le hscale' (varianceTailScale_sq n β) hinv hsize

end QuantitativePaper
