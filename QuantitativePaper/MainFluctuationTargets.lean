module
public import QuantitativePaper.UniformEnergyVarianceLower
public import QuantitativePaper.GroundFluctuationPassage

@[expose] public section

/-! Literal main fluctuation/tail statements in the original finite SK
normalization. The scaling lemmas are supporting implications only. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
namespace QuantitativePaper
set_option maxHeartbeats 1400000

def MainGroundFluctuationsTarget : Prop :=
  ∃c C : ℝ,∃N0 : ℕ,0<c ∧ 0<C ∧ 1≤N0 ∧ ∀n : ℕ,N0≤n→
    c*(n:ℝ)^(4/15:ℝ)≤groundStateVariance n ∧
    groundStateVariance n≤C*(n:ℝ)^(7/15:ℝ) ∧
    c*(n:ℝ)^(-(11/12:ℝ))≤groundScalarValue-groundMean n ∧
    groundScalarValue-groundMean n≤C*(n:ℝ)^(-(2/3:ℝ))

def MainFixedTemperatureFluctuationsTarget : Prop :=
  ∀β : ℝ,1<β→∃c C : ℝ,∃N0 : ℕ,0<c ∧ 0<C ∧ 1≤N0 ∧ ∀n : ℕ,N0≤n→
    c*(n:ℝ)^(4/15:ℝ)≤freeEnergyVariance n β ∧
    freeEnergyVariance n β≤C*(n:ℝ)^(7/15:ℝ) ∧
    c*(n:ℝ)^(-(11/12:ℝ))≤parisiPDEValue β 0-pressure n β ∧
    parisiPDEValue β 0-pressure n β≤C*(n:ℝ)^(-(2/3:ℝ))

def MainUpperTailsTarget : Prop :=
  ∀β : ℝ,1<β→∃A xstar c C : ℝ,∃N0 : ℕ,
    0<A ∧ 0<xstar ∧ 0<c ∧ 0<C ∧ 1≤N0 ∧ ∀n : ℕ,N0≤n→
      ∀x : ℝ,A*(n:ℝ)^(-(2/3:ℝ))≤x→x≤xstar→
        Real.exp (-C*(n:ℝ)*x^(6/5:ℝ))≤
          (couplingLaw n).real {g | (n:ℝ)*(parisiPDEValue β 0+x)≤logPartition n β g} ∧
        (couplingLaw n).real {g | (n:ℝ)*(parisiPDEValue β 0+x)≤logPartition n β g}≤
          Real.exp (-c*(n:ℝ)*x^(6/5:ℝ))

def MainUniformUpperTailsTarget : Prop :=
  ∃A xstar c C : ℝ,∃N0 : ℕ,
    0<A ∧ 0<xstar ∧ 0<c ∧ 0<C ∧ 1≤N0 ∧ ∀n : ℕ,N0≤n→
      ∀x : ℝ,A*(n:ℝ)^(-(2/3:ℝ))≤x→x≤xstar→
        (∀β : ℝ,2≤β→
          Real.exp (-C*(n:ℝ)*x^(6/5:ℝ))≤
            (couplingLaw n).real {g | (n:ℝ)*(parisiPDEValue β 0/β+x)≤energyFreeEnergy n β g} ∧
          (couplingLaw n).real {g | (n:ℝ)*(parisiPDEValue β 0/β+x)≤energyFreeEnergy n β g}≤
            Real.exp (-c*(n:ℝ)*x^(6/5:ℝ))) ∧
        Real.exp (-C*(n:ℝ)*x^(6/5:ℝ))≤
          (couplingLaw n).real {g | (n:ℝ)*(groundScalarValue+x)≤groundState n g} ∧
        (couplingLaw n).real {g | (n:ℝ)*(groundScalarValue+x)≤groundState n g}≤
          Real.exp (-c*(n:ℝ)*x^(6/5:ℝ))

theorem scalarEnergyValue_zero_eq_pressure_scaled (β : ℝ) :
    scalarEnergyValue β 0=parisiPDEValue β 0/β := by
  unfold scalarEnergyValue
  rw [zero_div,constrainedParisiValue_zero]

theorem freeEnergyVariance_eq_scaled_energyVariance (n : ℕ) (β : ℝ) (hβ : β≠0) :
    freeEnergyVariance n β=β^2*variance (energyFreeEnergy n β) (couplingLaw n) := by
  have he : logPartition n β=fun g=>β*energyFreeEnergy n β g := by
    funext g
    unfold energyFreeEnergy
    exact (mul_div_cancel₀ _ hβ).symm
  unfold freeEnergyVariance
  rw [he,variance_const_mul]

theorem original_free_energy_tail_eq_energy_tail (n : ℕ) (β x : ℝ) (hβ : 0<β) :
    (couplingLaw n).real {g | (n:ℝ)*(parisiPDEValue β 0+x)≤logPartition n β g}=
      (couplingLaw n).real {g | (n:ℝ)*(scalarEnergyValue β 0+x/β)≤energyFreeEnergy n β g} := by
  congr 1
  ext g
  simp only [mem_setOf_eq,scalarEnergyValue_zero_eq_pressure_scaled,energyFreeEnergy]
  rw [le_div_iff₀ hβ]
  have he : (n:ℝ)*(parisiPDEValue β 0/β+x/β)*β=(n:ℝ)*(parisiPDEValue β 0+x) := by
    field_simp
  rw [he]

theorem fixed_temperature_four_powers_of_energy (β c C : ℝ) (hβ : 0<β)
    (hc : 0<c) (hC : 0<C) (N0 : ℕ) (hN0 : 1≤N0)
    (henergy : ∀n : ℕ,N0≤n→
      c*(n:ℝ)^(4/15:ℝ)≤variance (energyFreeEnergy n β) (couplingLaw n) ∧
      variance (energyFreeEnergy n β) (couplingLaw n)≤C*(n:ℝ)^(7/15:ℝ) ∧
      c*(n:ℝ)^(-(11/12:ℝ))≤energyMeanDeficit n β ∧
      energyMeanDeficit n β≤C*(n:ℝ)^(-(2/3:ℝ))) :
    ∃co Co : ℝ,0<co ∧ 0<Co ∧ ∀n : ℕ,N0≤n→
      co*(n:ℝ)^(4/15:ℝ)≤freeEnergyVariance n β ∧
      freeEnergyVariance n β≤Co*(n:ℝ)^(7/15:ℝ) ∧
      co*(n:ℝ)^(-(11/12:ℝ))≤parisiPDEValue β 0-pressure n β ∧
      parisiPDEValue β 0-pressure n β≤Co*(n:ℝ)^(-(2/3:ℝ)) := by
  let co:=min (β^2*c) (β*c)
  let Co:=max (β^2*C) (β*C)
  refine ⟨co,Co,lt_min (by positivity) (by positivity),
    (show 0<β^2*C by positivity).trans_le (le_max_left _ _),?_⟩
  intro n hn
  obtain ⟨hv0,hv1,hm0,hm1⟩:=henergy n hn
  have hp : parisiPDEValue β 0-pressure n β=β*energyMeanDeficit n β := by
    rw [energyMeanDeficit_eq_pressure_gap]
    exact (mul_div_cancel₀ _ hβ.ne').symm
  rw [freeEnergyVariance_eq_scaled_energyVariance n β hβ.ne',hp]
  refine ⟨?_,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (show (0:ℝ)≤(n:ℝ) by positivity) (4/15:ℝ))).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hv0 (sq_nonneg β))
  · exact (mul_le_mul_of_nonneg_left hv1 (sq_nonneg β)).trans
      (by simpa only [Co,←mul_assoc] using mul_le_mul_of_nonneg_right (le_max_left (β^2*C) (β*C)) (Real.rpow_nonneg (show (0:ℝ)≤(n:ℝ) by positivity) (7/15:ℝ)))
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (show (0:ℝ)≤(n:ℝ) by positivity) (-(11/12:ℝ)))).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm0 hβ.le)
  · exact (mul_le_mul_of_nonneg_left hm1 hβ.le).trans
      (by simpa only [Co,←mul_assoc] using mul_le_mul_of_nonneg_right (le_max_right (β^2*C) (β*C)) (Real.rpow_nonneg (show (0:ℝ)≤(n:ℝ) by positivity) (-(2/3:ℝ))))

theorem fixed_temperature_tails_of_energy (β A xstar c C : ℝ) (hβ : 0<β)
    (hA : 0<A) (hxs : 0<xstar) (hc : 0<c) (hC : 0<C)
    (N0 : ℕ) (hN0 : 1≤N0)
    (henergy : ∀n : ℕ,N0≤n→∀x : ℝ,A*(n:ℝ)^(-(2/3:ℝ))≤x→x≤xstar→
      Real.exp (-C*(n:ℝ)*x^(6/5:ℝ))≤
        (couplingLaw n).real {g | (n:ℝ)*(scalarEnergyValue β 0+x)≤energyFreeEnergy n β g} ∧
      (couplingLaw n).real {g | (n:ℝ)*(scalarEnergyValue β 0+x)≤energyFreeEnergy n β g}≤
        Real.exp (-c*(n:ℝ)*x^(6/5:ℝ))) :
    ∃Ao xo co Co : ℝ,0<Ao ∧ 0<xo ∧ 0<co ∧ 0<Co ∧ ∀n : ℕ,N0≤n→
      ∀x : ℝ,Ao*(n:ℝ)^(-(2/3:ℝ))≤x→x≤xo→
        Real.exp (-Co*(n:ℝ)*x^(6/5:ℝ))≤
          (couplingLaw n).real {g | (n:ℝ)*(parisiPDEValue β 0+x)≤logPartition n β g} ∧
        (couplingLaw n).real {g | (n:ℝ)*(parisiPDEValue β 0+x)≤logPartition n β g}≤
          Real.exp (-co*(n:ℝ)*x^(6/5:ℝ)) := by
  refine ⟨β*A,β*xstar,c/β^(6/5:ℝ),C/β^(6/5:ℝ),
    by positivity,by positivity,by positivity,by positivity,?_⟩
  intro n hn x hxlo hxhi
  have hxlow : A*(n:ℝ)^(-(2/3:ℝ))≤x/β := by
    apply (le_div_iff₀ hβ).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hxlo
  have hxhigh : x/β≤xstar := (div_le_iff₀ hβ).mpr (by simpa only [mul_comm] using hxhi)
  have hh:=henergy n hn (x/β) hxlow hxhigh
  have hnR : 0<(n:ℝ) := by exact_mod_cast Nat.zero_lt_one.trans_le (hN0.trans hn)
  have hx : 0<x := (by positivity : 0<β*A*(n:ℝ)^(-(2/3:ℝ))).trans_le hxlo
  rw [original_free_energy_tail_eq_energy_tail n β x hβ]
  convert hh using 1 <;> congr 1 <;>
    rw [Real.div_rpow hx.le hβ.le] <;> ring

end QuantitativePaper
