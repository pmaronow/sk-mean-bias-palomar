module
public import QuantitativePaper.ShortVarianceMeanUniform
public import QuantitativePaper.UniformScalarTrialFifthOrder

@[expose] public section

/-! Literal main Lemma 5.8, with the true finite SK variance and mean.
The temperature-uniform fifth-order trial bound is fully discharged. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper

def ShortVarianceMeanTarget : Prop :=
  ∀β0 : ℝ,1<β0→∃c : ℝ,0<c ∧ ∀n : ℕ,0<n→∀β : ℝ,β0≤β→
    c*((variance (energyFreeEnergy n β) (couplingLaw n)+1/2)/(n:ℝ))^(5/4:ℝ)≤
      energyMeanDeficit n β

theorem short_variance_mean : ShortVarianceMeanTarget := by
  intro β0 hβ0
  obtain ⟨C1,L,hC1,hL,hL1,hLβ,htrial⟩:=scalar_floor_uniform_fifth_order β0 hβ0
  exact energyMeanDeficit_variance_power_of_uniform_trial β0 C1 L
    (zero_lt_one.trans hβ0) (zero_le_one.trans hC1) hL hLβ
    (fun β hβ lam hlam=>(htrial β hβ lam ⟨hlam.1.le,hlam.2⟩).2)

end QuantitativePaper
