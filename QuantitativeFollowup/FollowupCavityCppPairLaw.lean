module
public import QuantitativeFollowup.FollowupCavityCppNativeFunction

@[expose] public section

/-! Binary Cpp factors are genuine two-fresh spin expectations. The cube of
the rest factor is exactly the actual local third moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem followupCavityCppBinary_expectation_eq_integral
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap)
    (F : TerminalSpins (Configuration (n+1)) anisotropicBinaryObservationTree→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree F u=
    ∫σ,F σ∂(anisotropicBinarySpinProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
      μ a p : Measure (Configuration (n+1)×Configuration (n+1))) := by
  rw [followupCavityNativeTerminalExpectation_eq β ρ hβ hρ μ a _ _ _ u hu,
    cavityBinaryObservation_energy_integral]

theorem integral_cavityCppTauTerminalTest_abs_cube_eq
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    (∫σ,|cavityCppTauTerminalTest n p σ|^3
      ∂(anisotropicBinarySpinProbability D μ a p : Measure (Configuration (n+1)×Configuration (n+1))))=
    cavityCubicPairMoment D μ a p := rfl

theorem abs_followupCavityCppEpsilonExpectation_le_one
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree
      (cavityCppEpsilonTerminalTest n) u|≤1 := by
  rw [followupCavityCppBinary_expectation_eq_integral β ρ hβ hρ μ a p _ u hu]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(anisotropicBinarySpinProbability (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p :
        Measure (Configuration (n+1)×Configuration (n+1))))
      (f:=fun σ : Configuration (n+1)×Configuration (n+1)=>cavityCppEpsilonTerminalTest n σ) (C:=1)
      (.of_forall fun σ=>by simpa only [Real.norm_eq_abs] using cavityCppEpsilonTerminalTest_abs_le σ)

end QuantitativeFollowup
