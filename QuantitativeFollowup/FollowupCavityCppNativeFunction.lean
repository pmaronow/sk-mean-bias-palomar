module
public import QuantitativeFollowup.FollowupCavityNativeTerminalApproximation
public import QuantitativeFollowup.FollowupCavityCppFourDescendantPrinted
public import QuantitativeFollowup.FollowupCavityFourObservationLaw
public import QuantitativeFollowup.FollowupCavityCubicComparison

@[expose] public section

/-! The native Cpp curve is a literal polynomial of three fixed terminal
observation tests. This representation contains no response assumption. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityCppFourTerminalTest (n : ℕ) (p : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1)) cavityFourObservationTree) : ℝ :=
  Paper.spinSign (σ.1.1 (Fin.last n))*Paper.spinSign (σ.1.2 (Fin.last n))*
    (cavityRestOverlap n σ.2.1 σ.2.2-(p:ℝ))

def cavityCppEpsilonTerminalTest (n : ℕ)
    (σ : TerminalSpins (Configuration (n+1)) anisotropicBinaryObservationTree) : ℝ :=
  Paper.spinSign (σ.1 (Fin.last n))*Paper.spinSign (σ.2 (Fin.last n))

def cavityCppTauTerminalTest (n : ℕ) (p : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1)) anisotropicBinaryObservationTree) : ℝ :=
  cavityRestOverlap n σ.1 σ.2-(p:ℝ)

theorem cavityCppEpsilonTerminalTest_abs_le (σ) : |cavityCppEpsilonTerminalTest n σ|≤1 := by
  have hs (b : Bool):|Paper.spinSign b|=1:=by cases b <;> norm_num [Paper.spinSign]
  simp only [cavityCppEpsilonTerminalTest,abs_mul,hs,one_mul,le_refl]

theorem cavityCppTauTerminalTest_abs_le (p : Paper.Overlap) (σ) :
    |cavityCppTauTerminalTest n p σ|≤2 := by
  rw [cavityCppTauTerminalTest,←cavitySpinOverlapDefect_abs_eq_rest]
  exact cavitySpinOverlapDefect_abs_le_two n p p.property _ _

theorem cavityCppFourTerminalTest_abs_le (p : Paper.Overlap) (σ) :
    |cavityCppFourTerminalTest n p σ|≤2 := by
  have hs (b : Bool):|Paper.spinSign b|=1:=by cases b <;> norm_num [Paper.spinSign]
  simp only [cavityCppFourTerminalTest,abs_mul,hs,one_mul]
  rw [←cavitySpinOverlapDefect_abs_eq_rest]
  exact cavitySpinOverlapDefect_abs_le_two n p p.property _ _

def followupCavityCppFunction (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) (u : ℝ) : ℝ :=
  followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) cavityFourObservationTree (cavityCppFourTerminalTest n p) u-
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n) u*
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p) u

theorem followupCavityCppFunction_eq_actual (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityCppFunction n β ρ hβ hρ μ a p u=
      followupCavityCpp n β ρ hβ hρ μ a u hu p := by
  rw [followupCavityCpp_eq_psi_four_sub_product]
  unfold followupCavityCppFunction
  rw [followupCavityNativeTerminalExpectation_eq β ρ hβ hρ μ a _ _ _ u hu,
    followupCavityNativeTerminalExpectation_eq β ρ hβ hρ μ a _ _ _ u hu,
    followupCavityNativeTerminalExpectation_eq β ρ hβ hρ μ a _ _ _ u hu,
    cavityFourObservation_energy_integral,cavityBinaryObservation_energy_integral,
    cavityBinaryObservation_energy_integral,anisotropicBinarySpinProbability_eq_fresh_pair]
  simp only [cavityCppPsiFour,cavityCppPsiEpsilon,cavityCppPsiTau]
  congr 1
  congr 1
  · exact integral_map (μ:=anisotropicFreshTerminalPairLaw
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p) measurable_snd.aemeasurable
      (measurable_of_finite (cavityCppEpsilonTerminalTest n)).aestronglyMeasurable
  · exact integral_map (μ:=anisotropicFreshTerminalPairLaw
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p) measurable_snd.aemeasurable
      (measurable_of_finite (cavityCppTauTerminalTest n p)).aestronglyMeasurable

theorem followupCavityCppFunction_zero (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    followupCavityCppFunction n β ρ hβ hρ μ a p 0=0 := by
  rw [followupCavityCppFunction_eq_actual β ρ hβ hρ μ a p 0 ⟨le_rfl,zero_le_one⟩]
  exact followupCavityCpp_zero n β ρ hβ hρ μ a p

end QuantitativeFollowup
