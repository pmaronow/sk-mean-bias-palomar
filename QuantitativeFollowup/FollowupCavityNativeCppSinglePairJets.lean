module
public import QuantitativeFollowup.FollowupCavityNativeSecondStreamingCubic
public import QuantitativeFollowup.FollowupCavityCppNativeFunction

@[expose] public section

/-! The actual four-mark and rest-pair factors of Cpp retain one-defect
cubic second-jet bounds. Every branch in the fixed sibling tree splits at p. -/
noncomputable section
open Set
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private theorem nativeCppPairSchedule_antitone (p : Paper.Overlap):
    Antitone (anisotropicBinaryObservationSchedule p) := by
  apply antitone_nat_of_succ_le
  intro j
  rcases j with _|_|j
  · exact p.property.2
  · exact p.property.1
  · exact le_rfl

private theorem cppFour_onePair_domination (p : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1)) cavityFourObservationTree):
    |cavityCppFourTerminalTest n p σ|≤
      |cavitySpinOverlapDefect n
        (anisotropicBinaryObservationSchedule p
          (observationCommonLevel cavityFourObservationTree
            (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inr ()))))
        (observationLeafTerminalSpin cavityFourObservationTree (Sum.inr (Sum.inl ())) σ)
        (observationLeafTerminalSpin cavityFourObservationTree (Sum.inr (Sum.inr ())) σ)| := by
  have hs (b : Bool):|Paper.spinSign b|=1:=by cases b <;> norm_num [Paper.spinSign]
  simp only [cavityCppFourTerminalTest,abs_mul,hs,one_mul]
  change |cavityRestOverlap n σ.2.1 σ.2.2-(p:ℝ)|≤|cavitySpinOverlapDefect n p σ.2.1 σ.2.2|
  exact (cavitySpinOverlapDefect_abs_eq_rest n p σ.2.1 σ.2.2).ge

private theorem cppTau_onePair_domination (p : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1)) anisotropicBinaryObservationTree):
    |cavityCppTauTerminalTest n p σ|≤
      |cavitySpinOverlapDefect n
        (anisotropicBinaryObservationSchedule p
          (observationCommonLevel anisotropicBinaryObservationTree (Sum.inl ()) (Sum.inr ())))
        (observationLeafTerminalSpin anisotropicBinaryObservationTree (Sum.inl ()) σ)
        (observationLeafTerminalSpin anisotropicBinaryObservationTree (Sum.inr ()) σ)| := by
  change |cavityRestOverlap n σ.1 σ.2-(p:ℝ)|≤|cavitySpinOverlapDefect n p σ.1 σ.2|
  exact (cavitySpinOverlapDefect_abs_eq_rest n p σ.1 σ.2).ge

theorem abs_followupCavityCppFour_secondWithinJet_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1):
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule p) cavityFourObservationTree (cavityCppFourTerminalTest n p))
        (Icc (0:ℝ) 1) 2 u|≤
      (followupCavityAlpha n β ρ/2)^2*cavitySecondStreamingCost 4*
        (cavityThirdMoment D μ a+3*cavityCubicPairMoment D μ a p) := by
  have hh:=abs_followupCavityNativeTerminalExpectation_secondWithinJet_cubic_le hn β ρ hβ hρ μ a ha hfloor
    (anisotropicBinaryObservationSchedule p) (nativeCppPairSchedule_antitone p) (by norm_num) rfl rfl
    cavityFourObservationTree (cavityCppFourTerminalTest n p)
    (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inr ())) (cppFour_onePair_domination p) u hu
  convert! hh using 1 <;>
    simp only [cavityFourObservationTree,asGenealogy,FiniteCascadeGenealogy.leafCount,
      finiteCascadeUnweightedBranchSum,anisotropicBinaryObservationSchedule] <;> norm_num <;> ring

theorem abs_followupCavityCppTau_secondWithinJet_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1):
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p))
        (Icc (0:ℝ) 1) 2 u|≤
      (followupCavityAlpha n β ρ/2)^2*cavitySecondStreamingCost 2*
        (cavityThirdMoment D μ a+cavityCubicPairMoment D μ a p) := by
  have hh:=abs_followupCavityNativeTerminalExpectation_secondWithinJet_cubic_le hn β ρ hβ hρ μ a ha hfloor
    (anisotropicBinaryObservationSchedule p) (nativeCppPairSchedule_antitone p) (by norm_num) rfl rfl
    anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p)
    (Sum.inl ()) (Sum.inr ()) (cppTau_onePair_domination p) u hu
  convert! hh using 1 <;>
    simp only [anisotropicBinaryObservationTree,asGenealogy,FiniteCascadeGenealogy.leafCount,
      finiteCascadeUnweightedBranchSum,anisotropicBinaryObservationSchedule] <;> norm_num

end QuantitativeFollowup
