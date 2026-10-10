module
public import QuantitativeFollowup.FollowupCavityCppNativeJets

@[expose] public section

/-! Literal product differentiation of the actual native four- and binary-
terminal factors. The binary product uses independent expectations. -/
noncomputable section
open Set
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private theorem cppFactorSchedule_antitone (p : Paper.Overlap):
    Antitone (anisotropicBinaryObservationSchedule p) := by
  apply antitone_nat_of_succ_le
  intro j
  rcases j with _|_|j
  · exact p.property.2
  · exact p.property.1
  · exact le_rfl

private theorem cppFactor_hasDeriv (hn : 0<n) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (T : FiniteTerminalGenealogy 2) (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (r : ℕ) (u : ℝ) (hu:u∈Icc (0:ℝ) 1):
    HasDerivWithinAt (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) T F) (Icc 0 1) r)
      (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) T F) (Icc 0 1) (r+1) u) (Icc 0 1) u :=
  hasDerivWithinAt_followupCavityNativeTerminalExpectation_withinJet hn β ρ hβ hρ μ a ha hfloor
    _ (cppFactorSchedule_antitone p) (by norm_num) rfl rfl T F r u hu

theorem followupCavityCppFunction_firstWithinJet_eq_factors
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (u : ℝ) (hu:u∈Icc (0:ℝ) 1):
    let f:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) cavityFourObservationTree (cavityCppFourTerminalTest n p)
    let g:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n)
    let h:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p)
    withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 u=
      withinJet f (Icc 0 1) 1 u-withinJet g (Icc 0 1) 1 u*h u-g u*withinJet h (Icc 0 1) 1 u := by
  dsimp only
  have hf:=cppFactor_hasDeriv hn β ρ hβ hρ μ a ha hfloor p cavityFourObservationTree
    (cavityCppFourTerminalTest n p) 0 u hu
  have hg:=cppFactor_hasDeriv hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppEpsilonTerminalTest n) 0 u hu
  have hh:=cppFactor_hasDeriv hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppTauTerminalTest n p) 0 u hu
  have hd:=(hf.fun_sub (hg.fun_mul hh)).derivWithin (uniqueDiffOn_Icc_zero_one u hu)
  simp only [withinJet] at hd ⊢
  change derivWithin (fun x=>
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) cavityFourObservationTree (cavityCppFourTerminalTest n p) x-
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n) x*
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p) x)
    (Icc (0:ℝ) 1) u=_
  rw [hd]
  ring

theorem followupCavityCppFunction_secondWithinJet_eq_factors
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (u : ℝ) (hu:u∈Icc (0:ℝ) 1):
    let f:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) cavityFourObservationTree (cavityCppFourTerminalTest n p)
    let g:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n)
    let h:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p)
    withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 2 u=
      withinJet f (Icc 0 1) 2 u-withinJet g (Icc 0 1) 2 u*h u-
        2*withinJet g (Icc 0 1) 1 u*withinJet h (Icc 0 1) 1 u-g u*withinJet h (Icc 0 1) 2 u := by
  dsimp only
  have hf:=cppFactor_hasDeriv hn β ρ hβ hρ μ a ha hfloor p cavityFourObservationTree
    (cavityCppFourTerminalTest n p) 1 u hu
  have hg:=cppFactor_hasDeriv hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppEpsilonTerminalTest n) 1 u hu
  have hh:=cppFactor_hasDeriv hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppTauTerminalTest n p) 1 u hu
  have hg0:=cppFactor_hasDeriv hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppEpsilonTerminalTest n) 0 u hu
  have hh0:=cppFactor_hasDeriv hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppTauTerminalTest n p) 0 u hu
  have hd:=((hf.fun_sub (hg.fun_mul hh0)).fun_sub (hg0.fun_mul hh)).derivWithin
    (uniqueDiffOn_Icc_zero_one u hu)
  change derivWithin (withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1) (Icc 0 1) u=_
  rw [derivWithin_congr
    (fun v hv=>followupCavityCppFunction_firstWithinJet_eq_factors hn β ρ hβ hρ μ a ha hfloor p v hv)
    (followupCavityCppFunction_firstWithinJet_eq_factors hn β ρ hβ hρ μ a ha hfloor p u hu)]
  simp only [withinJet] at hd ⊢
  rw [hd]
  ring

end QuantitativeFollowup
