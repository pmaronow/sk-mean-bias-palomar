module
public import QuantitativeFollowup.FollowupCavityCppNativeFactorJets
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingWeakJets

@[expose] public section

/-! The actual native covariance's initial first jet is the genuine limit
along atom-preserving finite profiles. This is a consequence of the closed
terminal-observation jet convergence, without a response identity input. -/
noncomputable section
open Set Filter MeasureTheory FourPapersCommon QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
open SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

private theorem nativeFirstJet_binary_antitone (p : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule p):=by
  apply antitone_nat_of_succ_le
  intro j
  cases j with
  | zero => exact p.property.2
  | succ j => cases j with
    | zero => exact p.property.1
    | succ j => exact le_refl _

theorem tendsto_followupCavityCpp_firstJet_zero_preserving
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hS : zeroOverlap∈S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (p : Paper.Overlap) :
    Tendsto (fun N=>withinJet (followupCavityCppFunction n β ρ hβ hρ
      (FRSB.preservingMeasure μ S N) a p) (Icc (0:ℝ) 1) 1 0) atTop
      (𝓝 (withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 0)):=by
  have hzero:(0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩
  have hfloorN (N : ℕ):a≤Paper.parisiCDF (FRSB.preservingMeasure μ S N) 0:=by
    change a ≤ Paper.parisiCDF (FRSB.preservingMeasure μ S N) (zeroOverlap:ℝ)
    rw [FRSB.preservingMeasure_cdf_mass μ S N zeroOverlap hS]
    exact hfloor
  have hj (T : FiniteTerminalGenealogy 2)
      (F : TerminalSpins (Configuration (n+1)) T→ℝ) (r : ℕ):=
    (tendstoUniformlyOn_followupCavityNativeJets_preserving hn β ρ hβ hρ
      μ S hS a ha hfloor (anisotropicBinaryObservationSchedule p)
      (nativeFirstJet_binary_antitone p) (by norm_num) rfl rfl T F r).tendsto_at hzero
  have he:=((hj cavityFourObservationTree (cavityCppFourTerminalTest n p) 1).sub
    ((hj anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n) 1).mul
      (hj anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p) 0))).sub
        ((hj anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n) 0).mul
          (hj anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p) 1))
  convert he using 1
  · funext N
    exact followupCavityCppFunction_firstWithinJet_eq_factors hn β ρ hβ hρ
      (FRSB.preservingMeasure μ S N) a ha (hfloorN N) p 0 hzero
  · exact congrArg nhds (followupCavityCppFunction_firstWithinJet_eq_factors
      hn β ρ hβ hρ μ a ha hfloor p 0 hzero)

end QuantitativeFollowup
