module
public import QuantitativeFollowup.FollowupCavityNativeStreamingRegularity

@[expose] public section

/-! Native bounds follow by order closure from actual grid jets. -/
noncomputable section
open Set Filter
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem abs_followupCavityNativeTerminalExpectation_withinJet_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (r : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) r u|≤
        growth (7*β^2) (FiniteCascadeGenealogy.leafCount (asGenealogy T)) r*C := by
  have ht:=(followupCavityNativeTerminalExpectation_jet_limit hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F).1 r |>.tendsto_at hu
  exact le_of_tendsto ht.abs (.of_forall (fun N=>abs_followupCavityNativeGrid_withinJet_le
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF N r u hu))

end QuantitativeFollowup
