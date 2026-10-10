module
public import QuantitativeFollowup.FollowupCavityNativeGridUniformJets
public import FourPapersCommon.FiniteStreamingClosedJetLimits
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Actual closed-interval native streaming jets are limits of the genuine
finite jets. No extension outside the physical interpolation interval is used. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem followupCavityNativeTerminalExpectation_jet_limit
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    (∀ r, TendstoUniformlyOn
      (fun N=>withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ
        (Paper.parisiGridMeasure μ N) a q T F) (Icc (0:ℝ) 1) r)
      (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
        (Icc (0:ℝ) 1) r) atTop (Icc (0:ℝ) 1)) ∧
    (∀ r u, u∈Icc (0:ℝ) 1→HasDerivWithinAt
      (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
        (Icc (0:ℝ) 1) r)
      (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
        (Icc (0:ℝ) 1) (r+1) u) (Icc (0:ℝ) 1) u) := by
  classical
  let C0:=∑σ,|F σ|
  have hC0:0≤C0:=Finset.sum_nonneg (fun σ _=>abs_nonneg _)
  have hF (σ):|F σ|≤C0:=Finset.single_le_sum (fun σ _=>abs_nonneg (F σ)) (Finset.mem_univ σ)
  let C : ℕ→ℝ≥0:=fun r=>⟨growth (7*β^2)
    (FiniteCascadeGenealogy.leafCount (asGenealogy T)) r*C0,
    mul_nonneg (growth_nonneg _ (by positivity) _ _) hC0⟩
  apply tendstoUniformlyOn_actual_withinJets_on_Icc
    (fun N r=>withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ
      (Paper.parisiGridMeasure μ N) a q T F) (Icc (0:ℝ) 1) r)
    (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
    (fun N r u hu=>hasDerivWithinAt_followupCavityNativeGrid_withinJet hn β ρ hβ hρ
      μ a ha hfloor q hq hJ hzero htop T F N r u hu) C
  · intro N r _ u hu
    have hh:=abs_followupCavityNativeGrid_withinJet_le hn β ρ hβ hρ
      μ a ha hfloor q hq hJ hzero htop T F C0 hC0 hF N r u hu
    convert! hh using 1
  · intro u _
    exact tendsto_followupCavityNativeTerminalExpectation_grid β ρ hβ hρ μ a q hq T F u

theorem hasDerivWithinAt_followupCavityNativeTerminalExpectation_withinJet
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (r : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) r)
      (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
        (Icc (0:ℝ) 1) (r+1) u) (Icc (0:ℝ) 1) u :=
  (followupCavityNativeTerminalExpectation_jet_limit hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F).2 r u hu

private theorem contDiffOn_withinJet_of_actual_derivatives (g : ℝ→ℝ)
    (hD : ∀r u,u∈Icc (0:ℝ) 1→HasDerivWithinAt (withinJet g (Icc 0 1) r)
      (withinJet g (Icc 0 1) (r+1) u) (Icc 0 1) u) (r : ℕ) :
    ContDiffOn ℝ ∞ (withinJet g (Icc (0:ℝ) 1) r) (Icc (0:ℝ) 1) := by
  have hs:=uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)
  have hall (N : ℕ) : ∀r,ContDiffOn ℝ N (withinJet g (Icc (0:ℝ) 1) r) (Icc (0:ℝ) 1) := by
    induction N with
    | zero => intro r; exact contDiffOn_zero.mpr (fun u hu=>(hD r u hu).continuousWithinAt)
    | succ N ih =>
      intro r
      rw [show ((N+1:ℕ):ℕ∞ω)=(N:ℕ∞ω)+1 by simp,contDiffOn_succ_iff_derivWithin hs]
      refine ⟨fun u hu=>(hD r u hu).differentiableWithinAt,?_,?_⟩
      · simp
      · exact ih (r+1)
  exact contDiffOn_infty.mpr (fun N=>hall N r)

theorem contDiffOn_followupCavityNativeTerminalExpectation_withinJet
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (r : ℕ) :
    ContDiffOn ℝ ∞ (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) r) (Icc (0:ℝ) 1) :=
  contDiffOn_withinJet_of_actual_derivatives _
    (fun r u hu=>hasDerivWithinAt_followupCavityNativeTerminalExpectation_withinJet hn β ρ hβ hρ
      μ a ha hfloor q hq hJ hzero htop T F r u hu) r

theorem contDiffOn_followupCavityNativeTerminalExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    ContDiffOn ℝ ∞ (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) :=
  contDiffOn_followupCavityNativeTerminalExpectation_withinJet hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F 0

end QuantitativeFollowup
