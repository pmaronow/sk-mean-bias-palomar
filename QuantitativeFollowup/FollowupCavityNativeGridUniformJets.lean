module
public import QuantitativeFollowup.FollowupCavityNativeTerminalApproximation
public import QuantitativeFollowup.FollowupCavityStreamingUniformJets

@[expose] public section

/-! True derivatives of the fixed-observation grid laws have bounds
independent of the profile mesh. The finite realization is fixed over
the entire closed physical interpolation interval. -/
noncomputable section
open Set
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityWithinJet_congr_eqOn {f g : ℝ→ℝ} {S : Set ℝ}
    (h : Set.EqOn f g S) (r : ℕ) : Set.EqOn (withinJet f S r) (withinJet g S r) S := by
  induction r with
  | zero => exact h
  | succ r ih =>
      intro u hu
      exact derivWithin_congr ih (ih hu)

theorem hasDerivWithinAt_followupCavityNativeGrid_withinJet
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (N r : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let f:=followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q T F
    HasDerivWithinAt (withinJet f (Icc (0:ℝ) 1) r)
      (withinJet f (Icc (0:ℝ) 1) (r+1) u) (Icc (0:ℝ) 1) u := by
  classical
  dsimp only
  let C:=∑σ,|F σ|
  have hC:0≤C:=Finset.sum_nonneg (fun σ _=>abs_nonneg _)
  have hF (σ):|F σ|≤C:=Finset.single_le_sum (fun σ _=>abs_nonneg (F σ)) (Finset.mem_univ σ)
  obtain ⟨K,s,A,_,hszero,has,_,_,he⟩:=exists_finite_cavityStreamingAtom_grid_representation β ρ hβ hρ
    μ a hfloor q hq hJ hzero htop T F C hC hF N
  have hEq : Set.EqOn (A.eval β ρ hβ hρ s a)
      (followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q T F)
      (Icc (0:ℝ) 1):=fun v hv=>he v hv
  have hh:=hasDerivWithinAt_cavityStreamingAtom_withinJet hn β ρ hβ hρ s a ha has hszero A r u hu
  rw [cavityWithinJet_congr_eqOn hEq (r+1) hu] at hh
  exact hh.congr (fun v hv=>(cavityWithinJet_congr_eqOn hEq r hv).symm)
    ((cavityWithinJet_congr_eqOn hEq r hu).symm)

theorem abs_followupCavityNativeGrid_withinJet_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (N r : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ
      (Paper.parisiGridMeasure μ N) a q T F) (Icc (0:ℝ) 1) r u|≤
      growth (7*β^2) (FiniteCascadeGenealogy.leafCount (asGenealogy T)) r*C := by
  obtain ⟨K,s,A,_,hszero,has,hcomp,hbound,he⟩:=exists_finite_cavityStreamingAtom_grid_representation β ρ hβ hρ
    μ a hfloor q hq hJ hzero htop T F C hC hF N
  have hEq : Set.EqOn (A.eval β ρ hβ hρ s a)
      (followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q T F)
      (Icc (0:ℝ) 1):=fun v hv=>he v hv
  have hh:=abs_cavityStreamingAtom_withinJet_le hn β ρ hβ hρ s a ha has hszero A r u hu
  rw [hcomp,hbound,cavityWithinJet_congr_eqOn hEq r hu] at hh
  exact hh

end QuantitativeFollowup
