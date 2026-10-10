module
public import QuantitativeFollowup.FollowupCavityNativeStreamingRegularity
public import QuantitativeFollowup.FollowupCavityCppNativeFunction

@[expose] public section

/-! Genuine native Cpp smoothness and its first two finite-grid jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem cppSchedule_antitone (p : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule p) := by
  apply antitone_nat_of_succ_le
  intro i
  rcases i with _|_|i
  · exact p.property.2
  · exact p.property.1
  · exact le_rfl

private theorem nativeCppTest_derivatives (hn : 0<n) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (T : FiniteTerminalGenealogy 2) (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    ∀r u,u∈Icc (0:ℝ) 1→HasDerivWithinAt
      (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule p) T F) (Icc 0 1) r)
      (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule p) T F) (Icc 0 1) (r+1) u) (Icc 0 1) u :=
  fun r u hu=>hasDerivWithinAt_followupCavityNativeTerminalExpectation_withinJet hn β ρ hβ hρ
    μ a ha hfloor _ (cppSchedule_antitone p) (by norm_num) rfl rfl T F r u hu

theorem contDiffOn_followupCavityCppFunction (hn : 0<n) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap) :
    ContDiffOn ℝ ∞ (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) := by
  have h (T : FiniteTerminalGenealogy 2) (F : TerminalSpins (Configuration (n+1)) T→ℝ) :=
    contDiffOn_followupCavityNativeTerminalExpectation hn β ρ hβ hρ μ a ha hfloor
      (anisotropicBinaryObservationSchedule p) (cppSchedule_antitone p) (by norm_num) rfl rfl T F
  exact (h _ (cavityCppFourTerminalTest n p)).sub
    ((h _ (cavityCppEpsilonTerminalTest n)).mul (h _ (cavityCppTauTerminalTest n p)))

private theorem cppJet_one (f g h : ℝ→ℝ)
    (hD : ∀k∈({f,g,h}:Set (ℝ→ℝ)),∀r u,u∈Icc (0:ℝ) 1→
      HasDerivWithinAt (withinJet k (Icc 0 1) r) (withinJet k (Icc 0 1) (r+1) u) (Icc 0 1) u)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    withinJet (fun x=>f x-g x*h x) (Icc 0 1) 1 u=
      withinJet f (Icc 0 1) 1 u-withinJet g (Icc 0 1) 1 u*h u-g u*withinJet h (Icc 0 1) 1 u := by
  have hf:=hD f (by simp) 0 u hu
  have hg:=hD g (by simp) 0 u hu
  have hh:=hD h (by simp) 0 u hu
  have hd:=(hf.fun_sub (hg.fun_mul hh)).derivWithin (uniqueDiffOn_Icc_zero_one u hu)
  change derivWithin (fun x=>f x-g x*h x) (Icc 0 1) u=_
  simp only [withinJet] at hd ⊢
  rw [hd]
  ring

private theorem cppJet_two (f g h : ℝ→ℝ)
    (hD : ∀k∈({f,g,h}:Set (ℝ→ℝ)),∀r u,u∈Icc (0:ℝ) 1→
      HasDerivWithinAt (withinJet k (Icc 0 1) r) (withinJet k (Icc 0 1) (r+1) u) (Icc 0 1) u)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    withinJet (fun x=>f x-g x*h x) (Icc 0 1) 2 u=
      withinJet f (Icc 0 1) 2 u-withinJet g (Icc 0 1) 2 u*h u-
        2*withinJet g (Icc 0 1) 1 u*withinJet h (Icc 0 1) 1 u-g u*withinJet h (Icc 0 1) 2 u := by
  have hf:=hD f (by simp) 1 u hu
  have hg:=hD g (by simp) 1 u hu
  have hh:=hD h (by simp) 1 u hu
  have hg0:=hD g (by simp) 0 u hu
  have hh0:=hD h (by simp) 0 u hu
  have hd:=((hf.fun_sub (hg.fun_mul hh0)).fun_sub (hg0.fun_mul hh)).derivWithin
    (uniqueDiffOn_Icc_zero_one u hu)
  change derivWithin (withinJet (fun x=>f x-g x*h x) (Icc 0 1) 1) (Icc 0 1) u=_
  rw [derivWithin_congr (fun v hv=>cppJet_one f g h hD v hv) (cppJet_one f g h hD u hu)]
  simp only [withinJet] at hd ⊢
  rw [hd]
  ring

theorem tendsto_followupCavityCppFunction_grid_first_two_jets (hn : 0<n) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (r : ℕ) (hr : r≤2) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Tendsto (fun N=>withinJet (followupCavityCppFunction n β ρ hβ hρ
        (Paper.parisiGridMeasure μ N) a p) (Icc 0 1) r u) atTop
      (𝓝 (withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) r u)) := by
  let e (ν : Paper.ParisiMeasure) (T : FiniteTerminalGenealogy 2)
      (F : TerminalSpins (Configuration (n+1)) T→ℝ) :=
    followupCavityNativeTerminalExpectation n β ρ hβ hρ ν a (anisotropicBinaryObservationSchedule p) T F
  let f (ν):=e ν cavityFourObservationTree (cavityCppFourTerminalTest n p)
  let g (ν):=e ν anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n)
  let h (ν):=e ν anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p)
  have ht (T : FiniteTerminalGenealogy 2) (F : TerminalSpins (Configuration (n+1)) T→ℝ) (r : ℕ) :
      Tendsto (fun N=>withinJet (e (Paper.parisiGridMeasure μ N) T F) (Icc 0 1) r u) atTop
        (𝓝 (withinJet (e μ T F) (Icc 0 1) r u)) :=
    (followupCavityNativeTerminalExpectation_jet_limit hn β ρ hβ hρ μ a ha hfloor
      _ (cppSchedule_antitone p) (by norm_num) rfl rfl T F).1 r |>.tendsto_at hu
  have hlim (r : ℕ) :=ht cavityFourObservationTree (cavityCppFourTerminalTest n p) r
  have glim (r : ℕ) :=ht anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n) r
  have hlim' (r : ℕ) :=ht anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p) r
  have hd : ∀k∈({f μ,g μ,h μ}:Set (ℝ→ℝ)),∀r u,u∈Icc (0:ℝ) 1→
      HasDerivWithinAt (withinJet k (Icc 0 1) r) (withinJet k (Icc 0 1) (r+1) u) (Icc 0 1) u := by
    intro k hk
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hk
    rcases hk with rfl|rfl|rfl <;> exact nativeCppTest_derivatives hn β ρ hβ hρ μ a ha hfloor p _ _
  have hdj (N : ℕ) : ∀k∈({f (Paper.parisiGridMeasure μ N),g (Paper.parisiGridMeasure μ N),
      h (Paper.parisiGridMeasure μ N)}:Set (ℝ→ℝ)),∀r u,u∈Icc (0:ℝ) 1→
      HasDerivWithinAt (withinJet k (Icc 0 1) r) (withinJet k (Icc 0 1) (r+1) u) (Icc 0 1) u := by
    intro k hk r v hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hk
    rcases hk with rfl|rfl|rfl <;> exact hasDerivWithinAt_followupCavityNativeGrid_withinJet hn β ρ hβ hρ
      μ a ha hfloor _ (cppSchedule_antitone p) (by norm_num) rfl rfl _ _ N r v hv
  change Tendsto (fun N=>withinJet (fun x=>f (Paper.parisiGridMeasure μ N) x-
    g (Paper.parisiGridMeasure μ N) x*h (Paper.parisiGridMeasure μ N) x) (Icc 0 1) r u) atTop
    (𝓝 (withinJet (fun x=>f μ x-g μ x*h μ x) (Icc 0 1) r u))
  interval_cases r
  · exact (hlim 0).sub ((glim 0).mul (hlim' 0))
  · simp_rw [cppJet_one _ _ _ (hdj _) u hu,cppJet_one _ _ _ hd u hu]
    exact ((hlim 1).sub ((glim 1).mul (hlim' 0))).sub ((glim 0).mul (hlim' 1))
  · simp_rw [cppJet_two _ _ _ (hdj _) u hu,cppJet_two _ _ _ hd u hu]
    exact (((hlim 2).sub ((glim 2).mul (hlim' 0))).sub
      (((glim 1).const_mul 2).mul (hlim' 1))).sub ((glim 0).mul (hlim' 2))

end QuantitativeFollowup
