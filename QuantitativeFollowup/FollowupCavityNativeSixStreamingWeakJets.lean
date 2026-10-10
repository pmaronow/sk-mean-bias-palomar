module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingApproximation
public import QuantitativeFollowup.FollowupCavityNativeStreamingBounds

@[expose] public section

/-! Actual native jets converge under arbitrary floor-preserving weak
profile approximation. In particular, the atom-preserving approximation
can replace the canonical grids in the literal streaming passage. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction ContDiff NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem tendsto_followupCavityNativeTerminalExpectation_of_weak
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated]
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    {μj : L→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (u : ℝ) :
    Tendsto (fun N=>followupCavityNativeTerminalExpectation n β ρ hβ hρ (μj N) a q T F u) l
      (𝓝 (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F u)) := by
  classical
  by_cases hu:u∈Icc (0:ℝ) 1
  · simp only [followupCavityNativeTerminalExpectation,dif_pos hu]
    let C:ℝ:=∑σ:TerminalSpins (Configuration (n+1)) T,‖F σ‖
    have hb (σ:TerminalSpins (Configuration (n+1)) T):‖F σ‖≤C:=
      Finset.single_le_sum (fun σ _=>norm_nonneg (F σ)) (Finset.mem_univ σ)
    let G:CavityPathRecordSpace T (n+1)→ᵇℝ:=BoundedContinuousFunction.mkOfBound
      ⟨fun z=>F (finiteCascadeRecordTerminalSpins T z.2),
        (continuous_of_discreteTopology (f:=F)).comp
          ((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_snd)⟩
      (2*C) (fun z w=>(dist_le_norm_add_norm _ _).trans
        ((add_le_add (hb _) (hb _)).trans_eq (by ring)))
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (tendsto_anisotropicRecordedEnergyProbability
        (followupCavitySpinModel n β ρ hβ hρ u hu) hμ a q T hq) G
  · simp only [followupCavityNativeTerminalExpectation,dif_neg hu]
    exact tendsto_const_nhds

theorem tendstoUniformlyOn_followupCavityNativeJets_of_weak
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μj : ℕ→Paper.ParisiMeasure) (μ : Paper.ParisiMeasure) (hμ : Tendsto μj atTop (𝓝 μ))
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : ∀N,a≤Paper.parisiCDF (μj N) 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (r : ℕ) :
    TendstoUniformlyOn
      (fun N=>withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ (μj N) a q T F)
        (Icc (0:ℝ) 1) r)
      (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
        (Icc (0:ℝ) 1) r) atTop (Icc (0:ℝ) 1) := by
  classical
  let C0:=∑σ,|F σ|
  have hC0:0≤C0:=Finset.sum_nonneg (fun σ _=>abs_nonneg _)
  have hF (σ):|F σ|≤C0:=Finset.single_le_sum (fun σ _=>abs_nonneg (F σ)) (Finset.mem_univ σ)
  let C : ℕ→ℝ≥0:=fun r=>⟨growth (7*β^2)
    (FiniteCascadeGenealogy.leafCount (asGenealogy T)) r*C0,
    mul_nonneg (growth_nonneg _ (by positivity) _ _) hC0⟩
  apply (tendstoUniformlyOn_actual_withinJets_on_Icc
    (fun N r=>withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ (μj N) a q T F)
      (Icc (0:ℝ) 1) r)
    (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
    (fun N r u hu=>hasDerivWithinAt_followupCavityNativeTerminalExpectation_withinJet
      hn β ρ hβ hρ (μj N) a ha (hfloor N) q hq hJ hzero htop T F r u hu) C ?_ ?_).1 r
  · intro N r _ u hu
    have hh:=abs_followupCavityNativeTerminalExpectation_withinJet_le hn β ρ hβ hρ
      (μj N) a ha (hfloor N) q hq hJ hzero htop T F C0 hC0 hF r u hu
    convert! hh using 1
  · intro u _
    exact tendsto_followupCavityNativeTerminalExpectation_of_weak β ρ hβ hρ hμ a q hq T F u

theorem tendstoUniformlyOn_followupCavityNativeJets_preserving
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hS : zeroOverlap∈S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (r : ℕ) :
    TendstoUniformlyOn
      (fun N=>withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ
        (FRSB.preservingMeasure μ S N) a q T F) (Icc (0:ℝ) 1) r)
      (withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
        (Icc (0:ℝ) 1) r) atTop (Icc (0:ℝ) 1) := by
  apply tendstoUniformlyOn_followupCavityNativeJets_of_weak hn β ρ hβ hρ
    (FRSB.preservingMeasure μ S) μ (FRSB.tendsto_preservingMeasure μ S) a ha
    (fun N=>?_) q hq hJ hzero htop T F r
  have he : Paper.parisiCDF (FRSB.preservingMeasure μ S N) 0=Paper.parisiCDF μ 0 :=
    FRSB.preservingMeasure_cdf_mass μ S N zeroOverlap hS
  rw [he]
  exact hfloor

end QuantitativeFollowup
