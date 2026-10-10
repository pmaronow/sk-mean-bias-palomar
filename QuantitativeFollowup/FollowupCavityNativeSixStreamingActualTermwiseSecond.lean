module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceTermDerivatives
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceFutureDerivative
public import QuantitativeFollowup.FollowupCavityNativeStreamingRegularity

@[expose] public section

/-! Actual termwise second streaming for every deterministic profile.
Each marked integrand is differentiated on its actual representing tree,
all fixed mark integrals are differentiated by genuine endpoint dominated
convergence, and both cross weights stay on the unchanged original tree.
The independent normalizer follows the true product rule. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingSourceSixParameterBracket
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (u : ℝ) : ℝ :=
  nativeStreamingSourceSixFunctional μ a q T
    (fun P=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F P u)

def nativeStreamingSourceSecondParameterBracket
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (u : ℝ) : ℝ :=
  if hu : u∈Icc (0:ℝ) 1 then
    nativeStreamingSourceTermwiseSecondBracket
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F else 0

theorem nativeStreamingSourceSixParameterBracket_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    nativeStreamingSourceSixParameterBracket β ρ hβ hρ μ a q T F u =
      nativeStreamingSourceSixBracket (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F := by
  simp only [nativeStreamingSourceSixParameterBracket,nativeStreamingPatternParameterMoment,dif_pos hu]
  exact (nativeStreamingSourceSixBracket_eq_pattern_functional _ μ a q T F).symm

theorem hasDerivWithinAt_nativeStreamingSourceSixBracket_termwise_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (nativeStreamingSourceSixParameterBracket β ρ hβ hρ μ a q T F)
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceTermwiseSecondBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) (Icc (0:ℝ) 1) u := by
  have h1 := hasDerivWithinAt_nativeStreamingSourceOriginal_parameter_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF u hu
  have h2 : HasDerivWithinAt
      (fun t=>-2*∑i : ObservationLeaf T,nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.originalFresh i o) t))
      (-2*∑i : ObservationLeaf T,nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
          (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.originalFresh i o))) (Icc (0:ℝ) 1) u := by
    simpa only [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
        hasDerivWithinAt_nativeStreamingSourceOriginalFresh_weight_parameter_actual
          hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF i u hu)).const_mul (-2)
  have h3 := hasDerivWithinAt_nativeStreamingSourceCross_parameter_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF u hu
  have h4 := hasDerivWithinAt_nativeStreamingSourceCurrent_parameter_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF u hu
  have h5 := hasDerivWithinAt_nativeStreamingSourceFuture_parameter_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF u hu
  have h6 := hasDerivWithinAt_nativeStreamingSourceNormalizer_parameter_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF u hu
  have h := ((((h1.add h2).add h3).add h4).add h5).add h6
  change HasDerivWithinAt (nativeStreamingSourceSixParameterBracket β ρ hβ hρ μ a q T F)
    (nativeStreamingSourceSixFunctional μ a q T
      (fun P=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
          (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F P)) (Icc (0:ℝ) 1) u at h
  rw [nativeStreamingSourceSixFunctional_const_mul] at h
  exact h

theorem followupCavityNativeTerminalExpectation_second_jet_termwise_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) 2 u =
      (followupCavityAlpha n β ρ/2)^2*nativeStreamingSourceTermwiseSecondBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F := by
  have hfirst (v : ℝ) (hv : v∈Icc (0:ℝ) 1) :
      withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
        (Icc (0:ℝ) 1) 1 v =
        (followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixParameterBracket β ρ hβ hρ μ a q T F v := by
    rw [nativeStreamingSourceSixParameterBracket_eq_actual β ρ hβ hρ μ a q T F v hv]
    simpa only [withinJet] using
      (hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
        q hq hJ hzero htop T F v hv).derivWithin
          (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) v hv)
  have hd := (hasDerivWithinAt_nativeStreamingSourceSixBracket_termwise_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF u hu).const_mul
    (followupCavityAlpha n β ρ/2)
  have hd2 := hd.congr_of_mem hfirst hu
  have he := hd2.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) u hu)
  calc
    withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) 2 u =
      (followupCavityAlpha n β ρ/2)*((followupCavityAlpha n β ρ/2)*
        nativeStreamingSourceTermwiseSecondBracket
          (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) := by
            simpa only [withinJet] using he
    _ = _ := by ring

theorem nativeStreamingSource_c2_termwise_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    ContDiffOn ℝ 2 (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) ∧
    (∀u (hu : u∈Icc (0:ℝ) 1),HasDerivWithinAt
      (nativeStreamingSourceSixParameterBracket β ρ hβ hρ μ a q T F)
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceTermwiseSecondBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) (Icc (0:ℝ) 1) u) ∧
    (∀u (hu : u∈Icc (0:ℝ) 1),withinJet
      (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F) (Icc (0:ℝ) 1) 2 u =
      (followupCavityAlpha n β ρ/2)^2*nativeStreamingSourceTermwiseSecondBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) := by
  classical
  let C := ∑σ : TerminalSpins (Configuration (n+1)) T,|F σ|
  have hC : 0≤C := Finset.sum_nonneg fun σ _=>abs_nonneg _
  have hF : ∀σ,|F σ|≤C := fun σ=>
    Finset.single_le_sum (fun σ _=>abs_nonneg (F σ)) (Finset.mem_univ σ)
  refine ⟨(contDiffOn_followupCavityNativeTerminalExpectation hn β ρ hβ hρ μ a ha
    (scalarFloor_cdf_lower hfloor (by norm_num)) q hq hJ hzero htop T F).of_le (by simp),?_,?_⟩
  · intro u hu
    exact hasDerivWithinAt_nativeStreamingSourceSixBracket_termwise_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF u hu
  · intro u hu
    exact followupCavityNativeTerminalExpectation_second_jet_termwise_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF u hu

end QuantitativeFollowup
