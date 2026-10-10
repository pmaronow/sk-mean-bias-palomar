module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedFiniteDerivative
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFiniteObservationEmbedding
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFinite

@[expose] public section

/-! The genuine original-tree six-term streaming formula for every actual
profile. The finite identity is derived from the physical marked derivative
and exact retained observations, then passed through preserving profiles. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingFiniteProfile_source_derivative
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (hμ : (μ:Measure Paper.Overlap).support.Finite)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) 1 u =
      (followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F := by
  let r := FRSB.finiteLawRSBScheme μ hμ
  have hr : r.q 1=0 := nativeStreaming_finiteScheme_first_zero μ hμ
  have hm : Paper.parisiSchemeMeasure r=μ := FRSB.parisiSchemeMeasure_finiteLawRSBScheme μ hμ
  obtain ⟨K,t,e,htm,ht,he,hezero,hetop,helevels⟩ :=
    exists_same_measure_trimmed_observation_scheme_embedding r hr q hq J hJ hzero htop
  have htm' : Paper.parisiSchemeMeasure (cdfMassScheme t)=μ :=
    (parisiSchemeMeasure_cdfMassScheme t).trans (htm.trans hm)
  have hf : Paper.parisiSchemeMeasure (cdfMassScheme t)∈scalarFloor a := by
    rw [htm']
    exact hfloor
  let d := observationEmbeddingGaps e
  have hdepth : observationRefinementDepth d J=K+1 :=
    (observationRefinementDepth_embedding e he hezero J).trans hetop
  have hlevels (i : ℕ) : anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i := by
    rw [observationRefinementDepth_embedding e he hezero]
    exact helevels i
  have H := nativeStreamingRefinedFinite_source_derivative hn β ρ hβ hρ t a ha hf ht
    q d hlevels T hdepth F u hu
  dsimp only at H
  rw [htm'] at H
  exact H

theorem nativeStreamingSource_derivative_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) 1 u =
      (followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F :=
  nativeStreamingSource_derivative_of_finite_profiles hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F u hu
    (fun ν hν hf=>nativeStreamingFiniteProfile_source_derivative hn β ρ hβ hρ ν hν
      a ha hf q hq hJ hzero htop T F u hu)

theorem hasDerivWithinAt_nativeStreamingSource_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) (Icc (0:ℝ) 1) u := by
  have hroot : a ≤ Paper.parisiCDF μ 0 := by
    rw [←zeroMass_eq_parisiCDF_zero]
    exact (mem_scalarFloor_iff a μ).mp hfloor
  have H := hasDerivWithinAt_followupCavityNativeTerminalExpectation_withinJet
    hn β ρ hβ hρ μ a ha hroot q hq hJ hzero htop T F 0 u hu
  rw [nativeStreamingSource_derivative_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ
    hzero htop T F u hu] at H
  exact H

end QuantitativeFollowup
