module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTrimmedTerminalExpectation
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceDerivativePassage

@[expose] public section

/-! The actual finite model derivative after the proved six-term
regrouping. The retained observation tree has the complete scheme prefix;
the extra initial advance is the genuine zero-time physical edge. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingRefinedFinite_source_derivative
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (t : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme t)∈scalarFloor a)
    (ht : t.q 1=0) (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i,anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J=k+1)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let μ := Paper.parisiSchemeMeasure (cdfMassScheme t)
    withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) 1 u =
      (followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F := by
  let s := cdfMassScheme t
  let μ := Paper.parisiSchemeMeasure s
  let Q := anisotropicRecordedSchemeSchedule s
  let R := observationRefineTree d T
  let U := observationTreeDepthCast hdepth R
  let Ffine := nativeStreamingRefinedTerminalTest d T F
  let G := fun σ : TerminalSpins (Configuration (n+1)) U=>
    Ffine (finiteCascadeRecordTerminalSpins R
      (observationRecordDepthCast hdepth R (observationUnitRecord U σ)))
  let Ft := cavityTerminalSampleObservable U.advance G
  have hs : s.q 1=0 := ht
  have has : a ≤ s.m 1 := by
    apply cdfMassScheme_preserves_floor t ht a
    have H := scalarFloor_cdf_lower hfloor (show (0:ℝ)≤0 from le_rfl)
    simpa only [parisiSchemeMeasure_cdfMassScheme] using H
  have hQ := anisotropicRecordedSchemeSchedule_antitone s
  have hphysical (v : ℝ) (hv : v∈Icc (0:ℝ) 1) :
      followupCavityPhysicalExpectation n β ρ hβ hρ s a U.advance Ft v=
      followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F v := by
    rw [followupCavityPhysicalExpectation_advance_terminal β ρ hβ hρ s a hs U G v hv]
    rw [nativeStreamingOldTerminalExpectation_depthCast _ μ a Q hdepth R Ffine,
      nativeStreamingOldTerminalExpectation_refinement _ μ a q Q d hQ hlevels T F]
    exact (followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a q T F v hv).symm
  have hd := hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed
    hn β ρ hβ hρ s a ha has hs U.advance Ft u hu
  have hobs : followupCavityPhysicalRecordObservable n U.advance Ft=
      (fun z=>G (finiteCascadeRecordTerminalSpins U z.2)) :=
    funext (nativeStreamingPhysicalRecordObservable_advance_terminal U G)
  rw [hobs,cavityMarkedSixExpectation_eq_native_vertex_six_bracket hn _ s a ha.1 has hs U G,
    nativeStreamingVertexSixBracket_depthCast _ μ a Q (anisotropicSchemeMass s) hdepth R Ffine,
    nativeStreamingRefinedSixBracket_agreement _ t a ha hfloor ht q d hlevels T hdepth.le F] at hd
  have hdNative := hd.congr_of_mem (fun v hv=>(hphysical v hv).symm) hu
  change derivWithin (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
    (Icc (0:ℝ) 1) u=_
  exact hdNative.derivWithin ((uniqueDiffOn_Icc zero_lt_one) u hu)

end QuantitativeFollowup
