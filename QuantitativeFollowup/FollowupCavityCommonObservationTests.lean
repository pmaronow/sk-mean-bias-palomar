module
public import QuantitativeFollowup.FollowupCavityCommonObservationRealization

@[expose] public section

/-! Fixed terminal tests on one exact observation refinement retain their
native expectation and their actual selected old-pair domination. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityObservationRefinedTerminalTest (n : ℕ) (d : ℕ→ℕ)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J=k+2)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    FiniteCascadeGenealogy.Samples (Configuration (n+1))
      (asGenealogy (observationTreeDepthCast hdepth (observationRefineTree d T)))→ℝ :=
  cavityTerminalSampleObservable _ (fun σ=>F (observationRefinementTerminalProject d T hdepth σ))

theorem cavityObservationRefinedTerminalTest_expectation
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hszero : s.q 1=0)
    (q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hl : ∀j,anisotropicRecordedSchemeSchedule s (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J=k+2)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1):
    followupCavityPhysicalExpectation n β ρ hβ hρ s a
      (observationTreeDepthCast hdepth (observationRefineTree d T))
      (cavityObservationRefinedTerminalTest n d T hdepth F) u=
    followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiSchemeMeasure s) a q T F u := by
  let U:=observationTreeDepthCast hdepth (observationRefineTree d T)
  let G:=fun σ : TerminalSpins (Configuration (n+1)) U=>F (observationRefinementTerminalProject d T hdepth σ)
  rw [followupCavityNativeTerminalExpectation_eq β ρ hβ hρ _ a q T F u hu]
  have hmap:=anisotropicRecordedProfileTreeLaw_refined_scheme
    (followupCavitySpinModel n β ρ hβ hρ u hu) s a q d hl T hdepth
  change (anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a U).map
    (Prod.map id (observationRefinementDepthProject (S:=Configuration (n+1)) d T hdepth))=
    (anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
      (Paper.parisiSchemeMeasure s) a q T:Measure (CavityPathRecordSpace T (n+1))) at hmap
  change followupCavityPhysicalExpectation n β ρ hβ hρ s a U (cavityTerminalSampleObservable U G) u=_
  rw [followupCavityPhysicalExpectation_terminal_integral β ρ hβ hρ s a hszero U G u hu,←hmap]
  have hFm:Measurable (fun z:CavityPathRecordSpace T (n+1)=>F (finiteCascadeRecordTerminalSpins T z.2)):=
    (measurable_of_finite F).comp ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)
  rw [integral_map
    (measurable_id.prodMap (measurable_observationRefinementDepthProject d T hdepth)).aemeasurable
    hFm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun z=>congrArg F (observationRefinementTerminalProject_record d T hdepth z.2)

theorem cavityObservationRefinedPhysicalTest_abs_le
    (d : ℕ→ℕ) (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J=k+2)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (C : ℝ) (hF : ∀σ,|F σ|≤C)
    (r : CavityPathRecordSpace (trimRoot (observationTreeDepthCast hdepth (observationRefineTree d T))) (n+1)):
    |followupCavityPhysicalRecordObservable n
      (observationTreeDepthCast hdepth (observationRefineTree d T))
      (cavityObservationRefinedTerminalTest n d T hdepth F) r|≤C := by
  change |F _|≤C
  exact hF _

theorem cavityObservationRefinedPhysicalTest_onePair_domination
    (s : RSBScheme k) (hszero : s.q 1=0) (q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hl : ∀j,anisotropicRecordedSchemeSchedule s (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J=k+2)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (i l : ObservationLeaf T)
    (hdom : ∀σ,|F σ|≤|cavitySpinOverlapDefect n (q (observationCommonLevel T i l))
      (observationLeafTerminalSpin T i σ) (observationLeafTerminalSpin T l σ)|)
    (r : CavityPathRecordSpace (trimRoot (observationTreeDepthCast hdepth (observationRefineTree d T))) (n+1)):
    |followupCavityPhysicalRecordObservable n
      (observationTreeDepthCast hdepth (observationRefineTree d T))
      (cavityObservationRefinedTerminalTest n d T hdepth F) r|≤
    |cavityRecordedLeafPairDefect s _ (cavityObservationRefinedLeaf d T hdepth i)
      (cavityObservationRefinedLeaf d T hdepth l) r.2| := by
  let U:=observationTreeDepthCast hdepth (observationRefineTree d T)
  let σ : TerminalSpins (Configuration (n+1)) (trimRoot U):=
    finiteCascadeRecordTerminalSpins (trimRoot U) r.2
  let e:=terminalSampleEquiv (S:=Configuration (n+1)) U
  let η:TerminalSpins (Configuration (n+1)) U:=
    (@MeasurableEquiv.symm (TerminalSpins (Configuration (n+1)) U)
      (FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy U))
      (terminalSpinMeasurableSpace (Configuration (n+1)) U)
      (FiniteCascadeGenealogy.sampleMeasurableSpace (Configuration (n+1)) (asGenealogy U)) e)
      (trimmedSpinEquiv (S:=Configuration (n+1)) U (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot U) σ))
  have hh:=hdom (observationRefinementTerminalProject d T hdepth η)
  have hi:=cavityObservationRefinedLeaf_terminalSpin (S:=Configuration (n+1)) d T hdepth i σ
  have hl':=cavityObservationRefinedLeaf_terminalSpin (S:=Configuration (n+1)) d T hdepth l σ
  dsimp only [η,e] at hh
  rw [hi,hl',observationLeafTerminalSpin_record,observationLeafTerminalSpin_record] at hh
  rw [←cavityObservationRefinedLeaf_profileLevel s hszero d T hdepth q hl i l] at hh
  change |F (observationRefinementTerminalProject d T hdepth η)|≤_ at hh
  convert! hh using 1 <;>
    simp only [cavityObservationRefinedTerminalTest,followupCavityPhysicalRecordObservable,
      cavityTerminalSampleObservable,η,e,σ,terminalSampleEquiv_recordSpins] <;> rfl

end QuantitativeFollowup
