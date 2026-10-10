module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedOriginalNormalizerTerms
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedPatternWeights
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedCrossWeights
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedFutureWeights
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexSixAgreement

@[expose] public section

/-! The whole actual finite six-term expression under observation refinement.
Every regrouping equality comes from the genuine marked laws, including the
future term's same-cell pair and both charges on the original tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingRefinedSixBracket_agreement
    (D : AnisotropicSpinModel (n+1)) (t : RSBScheme k)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme t)∈scalarFloor a)
    (ht : t.q 1=0) (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i,anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J≤k+1)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    let s := cdfMassScheme t
    let μ := Paper.parisiSchemeMeasure s
    let Q := anisotropicRecordedSchemeSchedule s
    nativeStreamingVertexSixBracket D μ a Q (anisotropicSchemeMass s)
      (observationRefineTree d T) (nativeStreamingRefinedTerminalTest d T F)=
      nativeStreamingSourceSixBracket D μ a q T F := by
  classical
  dsimp only
  have hQ := anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme t)
  have hq : (fun i=>anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i))=q := funext hlevels
  have ho := nativeStreamingSourceOriginalTerm_refinement D
    (Paper.parisiSchemeMeasure (cdfMassScheme t)) a q _ d hQ hlevels T F
  have hf := nativeStreamingRefinedOriginalFreshTerm_agreement D t a ha hfloor q d
    hlevels T hdepth F
  have hx := nativeStreamingRefinedCrossWeight_agreement D t a ha hfloor d T hdepth F
  dsimp only at hx
  rw [hq] at hx
  have hc := nativeStreamingRefinedCurrentWeight_agreement D t a ha hfloor q d
    hlevels T hdepth F
  have hu := nativeStreamingRefinedFutureWeight_agreement D t a ha hfloor ht q d
    hlevels T hdepth F
  have hz := nativeStreamingSourceNormalizerTerm_refinement D
    (Paper.parisiSchemeMeasure (cdfMassScheme t)) a q _ d hQ hlevels T F
  unfold nativeStreamingVertexSixBracket nativeStreamingSourceSixBracket
  rw [ho,hx,hc,hu,hz]
  rw [show (nativeStreamingSourceOriginalTerm D (Paper.parisiSchemeMeasure (cdfMassScheme t))
      a q T F - 2*(∑i : ObservationLeaf (observationRefineTree d T),
        nativeStreamingVertexChargeSum (anisotropicSchemeMass (cdfMassScheme t)) a
          (observationRefineTree d T) (fun v=>nativeStreamingPatternMoment D
            (Paper.parisiSchemeMeasure (cdfMassScheme t)) a
            (anisotropicRecordedSchemeSchedule (cdfMassScheme t)) (observationRefineTree d T)
            (nativeStreamingRefinedTerminalTest d T F) (.originalFresh i (.vertex v)))))=
      nativeStreamingSourceOriginalTerm D (Paper.parisiSchemeMeasure (cdfMassScheme t))
        a q T F+(-2:ℝ)*(∑i : ObservationLeaf (observationRefineTree d T),
        nativeStreamingVertexChargeSum (anisotropicSchemeMass (cdfMassScheme t)) a
          (observationRefineTree d T) (fun v=>nativeStreamingPatternMoment D
            (Paper.parisiSchemeMeasure (cdfMassScheme t)) a
            (anisotropicRecordedSchemeSchedule (cdfMassScheme t)) (observationRefineTree d T)
            (nativeStreamingRefinedTerminalTest d T F) (.originalFresh i (.vertex v)))) by ring]
  rw [hf]

end QuantitativeFollowup
