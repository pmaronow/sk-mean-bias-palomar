module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedFuturePatternIntegrals
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedDiscreteChargeGrouping
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFutureWeightCoherence

@[expose] public section

/-! The genuine future callback on every retained subdivision vertex
regroups to the original Stieltjes origin weight. Repeated clocks, same-cell
future pairs, and the final root correction remain in the identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingRefinedFutureWeight_agreement
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
    nativeStreamingVertexChargeSum (anisotropicSchemeMass s) a (observationRefineTree d T)
      (fun v=>nativeStreamingPatternFutureIntegral D μ a Q (observationRefineTree d T)
        (nativeStreamingRefinedTerminalTest d T F) (.vertex v)) =
      nativeStreamingSourceFutureTerm D μ a q T F := by
  dsimp only
  unfold nativeStreamingSourceFutureTerm
  have hQ := anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme t)
  have hq : Antitone q := by
    intro i j hij
    rw [←hlevels i,←hlevels j]
    exact hQ ((observationRefinementDepth_strictMono d).monotone hij)
  have hQ0 := nativeStreamingSchemeSchedule_zero (cdfMassScheme t)
  have hzero : q 0=1 := by rw [←hlevels 0]; exact hQ0
  have hs : (cdfMassScheme t).q 1=0 := ht
  have has : a≤(cdfMassScheme t).m 1 := by
    apply cdfMassScheme_preserves_floor t ht a
    have H := scalarFloor_cdf_lower hfloor (show (0:ℝ)≤0 from le_rfl)
    simpa only [parisiSchemeMeasure_cdfMassScheme] using H
  refine nativeStreamingNormalizedRefinedChargeSum_eq_originWeightIntegral t a ha hfloor q d
    hlevels T hdepth a _ _ ?_ ?_ ?_ ?_
  · exact nativeStreamingPatternFutureIntegral_vertex_root_coherent D _ a _ hQ hQ0 _ _
  · intro v
    exact nativeStreamingPatternFutureIntegral_finite_vertex_refinement D (cdfMassScheme t)
      a ha.1 has hs q _ d hQ hlevels hzero T F v
  · intro e p hp
    exact nativeStreamingPatternFutureIntegral_finite_selected_refinement D (cdfMassScheme t)
      a ha.1 has hs q _ d hQ hlevels hzero T F e p hp
  · intro e
    exact nativeStreamingPatternFutureIntegral_edge_child_endpoint D _ a q hq hzero T F e

end QuantitativeFollowup
