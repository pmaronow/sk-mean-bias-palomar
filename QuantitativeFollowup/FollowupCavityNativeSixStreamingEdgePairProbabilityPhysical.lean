module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairProbabilityLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairKernelPhysicalOrder

@[expose] public section

/-! An actual antitone clock determines the chronological two-mark law,
including coincident physical times and all retained original records. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem nativeStreamingEdgePairProbability_refinement_physical (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hq : Antitone q) (hzero : q 0=1) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (p k : ℕ) (hp : p<d e.depth) (hk : k<d f.depth)
    (r l : Paper.Overlap) (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hl : q (f.depth+1)≤l ∧ l≤q f.depth)
    (hpr : Q (observationRefinementDepth d e.depth+p+1)=r)
    (hkl : Q (observationRefinementDepth d f.depth+k+1)=l)
 :
    (nativeStreamingCrossVertexProbability D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      nativeStreamingEdgePairProbabilityFixed D μ a q T e f
        (nativeStreamingPairObservationIndex e.depth f.depth r l)
        (nativeStreamingPairObservationIndex f.depth e.depth l r) r l := by
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  apply ProbabilityMeasure.toMeasure_injective
  change (nativeStreamingCrossVertexProbability D μ a Q (observationRefineTree d T)
    (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k) :
      Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
        (Configuration n) (observationRefineTree d T)) ×
          (Configuration n × Configuration n))).map _=
      (nativeStreamingEdgePairProbabilityFixed D μ a q T e f
        (nativeStreamingPairObservationIndex e.depth f.depth r l)
        (nativeStreamingPairObservationIndex f.depth e.depth l r) r l :
          Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
            (Configuration n) T) × (Configuration n × Configuration n)))
  rw [nativeStreamingCrossVertexProbability_eq_law D μ a Q hQ hQ0,
    nativeStreamingEdgePairMarked_projection D μ a q Q d hQ hlevels T e f p k hp hk,
    nativeStreamingEdgePairProbabilityFixed_eq_kernel D μ a q hq hzero T e f
      (nativeStreamingPairObservationIndex e.depth f.depth r l)
      (nativeStreamingPairObservationIndex f.depth e.depth l r)
      (nativeStreamingPairObservationIndex_lt _ _ _ _)
      (nativeStreamingPairObservationIndex_lt _ _ _ _) r l hr hl,
    hpr,hkl,nativeStreamingPairObservationIndex_level,
    nativeStreamingPairObservationIndex_second_level]
  rw [nativeStreamingEdgePairObservedKernel_physical_order D μ q Q d hQ T e f p k r l hpr hkl]

end QuantitativeFollowup
