module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairProbability
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairMarkedProjection
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairKernelOrder

@[expose] public section

/-! The fixed observation genealogy and an arbitrary exact refinement
have the same complete old-record/two-terminal-mark law.  The order of
successive observations is kept explicitly on a shared edge. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem nativeStreamingEdgePairProbabilityFixed_eq_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (hq : Antitone q) (hzero : q 0=1) (T : FiniteTerminalGenealogy J)
    (e f : NativeStreamingEdge T) (p k : ℕ) (hp : p<2) (hk : k<2)
    (r l : Paper.Overlap)
    (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hl : q (f.depth+1)≤l ∧ l≤q f.depth) :
    (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k r l : Measure _)=
      ((anisotropicObservationInitialLaw D μ a ⊗ₘ
        nativeStreamingEdgePairObservedKernel D μ q (nativeStreamingEdgeIndexOrder p k) T e f
          (nativeStreamingPairObservationSchedule q e.depth f.depth r l
            (observationRefinementDepth nativeStreamingPairObservationSubdivision e.depth+p+1))
          (nativeStreamingPairObservationSchedule q e.depth f.depth r l
            (observationRefinementDepth nativeStreamingPairObservationSubdivision f.depth+k+1))) ⊗ₘ
        nativeStreamingEdgePairObservedSpinKernel D μ T
          (nativeStreamingPairObservationSchedule q e.depth f.depth r l
            (observationRefinementDepth nativeStreamingPairObservationSubdivision e.depth+p+1))
          (nativeStreamingPairObservationSchedule q e.depth f.depth r l
            (observationRefinementDepth nativeStreamingPairObservationSubdivision f.depth+k+1))).map
              (fun z=>((z.1.1,z.1.2.2.2),z.2)) := by
  let Q := nativeStreamingPairObservationSchedule q e.depth f.depth r l
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq
    e.depth f.depth r l hr hl
  have hQ0 : Q 0=1 := by
    simpa only [Q,nativeStreamingPairObservationSchedule,Nat.zero_mod,Nat.zero_div,
      ite_true] using hzero
  change (nativeStreamingCrossVertexProbability D μ a Q
    (observationRefineTree nativeStreamingPairObservationSubdivision T)
    (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e p)
    (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f k) :
      Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
        (Configuration n) (observationRefineTree nativeStreamingPairObservationSubdivision T)) ×
          (Configuration n × Configuration n))).map _=_
  rw [nativeStreamingCrossVertexProbability_eq_law D μ a Q hQ hQ0]
  exact nativeStreamingEdgePairMarked_projection D μ a q Q
    nativeStreamingPairObservationSubdivision hQ
    (nativeStreamingPairObservationSchedule_refinement q e.depth f.depth r l)
    T e f p k hp hk

 theorem nativeStreamingEdgePairProbability_refinement_eq_fixed (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hq : Antitone q) (hzero : q 0=1) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (p k : ℕ) (hp : p<d e.depth) (hk : k<d f.depth)
    (r l : Paper.Overlap) (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hl : q (f.depth+1)≤l ∧ l≤q f.depth)
    (hpr : Q (observationRefinementDepth d e.depth+p+1)=r)
    (hkl : Q (observationRefinementDepth d f.depth+k+1)=l)
    (horder : nativeStreamingEdgeIndexOrder p k=
      nativeStreamingEdgeIndexOrder (nativeStreamingPairObservationIndex e.depth f.depth r l)
        (nativeStreamingPairObservationIndex f.depth e.depth l r) ∨ e≠f) :
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
  rcases horder with horder|hne
  · rw [horder]
  · rw [nativeStreamingEdgePairObservedKernel_order_independent D μ q _ _ T e f hne r l]

end QuantitativeFollowup
