module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairObservedLaw

@[expose] public section

/-! Identify the complete old record and two conditional terminal marks
under an arbitrary fine refinement. The projection is obtained from the
proved joint ancestral law, not from matching spin marginals. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem nativeStreamingEdgePairMarked_projection (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (e f : NativeStreamingEdge T)
    (p k : ℕ) (hp : p<d e.depth) (hk : k<d f.depth) :
    (nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      ((anisotropicObservationInitialLaw D μ a ⊗ₘ
        nativeStreamingEdgePairObservedKernel D μ q (nativeStreamingEdgeIndexOrder p k) T e f
          (Q (observationRefinementDepth d e.depth+p+1))
          (Q (observationRefinementDepth d f.depth+k+1))) ⊗ₘ
            nativeStreamingEdgePairObservedSpinKernel D μ T
              (Q (observationRefinementDepth d e.depth+p+1))
              (Q (observationRefinementDepth d f.depth+k+1))).map
                (fun z=>((z.1.1,z.1.2.2.2),z.2)) := by
  let F := fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n) =>
      ((z.1.1,nativeStreamingEdgePairSelection d e f p k z.1.2),z.2)
  let G := fun z : (AnisotropicObservationState n ×
      (AnisotropicObservationState n × (AnisotropicObservationState n ×
        Records (AnisotropicObservationState n) (Configuration n) T))) ×
          (Configuration n × Configuration n) => ((z.1.1,z.1.2.2.2),z.2)
  have hF : Measurable F :=
    (measurable_fst.fst.prodMk ((measurable_nativeStreamingEdgePairSelection d e f p k).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hG : Measurable G :=
    (measurable_fst.fst.prodMk measurable_fst.snd.snd.snd).prodMk measurable_snd
  change Measure.map (G ∘ F) _=_
  rw [←Measure.map_map hG hF,
    nativeStreamingEdgePairSelectedMarkedLaw_collapse D μ a Q d e f p k hp hk,
    nativeStreamingEdgePairSelection_joint_law D μ a q Q d hQ hlevels T e f p k hp hk]

end QuantitativeFollowup
