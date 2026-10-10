module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedVertex
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedRefinement

@[expose] public section

/-! A genuine terminal mark at any interior fine vertex can be projected
jointly with its actual ancestral state and all original records.  The
result is the native terminal kernel at that retained state. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingEdgeObservedSpinKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) {j : ℕ} (T : FiniteTerminalGenealogy j) (r : Paper.Overlap) :
    Kernel (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T)) (Configuration n) :=
  (anisotropicObservationTerminalSpinKernel D μ r).comap (fun z=>z.2.1) measurable_snd.fst

instance nativeStreamingEdgeObservedSpinKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) {j : ℕ} (T : FiniteTerminalGenealogy j) (r : Paper.Overlap) :
    IsMarkovKernel (nativeStreamingEdgeObservedSpinKernel D μ T r) := by
  unfold nativeStreamingEdgeObservedSpinKernel
  infer_instance

theorem nativeStreamingEdgeSelectedMarkKernel_collapse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) :
    nativeStreamingSingleVertexKernel D μ Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p)=
      (nativeStreamingEdgeObservedSpinKernel D μ T
        (Q (observationRefinementDepth d e.depth+p+1))).comap
          (Prod.map id (nativeStreamingEdgeSelection d e p))
          (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p)) := by
  ext z σ hs
  change (anisotropicObservationTerminalSpinKernel D μ
      (Q (nativeStreamingEdgeSelectedVertex d e p).depth)
      (nativeStreamingVertexState (nativeStreamingEdgeSelectedVertex d e p) z.1 z.2)) σ=
    (anisotropicObservationTerminalSpinKernel D μ (Q (observationRefinementDepth d e.depth+p+1))
      (nativeStreamingEdgeSelection d e p z.2).1) σ
  rw [nativeStreamingEdgeSelectedVertex_depth d e p hp,nativeStreamingEdgeSelectedVertex_state]

theorem nativeStreamingEdgeSelectedMarkedLaw_collapse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) :
    (nativeStreamingSingleVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p)).map
        (fun z=>((z.1.1,nativeStreamingEdgeSelection d e p z.1.2),z.2))=
      (anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e
        (Q (observationRefinementDepth d e.depth+p+1))) ⊗ₘ
          nativeStreamingEdgeObservedSpinKernel D μ T
            (Q (observationRefinementDepth d e.depth+p+1)) := by
  unfold nativeStreamingSingleVertexLaw
  rw [nativeStreamingEdgeSelectedMarkKernel_collapse D μ Q d e p hp]
  have he:=compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (nativeStreamingEdgeSelection d e p))
    (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p))
    (nativeStreamingEdgeObservedSpinKernel D μ T (Q (observationRefinementDepth d e.depth+p+1)))
  rw [nativeStreamingEdgeSelection_joint_law D μ a q Q d hQ hlevels e p hp] at he
  exact he

end QuantitativeFollowup
