module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedMarkLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossMarkedLaw

@[expose] public section

/-! Preserve two genuine ancestral fields jointly with the entire
original record before drawing the two independent conditional terminal
marks. Equal field indices share their ancestor, while their terminal
marks retain the true conditional product law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {E S : Type} {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeStreamingEdgePairSelection (d : ℕ → ℕ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e f : NativeStreamingEdge T) (p k : ℕ) :
    Records E S (observationRefineTree d T) → E × (E × Records E S T) :=
  fun z=>((nativeStreamingEdgeSelection d e p z).1,
    ((nativeStreamingEdgeSelection d f k z).1,observationRefinementProject d T z))

theorem measurable_nativeStreamingEdgePairSelection [MeasurableSpace E] [MeasurableSpace S]
    (d : ℕ → ℕ) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (e f : NativeStreamingEdge T) (p k : ℕ) :
    Measurable (nativeStreamingEdgePairSelection (E:=E) (S:=S) d e f p k) :=
  (measurable_nativeStreamingEdgeSelection d e p).fst.prodMk
    ((measurable_nativeStreamingEdgeSelection d f k).fst.prodMk
      (measurable_observationRefinementProject d T))

theorem continuous_nativeStreamingEdgePairSelection [TopologicalSpace E] [TopologicalSpace S]
    (d : ℕ → ℕ) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (e f : NativeStreamingEdge T) (p k : ℕ) :
    Continuous (nativeStreamingEdgePairSelection (E:=E) (S:=S) d e f p k) :=
  (continuous_nativeStreamingEdgeSelection d e p).fst.prodMk
    ((continuous_nativeStreamingEdgeSelection d f k).fst.prodMk
      (continuous_observationRefinementProject d T))

def nativeStreamingEdgePairObservedSpinKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) {j : ℕ} (T : FiniteTerminalGenealogy j) (r l : Paper.Overlap) :
    Kernel (AnisotropicObservationState n × (AnisotropicObservationState n ×
      (AnisotropicObservationState n × Records (AnisotropicObservationState n) (Configuration n) T)))
      (Configuration n × Configuration n) :=
  (anisotropicObservationTerminalSpinKernel D μ r).comap (fun z=>z.2.1) measurable_snd.fst ×ₖ
    (anisotropicObservationTerminalSpinKernel D μ l).comap (fun z=>z.2.2.1) measurable_snd.snd.fst

instance nativeStreamingEdgePairObservedSpinKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) {j : ℕ} (T : FiniteTerminalGenealogy j) (r l : Paper.Overlap) :
    IsMarkovKernel (nativeStreamingEdgePairObservedSpinKernel D μ T r l) := by
  unfold nativeStreamingEdgePairObservedSpinKernel
  infer_instance

theorem nativeStreamingEdgePairSelectedMarkKernel_collapse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e f : NativeStreamingEdge T)
    (p k : ℕ) (hp : p<d e.depth) (hk : k<d f.depth) :
    nativeStreamingCrossVertexKernel D μ Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)=
      (nativeStreamingEdgePairObservedSpinKernel D μ T
        (Q (observationRefinementDepth d e.depth+p+1))
        (Q (observationRefinementDepth d f.depth+k+1))).comap
          (Prod.map id (nativeStreamingEdgePairSelection d e f p k))
          (measurable_id.prodMap (measurable_nativeStreamingEdgePairSelection d e f p k)) := by
  ext z : 1
  simp only [nativeStreamingCrossVertexKernel,nativeStreamingSingleVertexKernel,
    nativeStreamingEdgePairObservedSpinKernel,Kernel.prod_apply,Kernel.comap_apply]
  dsimp only [Function.uncurry]
  rw [nativeStreamingEdgeSelectedVertex_depth d e p hp,
    nativeStreamingEdgeSelectedVertex_depth d f k hk,
    nativeStreamingEdgeSelectedVertex_state,nativeStreamingEdgeSelectedVertex_state]
  rfl

theorem nativeStreamingEdgePairSelectedMarkedLaw_collapse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e f : NativeStreamingEdge T)
    (p k : ℕ) (hp : p<d e.depth) (hk : k<d f.depth) :
    (nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)).map
        (fun z=>((z.1.1,nativeStreamingEdgePairSelection d e f p k z.1.2),z.2))=
      ((anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T)).map
        (Prod.map id (nativeStreamingEdgePairSelection d e f p k))) ⊗ₘ
          nativeStreamingEdgePairObservedSpinKernel D μ T
            (Q (observationRefinementDepth d e.depth+p+1))
            (Q (observationRefinementDepth d f.depth+k+1)) := by
  unfold nativeStreamingCrossVertexLaw
  rw [nativeStreamingEdgePairSelectedMarkKernel_collapse D μ Q d e f p k hp hk]
  exact compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (nativeStreamingEdgePairSelection d e f p k))
    (measurable_id.prodMap (measurable_nativeStreamingEdgePairSelection d e f p k))
    (nativeStreamingEdgePairObservedSpinKernel D μ T
      (Q (observationRefinementDepth d e.depth+p+1))
      (Q (observationRefinementDepth d f.depth+k+1)))

end QuantitativeFollowup
