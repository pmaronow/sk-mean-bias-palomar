module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedMarkLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFuturePairLaw

@[expose] public section

/-! Retain the genuine ancestral field inside an old edge before running
one shared future transition and drawing two independent terminal marks.
The full old record is kept throughout this law identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingEdgeObservedFutureKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (r l : Paper.Overlap) :
    Kernel (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T))
        (Configuration n × Configuration n) :=
  ((anisotropicObservationTerminalSpinKernel D μ l ×ₖ
    anisotropicObservationTerminalSpinKernel D μ l) ∘ₖ
      anisotropicObservationTransition D μ r l).comap (fun z=>z.2.1) measurable_snd.fst

instance nativeStreamingEdgeObservedFutureKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (r l : Paper.Overlap) :
    IsMarkovKernel (nativeStreamingEdgeObservedFutureKernel D μ T r l) := by
  unfold nativeStreamingEdgeObservedFutureKernel
  infer_instance

theorem nativeStreamingEdgeSelectedFutureKernel_collapse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) (l : Paper.Overlap) :
    nativeStreamingFuturePairKernel D μ Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) l=
      (nativeStreamingEdgeObservedFutureKernel D μ T
        (Q (observationRefinementDepth d e.depth+p+1)) l).comap
          (Prod.map id (nativeStreamingEdgeSelection d e p))
          (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p)) := by
  ext z σ hs
  change (((anisotropicObservationTerminalSpinKernel D μ l ×ₖ
    anisotropicObservationTerminalSpinKernel D μ l) ∘ₖ
      anisotropicObservationTransition D μ (Q (nativeStreamingEdgeSelectedVertex d e p).depth) l)
        (nativeStreamingVertexState (nativeStreamingEdgeSelectedVertex d e p) z.1 z.2)) σ=
    (((anisotropicObservationTerminalSpinKernel D μ l ×ₖ
      anisotropicObservationTerminalSpinKernel D μ l) ∘ₖ
        anisotropicObservationTransition D μ
          (Q (observationRefinementDepth d e.depth+p+1)) l)
            (nativeStreamingEdgeSelection d e p z.2).1) σ
  rw [nativeStreamingEdgeSelectedVertex_depth d e p hp,nativeStreamingEdgeSelectedVertex_state]

theorem nativeStreamingEdgeSelectedFutureLaw_collapse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) (l : Paper.Overlap) :
    (nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) l).map
        (fun z=>((z.1.1,nativeStreamingEdgeSelection d e p z.1.2),z.2))=
      (anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e
        (Q (observationRefinementDepth d e.depth+p+1))) ⊗ₘ
          nativeStreamingEdgeObservedFutureKernel D μ T
            (Q (observationRefinementDepth d e.depth+p+1)) l := by
  unfold nativeStreamingFuturePairLaw
  rw [nativeStreamingEdgeSelectedFutureKernel_collapse D μ Q d e p hp l]
  have he:=compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (nativeStreamingEdgeSelection d e p))
    (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p))
    (nativeStreamingEdgeObservedFutureKernel D μ T
      (Q (observationRefinementDepth d e.depth+p+1)) l)
  rw [nativeStreamingEdgeSelection_joint_law D μ a q Q d hQ hlevels e p hp] at he
  exact he

theorem nativeStreamingEdgeSelectedFutureLaw_projection (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) (l : Paper.Overlap) :
    (nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) l).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      ((anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e
        (Q (observationRefinementDepth d e.depth+p+1))) ⊗ₘ
          nativeStreamingEdgeObservedFutureKernel D μ T
            (Q (observationRefinementDepth d e.depth+p+1)) l).map
              (fun z=>((z.1.1,z.1.2.2),z.2)) := by
  let F := fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n) =>
      ((z.1.1,nativeStreamingEdgeSelection d e p z.1.2),z.2)
  let G := fun z : (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T)) ×
        (Configuration n × Configuration n) => ((z.1.1,z.1.2.2),z.2)
  have hF : Measurable F :=
    (measurable_fst.fst.prodMk ((measurable_nativeStreamingEdgeSelection d e p).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hG : Measurable G :=
    (measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd
  have hGF : G ∘ F=(fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2)) := by
    funext z
    dsimp only [G,F,Function.comp_def]
    rw [nativeStreamingEdgeSelection_snd]
  rw [←hGF,←Measure.map_map hG hF,
    nativeStreamingEdgeSelectedFutureLaw_collapse D μ a q Q d hQ hlevels e p hp l]

end QuantitativeFollowup
