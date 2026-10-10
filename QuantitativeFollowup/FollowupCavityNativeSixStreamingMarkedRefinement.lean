module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexRefinement
public import FourPapersCommon.CompProdComapMap

@[expose] public section

/-! Prescribed ancestral fresh marks commute with exact observation
refinement. The complete original record remains jointly present, and
the mark is drawn from its true normalized restarted terminal kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingSingleVertexKernel_refinement (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingSingleVertexKernel D μ Q (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v)=
      (nativeStreamingSingleVertexKernel D μ q T v).comap
        (Prod.map id (observationRefinementProject d T))
        (measurable_id.prodMap (measurable_observationRefinementProject d T)) := by
  ext z σ hs
  change (anisotropicObservationTerminalSpinKernel D μ
    (Q (nativeStreamingRefinementVertexEmbed d T v).depth)
      (nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T v) z.1 z.2)) σ=
    (anisotropicObservationTerminalSpinKernel D μ (q v.depth)
      (nativeStreamingVertexState v z.1 (observationRefinementProject d T z.2))) σ
  rw [nativeStreamingRefinementVertexEmbed_depth,hlevels,
    nativeStreamingRefinementVertexEmbed_state]

theorem nativeStreamingSingleVertexLaw_refinement (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingSingleVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v)).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      nativeStreamingSingleVertexLaw D μ a q T v := by
  unfold nativeStreamingSingleVertexLaw
  rw [nativeStreamingSingleVertexKernel_refinement D μ q Q d hlevels T v]
  have he:=compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (observationRefinementProject d T))
    (measurable_id.prodMap (measurable_observationRefinementProject d T))
    (nativeStreamingSingleVertexKernel D μ q T v)
  rw [anisotropicRecordedProfileTreeLaw_refinement D μ a q Q d hQ hlevels T] at he
  exact he

end QuantitativeFollowup
