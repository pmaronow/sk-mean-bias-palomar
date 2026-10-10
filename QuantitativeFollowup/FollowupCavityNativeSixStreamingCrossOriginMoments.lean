module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeVertexHalfClosedFamilyIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairHalfClosedFamilyIntegral

@[expose] public section

/-! Cross attachment integrability comes from the actual bounded terminal
tests and measurable two-mark laws. Reversing an edge/vertex attachment
swaps only the two genuine fresh spins; every old record is retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem nativeStreamingSpinOverlapDefect_swap (q : ℝ)
    (σ τ : Configuration (n+1)) :
    cavitySpinOverlapDefect n q σ τ=cavitySpinOverlapDefect n q τ σ := by
  unfold cavitySpinOverlapDefect
  have hs : (∑i : Fin n, anisotropicCouplingFeature (cavityIncidentEdge i) σ *
      anisotropicCouplingFeature (cavityIncidentEdge i) τ) =
      ∑i : Fin n, anisotropicCouplingFeature (cavityIncidentEdge i) τ *
        anisotropicCouplingFeature (cavityIncidentEdge i) σ := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hs]
  ring

theorem nativeStreamingTerminalDefectMoment_fresh_swap
    (T : FiniteTerminalGenealogy J)
    (P : ProbabilityMeasure ((AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
        (Configuration (n+1) × Configuration (n+1))))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (q : Paper.Overlap) :
    nativeStreamingTerminalMarkMoment (P.map (fun z => (z.1,(z.2.2,z.2.1))))
      (nativeStreamingDefectSpinTest T F q) =
      nativeStreamingTerminalMarkMoment P (nativeStreamingDefectSpinTest T F q) := by
  let X := ((AnisotropicObservationState (n+1) ×
    Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
      (Configuration (n+1) × Configuration (n+1)))
  have hm : Measurable (fun z : X => (z.1,(z.2.2,z.2.1))) :=
    measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst)
  have hc : Continuous (fun z : X => nativeStreamingDefectSpinTest T F q
      (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f:=nativeStreamingDefectSpinTest T F q)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk
        continuous_snd)
  unfold nativeStreamingTerminalMarkMoment
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun z => by
    simp only [nativeStreamingDefectSpinTest]
    rw [nativeStreamingSpinOverlapDefect_swap]

theorem nativeStreamingPatternMoment_cross_vertex_edge
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T) (r : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.edge e r)) =
      nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.vertex v)) := by
  simp only [nativeStreamingPatternMoment, nativeStreamingOriginCrossProbability,
    nativeStreamingOriginCommonClock]
  exact nativeStreamingTerminalDefectMoment_fresh_swap T _ F _

theorem integrable_nativeStreamingEdgeVertexTerminalMoment_Ioc
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀r σ, |G r σ|≤C) :
    Integrable (fun r => nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeVertexPairProbability D μ a q T e v r) (G r))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  have hi : Integrable (nativeStreamingEdgeVertexFamilyHalfClosedMoment D μ a q T e v G)
      (parisiFreeMeasure μ a) :=
    (integrable_const C).mono'
      (measurable_nativeStreamingEdgeVertexFamilyHalfClosedMoment D μ a q hq T e v G hG).aestronglyMeasurable
      (.of_forall fun r => by
        simpa only [Real.norm_eq_abs] using
          nativeStreamingEdgeVertexFamilyHalfClosedMoment_abs_le D μ a q T e v G C hC hbound r)
  apply hi.restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [nativeStreamingEdgeVertexFamilyHalfClosedMoment, mem_Ioc.mp hr, and_self, ite_true]

theorem integrable_nativeStreamingEdgePairTerminalMoment_Ioc_prod
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e f : NativeStreamingEdge T) (S : Finset Paper.Overlap)
    (G : Paper.Overlap × Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun z => G z σ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀z σ, |G z σ|≤C) :
    Integrable (fun z : Paper.Overlap × Paper.Overlap => nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgePairProbability D μ a q T e f z.1 z.2) (G z))
      (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
        ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth)))) := by
  have hi : Integrable (nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q T e f S G)
      ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) :=
    (integrable_const C).mono'
      (measurable_nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q hq T e f S G hG).aestronglyMeasurable
      (.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using
          nativeStreamingEdgePairFamilyHalfClosedMoment_abs_le D μ a q T e f S G C hC hbound z)
  rw [Measure.prod_restrict]
  apply hi.restrict.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
  have hm : nativeStreamingEdgePairHalfClosedCondition q e f z := ⟨hz.1,hz.2⟩
  simp only [nativeStreamingEdgePairFamilyHalfClosedMoment, hm, ite_true]

end QuantitativeFollowup
