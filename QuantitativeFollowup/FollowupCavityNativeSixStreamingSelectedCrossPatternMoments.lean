module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedCrossPatternMomentsLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMoments

@[expose] public section

/-! Literal EV, VE and EE attachment moments in any exact subdivision
are the original-tree moments with the selected physical clocks. The
entire original terminal test is projected, and both fresh spins retain
their genuine product law even on diagonal selections. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem selectedCross_terminal_integral
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (P : Measure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n)))
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2) ∂P)=
      ∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂P.map (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2)) := by
  have hm : Measurable (fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n)=>((z.1.1,observationRefinementProject d T z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk ((measurable_observationRefinementProject d T).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hG : Measurable (fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)=>G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (measurable_of_finite G).comp
      (((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_fst.snd).prodMk measurable_snd)
  have H := integral_map (μ:=P) hm.aemeasurable hG.aestronglyMeasurable
  simpa only [Function.comp_def,nativeStreamingRefinementTerminalProject_record] using H.symm

theorem nativeStreamingSelectedCrossTerminalIntegral_EV_eq_origin_moment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (p : ℕ)
    (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2)
      ∂nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingRefinementVertexEmbed d T v))=
      nativeStreamingTerminalMarkMoment (nativeStreamingOriginCrossProbability D μ a q T
        (.edge e (Q (observationRefinementDepth d e.depth+p+1))) (.vertex v)) G := by
  rw [selectedCross_terminal_integral d T,
    nativeStreamingSelectedCrossLaw_EV_projection_eq_origin D μ a q Q d hQ hlevels hzero T e p hp v]
  rfl

theorem nativeStreamingSelectedCrossTerminalIntegral_VE_eq_origin_moment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (p : ℕ)
    (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2)
      ∂nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingRefinementVertexEmbed d T v) (nativeStreamingEdgeSelectedVertex d e p))=
      nativeStreamingTerminalMarkMoment (nativeStreamingOriginCrossProbability D μ a q T
        (.vertex v) (.edge e (Q (observationRefinementDepth d e.depth+p+1)))) G := by
  rw [selectedCross_terminal_integral d T,
    nativeStreamingSelectedCrossLaw_VE_projection_eq_origin D μ a q Q d hQ hlevels hzero T e p hp v]
  rfl

theorem nativeStreamingSelectedCrossTerminalIntegral_EE_eq_origin_moment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T) (p k : ℕ)
    (hp : p<d e.depth) (hk : k<d f.depth)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2)
      ∂nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k))=
      nativeStreamingTerminalMarkMoment (nativeStreamingOriginCrossProbability D μ a q T
        (.edge e (Q (observationRefinementDepth d e.depth+p+1)))
        (.edge f (Q (observationRefinementDepth d f.depth+k+1)))) G := by
  rw [selectedCross_terminal_integral d T,
    nativeStreamingSelectedCrossLaw_EE_projection_eq_origin D μ a q Q d hQ hlevels hzero T e f p k hp hk]
  rfl

theorem nativeStreamingPatternMoment_cross_EV_selected_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (p : ℕ) (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F)
      (.cross (.vertex (nativeStreamingEdgeSelectedVertex d e p))
        (.vertex (nativeStreamingRefinementVertexEmbed d T v)))=
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.edge e (Q (observationRefinementDepth d e.depth+p+1))) (.vertex v)) := by
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have hclock : nativeStreamingOriginCommonClock Q (observationRefineTree d T)
      (.vertex (nativeStreamingEdgeSelectedVertex d e p)) (.vertex (nativeStreamingRefinementVertexEmbed d T v))=
      nativeStreamingOriginCommonClock q T
        (.edge e (Q (observationRefinementDepth d e.depth+p+1))) (.vertex v) := by
    simp only [nativeStreamingOriginCommonClock]
    rw [nativeStreamingSelectedGeometry_commonPathDepth_symm (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingRefinementVertexEmbed d T v)]
    exact nativeStreamingEdgeOldVertex_commonPathClock d q Q T (fun i _=>hlevels i) v e p hp
  simp only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,hclock]
  rw [nativeStreamingOriginCrossProbability_vertex_vertex D μ a Q hQ hQ0]
  simpa only [nativeStreamingTerminalMarkMoment,nativeStreamingDefectSpinTest,
    nativeStreamingRefinedTerminalTest,Function.comp_apply] using
    nativeStreamingSelectedCrossTerminalIntegral_EV_eq_origin_moment D μ a q Q d hQ hlevels hzero T e p hp v
      (nativeStreamingDefectSpinTest T F (nativeStreamingOriginCommonClock q T
        (.edge e (Q (observationRefinementDepth d e.depth+p+1))) (.vertex v)))

theorem nativeStreamingPatternMoment_cross_VE_selected_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (p : ℕ) (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F)
      (.cross (.vertex (nativeStreamingRefinementVertexEmbed d T v))
        (.vertex (nativeStreamingEdgeSelectedVertex d e p)))=
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.vertex v) (.edge e (Q (observationRefinementDepth d e.depth+p+1)))) := by
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have hclock : nativeStreamingOriginCommonClock Q (observationRefineTree d T)
      (.vertex (nativeStreamingRefinementVertexEmbed d T v)) (.vertex (nativeStreamingEdgeSelectedVertex d e p))=
      nativeStreamingOriginCommonClock q T
        (.vertex v) (.edge e (Q (observationRefinementDepth d e.depth+p+1))) := by
    simp only [nativeStreamingOriginCommonClock]
    exact nativeStreamingEdgeOldVertex_commonPathClock d q Q T (fun i _=>hlevels i) v e p hp
  simp only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,hclock]
  rw [nativeStreamingOriginCrossProbability_vertex_vertex D μ a Q hQ hQ0]
  simpa only [nativeStreamingTerminalMarkMoment,nativeStreamingDefectSpinTest,
    nativeStreamingRefinedTerminalTest,Function.comp_apply] using
    nativeStreamingSelectedCrossTerminalIntegral_VE_eq_origin_moment D μ a q Q d hQ hlevels hzero T e p hp v
      (nativeStreamingDefectSpinTest T F (nativeStreamingOriginCommonClock q T
        (.vertex v) (.edge e (Q (observationRefinementDepth d e.depth+p+1)))))

theorem nativeStreamingPatternMoment_cross_EE_selected_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e f : NativeStreamingEdge T) (p k : ℕ) (hp : p<d e.depth) (hk : k<d f.depth) :
    nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F)
      (.cross (.vertex (nativeStreamingEdgeSelectedVertex d e p))
        (.vertex (nativeStreamingEdgeSelectedVertex d f k)))=
      nativeStreamingPatternMoment D μ a q T F
        (.cross (.edge e (Q (observationRefinementDepth d e.depth+p+1)))
          (.edge f (Q (observationRefinementDepth d f.depth+k+1)))) := by
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have hclock : nativeStreamingOriginCommonClock Q (observationRefineTree d T)
      (.vertex (nativeStreamingEdgeSelectedVertex d e p)) (.vertex (nativeStreamingEdgeSelectedVertex d f k))=
      nativeStreamingOriginCommonClock q T
        (.edge e (Q (observationRefinementDepth d e.depth+p+1)))
        (.edge f (Q (observationRefinementDepth d f.depth+k+1))) := by
    simp only [nativeStreamingOriginCommonClock]
    exact nativeStreamingEdgeSelectedVertex_commonPathClock d q Q hQ T (fun i _=>hlevels i) e f p k hp hk
  simp only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,hclock]
  rw [nativeStreamingOriginCrossProbability_vertex_vertex D μ a Q hQ hQ0]
  simpa only [nativeStreamingTerminalMarkMoment,nativeStreamingDefectSpinTest,
    nativeStreamingRefinedTerminalTest,Function.comp_apply] using
    nativeStreamingSelectedCrossTerminalIntegral_EE_eq_origin_moment D μ a q Q d hQ hlevels hzero T e f p k hp hk
      (nativeStreamingDefectSpinTest T F (nativeStreamingOriginCommonClock q T
        (.edge e (Q (observationRefinementDepth d e.depth+p+1)))
        (.edge f (Q (observationRefinementDepth d f.depth+k+1)))))

end QuantitativeFollowup
