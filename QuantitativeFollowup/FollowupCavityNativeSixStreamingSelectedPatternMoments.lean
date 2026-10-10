module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedPatternMomentsLaw
public import FourPapersCommon.FiniteObservationRefinementTerminalLeaves

@[expose] public section

/-! Literal terminal pattern moments at selected subdivision vertices
are the coarse edge pattern moments, with every original terminal leaf
and its true common-history defect clock retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem selectedPattern_terminal_record {E S : Type}
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (z : Records E S (observationRefineTree d T)) :
    observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z) =
        finiteCascadeRecordTerminalSpins T (observationRefinementProject d T z) := by
  simpa only [observationTreeDepthCast, observationRefinementDepthProject,
    observationRecordDepthCast, Function.comp_apply, id_eq] using
    observationRefinementTerminalProject_record d T rfl z

private theorem selectedPattern_terminal_leaf {S : Type}
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J) (i : ObservationLeaf T)
    (σ : TerminalSpins S (observationRefineTree d T)) :
    observationTerminalSpin (observationRefineTree d T) (observationRefinementLeafEmbed d T i) σ =
      observationTerminalSpin T i (observationRefinementTerminalProject d T rfl σ) := by
  simpa only [observationRefinementDepthLeafEmbed, observationTreeDepthCast] using
    (observationRefinementTerminalProject_leaf d T rfl i σ).symm

private theorem selectedPattern_pad_leaf_vertex {j : ℕ}
    (T : FiniteTerminalGenealogy j) (k : ℕ) (i : ObservationLeaf T) :
    observationLeafVertex (observationTreePad T k) (observationPadLeafEmbed T k i) =
      nativeStreamingPadVertexEmbed T k (observationLeafVertex T i) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg FiniteCascadeRecordVertex.child ih

private theorem selectedPattern_refined_leaf_vertex
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J) (i : ObservationLeaf T) :
    observationLeafVertex (observationRefineTree d T) (observationRefinementLeafEmbed d T i) =
      nativeStreamingRefinementVertexEmbed d T (observationLeafVertex T i) := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
      change FiniteCascadeRecordVertex.child
        (observationLeafVertex (observationTreePad (observationRefineTree d T) (d j))
          (observationPadLeafEmbed _ _ (observationRefinementLeafEmbed d T i))) = _
      rw [selectedPattern_pad_leaf_vertex, ih]
      rfl
  | fork T U ihT ihU => cases i with
    | inl i => exact congrArg FiniteCascadeRecordVertex.left (ihT i)
    | inr i => exact congrArg FiniteCascadeRecordVertex.right (ihU i)

private theorem selectedPattern_marked_integral {A : Type}
    [MeasurableSpace A] [MeasurableSingletonClass A] [Finite A]
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (P : Measure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) × A))
    (G : TerminalSpins (Configuration n) T × A → ℝ) :
    (∫z, G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2), z.2) ∂P) =
        ∫z, G (finiteCascadeRecordTerminalSpins T z.1.2, z.2)
          ∂P.map (fun z => ((z.1.1, observationRefinementProject d T z.1.2), z.2)) := by
  have hm : Measurable (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) × A) =>
      ((z.1.1, observationRefinementProject d T z.1.2), z.2)) :=
    (measurable_fst.fst.prodMk ((measurable_observationRefinementProject d T).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hG : Measurable (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × A) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2, z.2)) :=
    (measurable_of_finite G).comp
      (((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_fst.snd).prodMk measurable_snd)
  have H := integral_map (μ := P) hm.aemeasurable hG.aestronglyMeasurable
  simpa only [Function.comp_def, selectedPattern_terminal_record] using H.symm

theorem nativeStreamingSelectedSingleTerminalIntegral_eq_edge_moment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth)
    (G : TerminalSpins (Configuration n) T × Configuration n → ℝ) :
    (∫z, G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2), z.2)
      ∂nativeStreamingSingleVertexLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingEdgeSelectedVertex d e p)) =
      nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgeSingleMarkProbability D μ a q T e
          (Q (observationRefinementDepth d e.depth+p+1))) G := by
  rw [selectedPattern_marked_integral d T,
    nativeStreamingSelectedSingleLaw_projection_eq_edge_probability D μ a q Q d hQ
      hlevels hzero T e p hp]
  rfl

theorem nativeStreamingSelectedCurrentTerminalIntegral_eq_edge_moment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z, G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2), z.2)
      ∂nativeStreamingCurrentPairLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingEdgeSelectedVertex d e p)) =
      nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgeCurrentPairProbability D μ a q T e
          (Q (observationRefinementDepth d e.depth+p+1))) G := by
  rw [selectedPattern_marked_integral d T,
    nativeStreamingSelectedCurrentLaw_projection_eq_edge_probability D μ a q Q d hQ
      hlevels hzero T e p hp]
  rfl

theorem nativeStreamingPatternMoment_originalFresh_selected_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (e : NativeStreamingEdge T) (p : ℕ) (hp : p < d e.depth) :
    nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
      (F ∘ observationRefinementTerminalProject d T rfl)
      (.originalFresh (observationRefinementLeafEmbed d T i)
        (.vertex (nativeStreamingEdgeSelectedVertex d e p))) =
      nativeStreamingPatternMoment D μ a q T F
        (.originalFresh i (.edge e (Q (observationRefinementDepth d e.depth+p+1)))) := by
  have hQ0 : Q 0 = 1 := by
    simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have hclock : nativeStreamingOriginCommonClock Q (observationRefineTree d T)
      (.vertex (observationLeafVertex (observationRefineTree d T) (observationRefinementLeafEmbed d T i)))
      (.vertex (nativeStreamingEdgeSelectedVertex d e p)) =
      nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i))
        (.edge e (Q (observationRefinementDepth d e.depth+p+1))) := by
    simp only [nativeStreamingOriginCommonClock, selectedPattern_refined_leaf_vertex]
    exact nativeStreamingEdgeOldLeaf_commonPathClock_eq_mark d q Q T (fun j _ => hlevels j)
      i e p hp _ rfl
  simp only [nativeStreamingPatternMoment, nativeStreamingOriginSingleProbability, hclock,
    nativeStreamingTerminalMarkMoment]
  rw [nativeStreamingSingleVertexProbability_eq_law D μ a Q hQ hQ0]
  trans ∫z, nativeStreamingOriginalFreshSpinTest T F i
    (nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i))
      (.edge e (Q (observationRefinementDepth d e.depth+p+1))))
      (observationRefinementTerminalProject d T rfl
        (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2), z.2)
      ∂nativeStreamingSingleVertexLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingEdgeSelectedVertex d e p)
  · apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    simp only [nativeStreamingOriginalFreshSpinTest, Function.comp_apply,
      selectedPattern_terminal_leaf]
  · exact nativeStreamingSelectedSingleTerminalIntegral_eq_edge_moment D μ a q Q d hQ
      hlevels hzero T e p hp _

theorem nativeStreamingPatternMoment_current_selected_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (p : ℕ) (hp : p < d e.depth) :
    nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
      (F ∘ observationRefinementTerminalProject d T rfl)
      (.current (.vertex (nativeStreamingEdgeSelectedVertex d e p))) =
      nativeStreamingPatternMoment D μ a q T F
        (.current (.edge e (Q (observationRefinementDepth d e.depth+p+1)))) := by
  have hQ0 : Q 0 = 1 := by
    simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  simp only [nativeStreamingPatternMoment, nativeStreamingOriginCurrentProbability,
    nativeStreamingOriginLevel, nativeStreamingTerminalMarkMoment,
    nativeStreamingEdgeSelectedVertex_depth d e p hp]
  rw [nativeStreamingCurrentPairProbability_eq_law D μ a Q hQ hQ0]
  simpa only [nativeStreamingTerminalMarkMoment, nativeStreamingDefectSpinTest,
    Function.comp_apply] using
    nativeStreamingSelectedCurrentTerminalIntegral_eq_edge_moment D μ a q Q d hQ
      hlevels hzero T e p hp
      (nativeStreamingDefectSpinTest T F (Q (observationRefinementDepth d e.depth+p+1)))

end QuantitativeFollowup
