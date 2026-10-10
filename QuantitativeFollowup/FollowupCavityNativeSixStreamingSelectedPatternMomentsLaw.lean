module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMoments

@[expose] public section

/-! A selected interior vertex in any exact observation subdivision
projects to the actual one-slot edge law, retaining the entire old
record and its genuine single or current-pair terminal marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem selectedPattern_cell_bounds
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth) :
    Antitone q ∧
      q (e.depth+1) ≤ Q (observationRefinementDepth d e.depth+p+1) ∧
      Q (observationRefinementDepth d e.depth+p+1) ≤ q e.depth := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    rw [←hlevels i, ←hlevels j]
    exact hQ ((observationRefinementDepth_strictMono d).monotone hij)
  · rw [←hlevels (e.depth+1)]
    apply hQ
    change observationRefinementDepth d e.depth+p+1 ≤
      observationRefinementDepth d e.depth+d e.depth+1
    omega
  · rw [←hlevels e.depth]
    apply hQ
    omega

private theorem selectedPattern_single_projection
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth) :
    (nativeStreamingSingleVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p)).map
        (fun z => ((z.1.1, observationRefinementProject d T z.1.2), z.2)) =
      ((anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e
        (Q (observationRefinementDepth d e.depth+p+1))) ⊗ₘ
          nativeStreamingEdgeObservedSpinKernel D μ T
            (Q (observationRefinementDepth d e.depth+p+1))).map
              (fun z => ((z.1.1, z.1.2.2), z.2)) := by
  let A := fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        Configuration n => ((z.1.1, nativeStreamingEdgeSelection d e p z.1.2), z.2)
  let B := fun z : (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T)) ×
        Configuration n => ((z.1.1, z.1.2.2), z.2)
  have hA : Measurable A :=
    (measurable_fst.fst.prodMk ((measurable_nativeStreamingEdgeSelection d e p).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hB : Measurable B :=
    (measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd
  have hBA : B ∘ A = (fun z => ((z.1.1, observationRefinementProject d T z.1.2), z.2)) := by
    funext z
    dsimp only [B, A, Function.comp_def]
    rw [nativeStreamingEdgeSelection_snd]
  rw [←hBA, ←Measure.map_map hB hA,
    nativeStreamingEdgeSelectedMarkedLaw_collapse D μ a q Q d hQ hlevels e p hp]

private theorem selectedPattern_current_collapse
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth) :
    (nativeStreamingCurrentPairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p)).map
        (fun z => ((z.1.1, nativeStreamingEdgeSelection d e p z.1.2), z.2)) =
      (anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e
        (Q (observationRefinementDepth d e.depth+p+1))) ⊗ₘ
          (nativeStreamingEdgeObservedSpinKernel D μ T
            (Q (observationRefinementDepth d e.depth+p+1)) ×ₖ
              nativeStreamingEdgeObservedSpinKernel D μ T
                (Q (observationRefinementDepth d e.depth+p+1))) := by
  have hk : nativeStreamingCurrentPairKernel D μ Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) =
      (nativeStreamingEdgeObservedSpinKernel D μ T
        (Q (observationRefinementDepth d e.depth+p+1)) ×ₖ
          nativeStreamingEdgeObservedSpinKernel D μ T
            (Q (observationRefinementDepth d e.depth+p+1))).comap
        (Prod.map id (nativeStreamingEdgeSelection d e p))
        (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p)) := by
    ext z σ hs
    simp only [nativeStreamingCurrentPairKernel, nativeStreamingEdgeObservedSpinKernel,
      Kernel.comap_apply, Kernel.prod_apply, Function.uncurry_def]
    rw [nativeStreamingEdgeSelectedVertex_depth d e p hp, nativeStreamingEdgeSelectedVertex_state]
    rfl
  unfold nativeStreamingCurrentPairLaw
  rw [hk]
  have H := compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (nativeStreamingEdgeSelection d e p))
    (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p))
    (nativeStreamingEdgeObservedSpinKernel D μ T
      (Q (observationRefinementDepth d e.depth+p+1)) ×ₖ
        nativeStreamingEdgeObservedSpinKernel D μ T
          (Q (observationRefinementDepth d e.depth+p+1)))
  rw [nativeStreamingEdgeSelection_joint_law D μ a q Q d hQ hlevels e p hp] at H
  exact H

private theorem selectedPattern_current_projection
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth) :
    (nativeStreamingCurrentPairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p)).map
        (fun z => ((z.1.1, observationRefinementProject d T z.1.2), z.2)) =
      ((anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e
        (Q (observationRefinementDepth d e.depth+p+1))) ⊗ₘ
          (nativeStreamingEdgeObservedSpinKernel D μ T
            (Q (observationRefinementDepth d e.depth+p+1)) ×ₖ
              nativeStreamingEdgeObservedSpinKernel D μ T
                (Q (observationRefinementDepth d e.depth+p+1)))).map
                  (fun z => ((z.1.1, z.1.2.2), z.2)) := by
  let A := fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n) =>
      ((z.1.1, nativeStreamingEdgeSelection d e p z.1.2), z.2)
  let B := fun z : (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T)) ×
        (Configuration n × Configuration n) => ((z.1.1, z.1.2.2), z.2)
  have hA : Measurable A :=
    (measurable_fst.fst.prodMk ((measurable_nativeStreamingEdgeSelection d e p).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hB : Measurable B :=
    (measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd
  have hBA : B ∘ A = (fun z => ((z.1.1, observationRefinementProject d T z.1.2), z.2)) := by
    funext z
    dsimp only [B, A, Function.comp_def]
    rw [nativeStreamingEdgeSelection_snd]
  rw [←hBA, ←Measure.map_map hB hA,
    selectedPattern_current_collapse D μ a q Q d hQ hlevels T e p hp]

theorem nativeStreamingSelectedSingleLaw_projection_eq_edge_probability
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth) :
    (nativeStreamingSingleVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p)).map
        (fun z => ((z.1.1, observationRefinementProject d T z.1.2), z.2)) =
      (nativeStreamingEdgeSingleMarkProbability D μ a q T e
        (Q (observationRefinementDepth d e.depth+p+1)) : Measure _) := by
  let r := Q (observationRefinementDepth d e.depth+p+1)
  let d0 := nativeStreamingEdgeSubdivision e.depth
  let Q0 := nativeStreamingEdgeSchedule q e.depth r
  obtain ⟨hq, hr⟩ := selectedPattern_cell_bounds q Q d hQ hlevels T e p hp
  have hQ0 : Antitone Q0 := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hQ00 : Q0 0 = 1 := by simpa [Q0, nativeStreamingEdgeSchedule] using hzero
  have hp0 : 0 < d0 e.depth := by simp [d0, nativeStreamingEdgeSubdivision]
  have hmark0 : Q0 (observationRefinementDepth d0 e.depth+0+1) = r := by
    simp [Q0, d0, nativeStreamingEdgeSubdivision_depth, nativeStreamingEdgeSchedule]
  have H0 := selectedPattern_single_projection D μ a q Q0 d0 hQ0
    (nativeStreamingEdgeSchedule_refinement q e.depth r) T e 0 hp0
  rw [nativeStreamingSelected_one_slot_vertex, hmark0] at H0
  have H := selectedPattern_single_projection D μ a q Q d hQ hlevels T e p hp
  apply H.trans
  change _ = (nativeStreamingSingleVertexProbability D μ a Q0 (observationRefineTree d0 T)
    (nativeStreamingEdgeRefinedVertex d0 e) : Measure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d0 T)) ×
        Configuration n)).map _
  rw [nativeStreamingSingleVertexProbability_eq_law D μ a Q0 hQ0 hQ00]
  exact H0.symm

theorem nativeStreamingSelectedCurrentLaw_projection_eq_edge_probability
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i, Q (observationRefinementDepth d i) = q i) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth) :
    (nativeStreamingCurrentPairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p)).map
        (fun z => ((z.1.1, observationRefinementProject d T z.1.2), z.2)) =
      (nativeStreamingEdgeCurrentPairProbability D μ a q T e
        (Q (observationRefinementDepth d e.depth+p+1)) : Measure _) := by
  let r := Q (observationRefinementDepth d e.depth+p+1)
  let d0 := nativeStreamingEdgeSubdivision e.depth
  let Q0 := nativeStreamingEdgeSchedule q e.depth r
  obtain ⟨hq, hr⟩ := selectedPattern_cell_bounds q Q d hQ hlevels T e p hp
  have hQ0 : Antitone Q0 := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hQ00 : Q0 0 = 1 := by simpa [Q0, nativeStreamingEdgeSchedule] using hzero
  have hp0 : 0 < d0 e.depth := by simp [d0, nativeStreamingEdgeSubdivision]
  have hmark0 : Q0 (observationRefinementDepth d0 e.depth+0+1) = r := by
    simp [Q0, d0, nativeStreamingEdgeSubdivision_depth, nativeStreamingEdgeSchedule]
  have H0 := selectedPattern_current_projection D μ a q Q0 d0 hQ0
    (nativeStreamingEdgeSchedule_refinement q e.depth r) T e 0 hp0
  rw [nativeStreamingSelected_one_slot_vertex, hmark0] at H0
  have H := selectedPattern_current_projection D μ a q Q d hQ hlevels T e p hp
  apply H.trans
  change _ = (nativeStreamingCurrentPairProbability D μ a Q0 (observationRefineTree d0 T)
    (nativeStreamingEdgeRefinedVertex d0 e) : Measure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d0 T)) ×
        (Configuration n × Configuration n))).map _
  rw [nativeStreamingCurrentPairProbability_eq_law D μ a Q0 hQ0 hQ00]
  exact H0.symm

end QuantitativeFollowup
