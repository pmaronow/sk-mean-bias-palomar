module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginCross
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeVertexEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinementTerminalMoments

@[expose] public section

/-! Actual selected/old and selected/selected cross laws under any exact
observation refinement. Both independent terminal marks and the entire
old record remain present, including equal selections and repeated clocks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem selectedCross_cell_bounds
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) :
    Antitone q ∧ q (e.depth+1)≤Q (observationRefinementDepth d e.depth+p+1) ∧
      Q (observationRefinementDepth d e.depth+p+1)≤q e.depth := by
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    rw [←hlevels i,←hlevels j]
    exact hQ ((observationRefinementDepth_strictMono d).monotone hij)
  · rw [←hlevels (e.depth+1)]
    apply hQ
    change observationRefinementDepth d e.depth+p+1≤
      observationRefinementDepth d e.depth+d e.depth+1
    omega
  · rw [←hlevels e.depth]
    apply hQ
    omega

private def selectedCrossObservedSpinKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap) :
    Kernel (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T))
      (Configuration n × Configuration n) :=
  nativeStreamingEdgeObservedSpinKernel D μ T r ×ₖ
    (nativeStreamingSingleVertexKernel D μ q T v).comap
      (fun z=> (z.1,z.2.2)) (measurable_fst.prodMk measurable_snd.snd)

private instance selectedCrossObservedSpinKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap) :
    IsMarkovKernel (selectedCrossObservedSpinKernel D μ q T v r) := by
  unfold selectedCrossObservedSpinKernel
  infer_instance

private theorem selectedCross_kernel_collapse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (p : ℕ)
    (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingCrossVertexKernel D μ Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingRefinementVertexEmbed d T v)=
      (selectedCrossObservedSpinKernel D μ q T v
        (Q (observationRefinementDepth d e.depth+p+1))).comap
          (Prod.map id (nativeStreamingEdgeSelection d e p))
          (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p)) := by
  ext z : 1
  simp only [nativeStreamingCrossVertexKernel,selectedCrossObservedSpinKernel,
    nativeStreamingEdgeObservedSpinKernel,nativeStreamingSingleVertexKernel,
    Kernel.prod_apply,Kernel.comap_apply]
  dsimp only [Function.uncurry]
  rw [nativeStreamingEdgeSelectedVertex_depth d e p hp,
    nativeStreamingEdgeSelectedVertex_state,nativeStreamingRefinementVertexEmbed_depth,
    hlevels,nativeStreamingRefinementVertexEmbed_state]
  simp only [Prod.map_fst,Prod.map_snd,id_eq,nativeStreamingEdgeSelection_snd]

private theorem selectedCross_EV_projection (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hQ : Antitone Q) (hlevels : ∀i,Q (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (p : ℕ)
    (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingRefinementVertexEmbed d T v)).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      ((anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e
        (Q (observationRefinementDepth d e.depth+p+1))) ⊗ₘ
          selectedCrossObservedSpinKernel D μ q T v
            (Q (observationRefinementDepth d e.depth+p+1))).map
              (fun z=>((z.1.1,z.1.2.2),z.2)) := by
  let A := fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n)=>
      ((z.1.1,nativeStreamingEdgeSelection d e p z.1.2),z.2)
  let B := fun z : (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T)) ×
        (Configuration n × Configuration n)=>((z.1.1,z.1.2.2),z.2)
  have hA : Measurable A :=
    (measurable_fst.fst.prodMk ((measurable_nativeStreamingEdgeSelection d e p).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hB : Measurable B :=
    (measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd
  have hBA : B ∘ A=(fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2)) := by
    funext z
    dsimp only [A,B,Function.comp_def]
    rw [nativeStreamingEdgeSelection_snd]
  rw [←hBA,←Measure.map_map hB hA]
  unfold nativeStreamingCrossVertexLaw
  rw [selectedCross_kernel_collapse D μ q Q d hlevels T e p hp v]
  have H := compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (nativeStreamingEdgeSelection d e p))
    (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p))
    (selectedCrossObservedSpinKernel D μ q T v
      (Q (observationRefinementDepth d e.depth+p+1)))
  rw [nativeStreamingEdgeSelection_joint_law D μ a q Q d hQ hlevels e p hp] at H
  exact congrArg (fun P=>P.map B) H

theorem nativeStreamingSelectedCrossLaw_EV_projection_eq_origin
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (p : ℕ)
    (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingRefinementVertexEmbed d T v)).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      (nativeStreamingOriginCrossProbability D μ a q T
        (.edge e (Q (observationRefinementDepth d e.depth+p+1))) (.vertex v) : Measure _) := by
  let r := Q (observationRefinementDepth d e.depth+p+1)
  let d0 := nativeStreamingEdgeSubdivision e.depth
  let Q0 := nativeStreamingEdgeSchedule q e.depth r
  obtain ⟨hq,hr⟩ := selectedCross_cell_bounds q Q d hQ hlevels T e p hp
  have hQ0 : Antitone Q0 := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hQ00 : Q0 0=1 := by simp [Q0,nativeStreamingEdgeSchedule,hzero]
  have hp0 : 0<d0 e.depth := by simp [d0,nativeStreamingEdgeSubdivision]
  have hmark0 : Q0 (observationRefinementDepth d0 e.depth+0+1)=r := by
    simp [Q0,d0,nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
  have H0 := selectedCross_EV_projection D μ a q Q0 d0 hQ0
    (nativeStreamingEdgeSchedule_refinement q e.depth r) T e 0 hp0 v
  rw [nativeStreamingSelected_one_slot_vertex,hmark0] at H0
  have H := selectedCross_EV_projection D μ a q Q d hQ hlevels T e p hp v
  apply H.trans
  change _=(nativeStreamingCrossVertexProbability D μ a Q0 (observationRefineTree d0 T)
    (nativeStreamingEdgeRefinedVertex d0 e) (nativeStreamingRefinementVertexEmbed d0 T v) :
      Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
        (Configuration n) (observationRefineTree d0 T)) ×
          (Configuration n × Configuration n))).map _
  rw [nativeStreamingCrossVertexProbability_eq_law D μ a Q0 hQ0 hQ00]
  exact H0.symm

theorem nativeStreamingCrossVertexLaw_swap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexLaw D μ a q T v w).map (Prod.map id Prod.swap)=
      nativeStreamingCrossVertexLaw D μ a q T w v := by
  unfold nativeStreamingCrossVertexLaw nativeStreamingCrossVertexKernel
  rw [←Measure.compProd_map measurable_swap,Kernel.map_prod_swap]

theorem nativeStreamingSelectedCrossLaw_VE_projection_eq_origin
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (p : ℕ)
    (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v) (nativeStreamingEdgeSelectedVertex d e p)).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      (nativeStreamingOriginCrossProbability D μ a q T
        (.vertex v) (.edge e (Q (observationRefinementDepth d e.depth+p+1))) : Measure _) := by
  let π := fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n)=>((z.1.1,observationRefinementProject d T z.1.2),z.2)
  have hπ : Measurable π :=
    (measurable_fst.fst.prodMk ((measurable_observationRefinementProject d T).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hswap : Measurable (Prod.map (id : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T → _) (Prod.swap : Configuration n × Configuration n → Configuration n × Configuration n)) :=
    measurable_id.prodMap measurable_swap
  have hswapFine : Measurable (Prod.map (id : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T) → _)
      (Prod.swap : Configuration n × Configuration n → Configuration n × Configuration n)) :=
    measurable_id.prodMap measurable_swap
  have hcomm : π ∘ Prod.map id Prod.swap=Prod.map id Prod.swap ∘ π := rfl
  change _=(nativeStreamingOriginCrossProbability D μ a q T
    (.edge e (Q (observationRefinementDepth d e.depth+p+1))) (.vertex v) :
      Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
        (Configuration n) T) × (Configuration n × Configuration n))).map
      (Prod.map id Prod.swap)
  rw [←nativeStreamingCrossVertexLaw_swap D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingRefinementVertexEmbed d T v),
    Measure.map_map hπ hswapFine,hcomm,←Measure.map_map hswap hπ,
    nativeStreamingSelectedCrossLaw_EV_projection_eq_origin D μ a q Q d hQ hlevels hzero T e p hp v]

theorem nativeStreamingSelectedCrossLaw_EE_projection_eq_origin
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T) (p k : ℕ)
    (hp : p<d e.depth) (hk : k<d f.depth) :
    (nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      (nativeStreamingOriginCrossProbability D μ a q T
        (.edge e (Q (observationRefinementDepth d e.depth+p+1)))
        (.edge f (Q (observationRefinementDepth d f.depth+k+1))) : Measure _) := by
  obtain ⟨hq,hr⟩ := selectedCross_cell_bounds q Q d hQ hlevels T e p hp
  obtain ⟨_,hl⟩ := selectedCross_cell_bounds q Q d hQ hlevels T f k hk
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have H := nativeStreamingOriginCrossProbability_edge_edge D μ a q Q d hq hzero hQ hlevels
    T e f p k hp hk _ _ hr hl rfl rfl
  have HM := congrArg (fun P : ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n))=> (P : Measure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)))) H
  rw [ProbabilityMeasure.toMeasure_map,nativeStreamingCrossVertexProbability_eq_law
    D μ a Q hQ hQ0] at HM
  exact HM

end QuantitativeFollowup
