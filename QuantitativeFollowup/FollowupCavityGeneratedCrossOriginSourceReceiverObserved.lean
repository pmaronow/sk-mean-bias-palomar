module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverBaseLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedCrossPatternMomentsLaw

@[expose] public section

/-! The edge-and-vertex pair probability is the genuine selected ancestral
state/whole-record law followed by its independent terminal-spin product. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n J : ℕ}

def printedGeneratedEdgeVertexObservedSpinKernel
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap) :
    Kernel (AnisotropicObservationState n ×
      (AnisotropicObservationState n × Records (AnisotropicObservationState n) (Configuration n) T))
      (Configuration n × Configuration n) :=
  nativeStreamingEdgeObservedSpinKernel D μ T r ×ₖ
    (nativeStreamingSingleVertexKernel D μ q T v).comap
      (fun z => (z.1,z.2.2)) (measurable_fst.prodMk measurable_snd.snd)

instance printedGeneratedEdgeVertexObservedSpinKernel_markov
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap) :
    IsMarkovKernel (printedGeneratedEdgeVertexObservedSpinKernel D μ q T v r) := by
  unfold printedGeneratedEdgeVertexObservedSpinKernel
  infer_instance

theorem printedGeneratedEdgeVertexObservedSpinKernel_refinement
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i, Q (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (p : ℕ)
    (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingCrossVertexKernel D μ Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingRefinementVertexEmbed d T v) =
      (printedGeneratedEdgeVertexObservedSpinKernel D μ q T v
        (Q (observationRefinementDepth d e.depth+p+1))).comap
          (Prod.map id (nativeStreamingEdgeSelection d e p))
          (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p)) := by
  ext z : 1
  simp only [nativeStreamingCrossVertexKernel,printedGeneratedEdgeVertexObservedSpinKernel,
    nativeStreamingEdgeObservedSpinKernel,nativeStreamingSingleVertexKernel,
    Kernel.prod_apply,Kernel.comap_apply]
  dsimp only [Function.uncurry]
  rw [nativeStreamingEdgeSelectedVertex_depth d e p hp,
    nativeStreamingEdgeSelectedVertex_state,nativeStreamingRefinementVertexEmbed_depth,
    hlevels,nativeStreamingRefinementVertexEmbed_state]
  simp only [Prod.map_fst,Prod.map_snd,id_eq,nativeStreamingEdgeSelection_snd]

def printedGeneratedEdgeVertexObservedLaw
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap) :
    Measure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × (Configuration n × Configuration n)) :=
  ((anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e r) ⊗ₘ
    printedGeneratedEdgeVertexObservedSpinKernel D μ q T v r).map
      (fun z => ((z.1.1,z.1.2.2),z.2))

private theorem printedGeneratedObserved_refinement_projection
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hQ : Antitone Q) (hlevels : ∀i, Q (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (p : ℕ)
    (hp : p<d e.depth) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingRefinementVertexEmbed d T v)).map
        (fun z => ((z.1.1,observationRefinementProject d T z.1.2),z.2)) =
      printedGeneratedEdgeVertexObservedLaw D μ a q T e v
        (Q (observationRefinementDepth d e.depth+p+1)) := by
  let A := fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T)) ×
        (Configuration n × Configuration n) => ((z.1.1,nativeStreamingEdgeSelection d e p z.1.2),z.2)
  let B := fun z : (AnisotropicObservationState n × (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T)) ×
        (Configuration n × Configuration n) => ((z.1.1,z.1.2.2),z.2)
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
  rw [printedGeneratedEdgeVertexObservedSpinKernel_refinement D μ q Q d hlevels T e p hp v]
  have H := compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (nativeStreamingEdgeSelection d e p))
    (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p))
    (printedGeneratedEdgeVertexObservedSpinKernel D μ q T v
      (Q (observationRefinementDepth d e.depth+p+1)))
  rw [nativeStreamingEdgeSelection_joint_law D μ a q Q d hQ hlevels e p hp] at H
  exact congrArg (fun M=>M.map B) H

theorem printedGeneratedEdgeVertexObservedLaw_eq_probability
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hq0 : q 0=1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap)
    (hr : q (e.depth+1)≤r ∧ r≤q e.depth) :
    printedGeneratedEdgeVertexObservedLaw D μ a q T e v r =
      (nativeStreamingOriginCrossProbability D μ a q T (.edge e r) (.vertex v) : Measure _) := by
  let d := nativeStreamingEdgeSubdivision e.depth
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hp : 0<d e.depth := by simp only [d,nativeStreamingEdgeSubdivision,if_true]; norm_num
  have hlevels : ∀j, Q (observationRefinementDepth d j)=q j :=
    nativeStreamingEdgeSchedule_refinement q e.depth r
  have hmark : Q (observationRefinementDepth d e.depth+0+1)=r := by
    simp only [Q,d,nativeStreamingEdgeSubdivision_depth,if_true,nativeStreamingEdgeSchedule,
      Nat.add_zero,Nat.le_refl,if_false,show ¬e.depth+1≤e.depth by omega]
  have H := (printedGeneratedObserved_refinement_projection D μ a q Q d hQ hlevels T e 0 hp v).symm.trans
    (nativeStreamingSelectedCrossLaw_EV_projection_eq_origin D μ a q Q d hQ hlevels hq0 T e 0 hp v)
  simpa only [hmark] using H

end QuantitativeFollowup
