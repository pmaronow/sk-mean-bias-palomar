module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsLaw

@[expose] public section

/-! Terminal tests and their actual single/current marked moments survive
the genuine endpoint observations. The original/fresh chosen leaves keep
their physical common ancestor clock, including the terminal endpoint. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

@[reducible] def nativeStreamingGeneratedEndpointTerminalProject {S : Type}
    (W : CavityGeneratedConstructedComponent m) :
    TerminalSpins S (nativeStreamingGeneratedEndpointComponent W).tree → TerminalSpins S W.tree :=
  nativeStreamingEndpointTerminalProject W.tree

@[reducible] def nativeStreamingGeneratedEndpointTerminalTest {S : Type}
    (W : CavityGeneratedConstructedComponent m) (F : TerminalSpins S W.tree → ℝ) :
    TerminalSpins S (nativeStreamingGeneratedEndpointComponent W).tree → ℝ :=
  F ∘ nativeStreamingGeneratedEndpointTerminalProject W

@[reducible] def nativeStreamingGeneratedEndpointLeaf
    (W : CavityGeneratedConstructedComponent m) (i : ObservationLeaf W.tree) :
    ObservationLeaf (nativeStreamingGeneratedEndpointComponent W).tree :=
  nativeStreamingEndpointLiftLeaf W.tree i

theorem nativeStreamingGeneratedEndpointTerminalProject_record {E S : Type}
    (W : CavityGeneratedConstructedComponent m)
    (z : Records E S (nativeStreamingGeneratedEndpointComponent W).tree) :
    nativeStreamingGeneratedEndpointTerminalProject W (finiteCascadeRecordTerminalSpins _ z) =
      finiteCascadeRecordTerminalSpins W.tree (nativeStreamingGeneratedEndpointRecordProject W z) :=
  nativeStreamingEndpointTerminalProject_record W.tree z.2

theorem nativeStreamingGeneratedEndpointTerminalProject_leaf {S : Type}
    (W : CavityGeneratedConstructedComponent m) (i : ObservationLeaf W.tree)
    (σ : TerminalSpins S (nativeStreamingGeneratedEndpointComponent W).tree) :
    observationTerminalSpin W.tree i (nativeStreamingGeneratedEndpointTerminalProject W σ) =
      observationTerminalSpin _ (nativeStreamingGeneratedEndpointLeaf W i) σ :=
  nativeStreamingEndpointTerminalProject_leaf W.tree i σ

theorem nativeStreamingGeneratedEndpointLeaf_vertex_commonClock
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree) (i : ObservationLeaf W.tree) :
    nativeStreamingOriginCommonClock (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree
      (.vertex (observationLeafVertex _ (nativeStreamingGeneratedEndpointLeaf W i)))
      (.vertex (nativeStreamingGeneratedEndpointVertex W v)) =
    nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock W h) W.tree
      (.vertex (observationLeafVertex W.tree i)) (.vertex v) := by
  change nativeStreamingGeneratedEndpointClock W h
    (finiteCascadeCommonPathDepth (observationTerminalUnaryLift W.tree)
      (observationLeafVertex _ (nativeStreamingEndpointLiftLeaf W.tree i)) (nativeStreamingEndpointLiftVertex v)) = _
  rw [nativeStreamingEndpointLiftLeaf_vertex_commonDepth,nativeStreamingGeneratedEndpointClock_succ]
  rfl

theorem nativeStreamingGeneratedEndpoint_single_terminal_integral
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree)
    (G : TerminalSpins (Configuration n) W.tree × Configuration n → ℝ) :
    (∫ z, G (nativeStreamingGeneratedEndpointTerminalProject W (finiteCascadeRecordTerminalSpins _ z.1.2),z.2)
      ∂nativeStreamingSingleVertexLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
        (nativeStreamingGeneratedEndpointComponent W).tree (nativeStreamingGeneratedEndpointVertex W v)) =
    ∫ z, G (finiteCascadeRecordTerminalSpins W.tree z.1.2,z.2)
      ∂nativeStreamingSingleVertexLaw D μ a (nativeStreamingGeneratedComponentClock W h) W.tree v := by
  have hm : Measurable (Prod.map
      (Prod.map (id : AnisotropicObservationState n → AnisotropicObservationState n)
        (nativeStreamingGeneratedEndpointRecordProject (S:=Configuration n) W))
      (id : Configuration n → Configuration n)) :=
    (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject
      (E:=AnisotropicObservationState n) (S:=Configuration n) W)).prodMap measurable_id
  have hc : Continuous (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) W.tree) × Configuration n) =>
      G (finiteCascadeRecordTerminalSpins W.tree z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f:=G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins W.tree).comp continuous_fst.snd).prodMk continuous_snd)
  rw [←nativeStreamingGeneratedEndpoint_single_law D μ a W h v,
    integral_map hm.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G
    (Prod.ext (nativeStreamingGeneratedEndpointTerminalProject_record W z.1.2) rfl)

theorem nativeStreamingGeneratedEndpoint_current_terminal_integral
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree)
    (G : TerminalSpins (Configuration n) W.tree × (Configuration n × Configuration n) → ℝ) :
    (∫ z, G (nativeStreamingGeneratedEndpointTerminalProject W (finiteCascadeRecordTerminalSpins _ z.1.2),z.2)
      ∂nativeStreamingCurrentPairLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
        (nativeStreamingGeneratedEndpointComponent W).tree (nativeStreamingGeneratedEndpointVertex W v)) =
    ∫ z, G (finiteCascadeRecordTerminalSpins W.tree z.1.2,z.2)
      ∂nativeStreamingCurrentPairLaw D μ a (nativeStreamingGeneratedComponentClock W h) W.tree v := by
  have hm : Measurable (Prod.map
      (Prod.map (id : AnisotropicObservationState n → AnisotropicObservationState n)
        (nativeStreamingGeneratedEndpointRecordProject (S:=Configuration n) W))
      (id : Configuration n × Configuration n → Configuration n × Configuration n)) :=
    (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject
      (E:=AnisotropicObservationState n) (S:=Configuration n) W)).prodMap measurable_id
  have hc : Continuous (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) W.tree) × (Configuration n × Configuration n)) =>
      G (finiteCascadeRecordTerminalSpins W.tree z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f:=G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins W.tree).comp continuous_fst.snd).prodMk continuous_snd)
  rw [←nativeStreamingGeneratedEndpoint_current_law D μ a W h v,
    integral_map hm.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G
    (Prod.ext (nativeStreamingGeneratedEndpointTerminalProject_record W z.1.2) rfl)

theorem nativeStreamingGeneratedEndpoint_originalFresh_moment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree) (F : TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (i : ObservationLeaf W.tree) :
    nativeStreamingPatternMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEndpointComponent W) h)
      (nativeStreamingGeneratedEndpointComponent W).tree (nativeStreamingGeneratedEndpointTerminalTest W F)
      (.originalFresh (nativeStreamingGeneratedEndpointLeaf W i)
        (.vertex (nativeStreamingGeneratedEndpointVertex W v))) =
    nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h) W.tree F
      (.originalFresh i (.vertex v)) := by
  rw [nativeStreamingGeneratedEndpointComponent_clock]
  have hq := nativeStreamingGeneratedComponentClock_antitone W h
  have hzero := nativeStreamingGeneratedComponentClock_terminal W h
  have hQ : Antitone (nativeStreamingGeneratedEndpointClock W h) := by
    rw [←nativeStreamingGeneratedEndpointComponent_clock]
    exact nativeStreamingGeneratedComponentClock_antitone _ h
  have hQ0 := nativeStreamingGeneratedEndpointClock_zero W h
  have hc := nativeStreamingGeneratedEndpointLeaf_vertex_commonClock W h v i
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginSingleProbability,
    nativeStreamingTerminalMarkMoment,hc]
  rw [nativeStreamingSingleVertexProbability_eq_law D μ a _ hQ hQ0,
    nativeStreamingSingleVertexProbability_eq_law D μ a _ hq hzero]
  have H := nativeStreamingGeneratedEndpoint_single_terminal_integral D μ a W h v
    (nativeStreamingOriginalFreshSpinTest W.tree F i
      (nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock W h) W.tree
        (.vertex (observationLeafVertex W.tree i)) (.vertex v)))
  convert H using 1
  congr 1
  funext z
  simp only [nativeStreamingOriginalFreshSpinTest,nativeStreamingGeneratedEndpointTerminalTest,Function.comp_apply]
  rw [nativeStreamingGeneratedEndpointTerminalProject_leaf]

theorem nativeStreamingGeneratedEndpoint_current_moment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree) (F : TerminalSpins (Configuration (n+1)) W.tree → ℝ) :
    nativeStreamingPatternMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEndpointComponent W) h)
      (nativeStreamingGeneratedEndpointComponent W).tree (nativeStreamingGeneratedEndpointTerminalTest W F)
      (.current (.vertex (nativeStreamingGeneratedEndpointVertex W v))) =
    nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h) W.tree F
      (.current (.vertex v)) := by
  rw [nativeStreamingGeneratedEndpointComponent_clock]
  have hq := nativeStreamingGeneratedComponentClock_antitone W h
  have hzero := nativeStreamingGeneratedComponentClock_terminal W h
  have hQ : Antitone (nativeStreamingGeneratedEndpointClock W h) := by
    rw [←nativeStreamingGeneratedEndpointComponent_clock]
    exact nativeStreamingGeneratedComponentClock_antitone _ h
  have hQ0 := nativeStreamingGeneratedEndpointClock_zero W h
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginCurrentProbability,
    nativeStreamingOriginLevel,nativeStreamingTerminalMarkMoment,nativeStreamingGeneratedEndpointVertex_depth,
    nativeStreamingGeneratedEndpointClock_succ]
  rw [nativeStreamingCurrentPairProbability_eq_law D μ a _ hQ hQ0,
    nativeStreamingCurrentPairProbability_eq_law D μ a _ hq hzero]
  simpa only [nativeStreamingDefectSpinTest,nativeStreamingGeneratedEndpointTerminalTest,Function.comp_apply] using
    nativeStreamingGeneratedEndpoint_current_terminal_integral D μ a W h v
      (nativeStreamingDefectSpinTest W.tree F (nativeStreamingGeneratedComponentClock W h v.depth))

end QuantitativeFollowup
