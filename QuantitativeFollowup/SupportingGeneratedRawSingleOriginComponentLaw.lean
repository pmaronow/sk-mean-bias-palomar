module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginTerminalPairs
public import QuantitativeFollowup.SupportingGeneratedObservedRawComponentLaw
public import QuantitativeFollowup.SupportingGeneratedOriginComponentReceiversDefinitions

@[expose] public section

/-! Actual raw chart record laws retain the full original observation
record and the true fresh marks. The terminal receiver is derived from
these mapped native probabilities for every finite terminal test. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

abbrev CavityGeneratedObservedRawComponentRecord (n : ℕ) (U : CavityGeneratedObservedRawComponent m) :=
  AnisotropicObservationState (n+1) × Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) U.tree

def cavityGeneratedObservedRawChartRecordProject
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) :
    CavityGeneratedObservedRawComponentRecord n (cavityGeneratedObservedRawChartComponent U γ k) →
      CavityGeneratedObservedRawComponentRecord n U × k.Mark (Configuration (n+1)) :=
  match γ with
  | .inl i => printedGeneratedVertexMarkedRecordProject k (cavityGeneratedObservedRawChartFork U i)
  | .inr (.inl i) => fun z=>
      let x := printedGeneratedVertexMarkedRecordProject k
        (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
          (cavityGeneratedObservedRawChartEdge U i)) z
      ((x.1.1,observationRefinementProject
        (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth) U.tree x.1.2),x.2)
  | .inr (.inr _) => printedGeneratedVertexMarkedRecordProject k (.root U.tree)

theorem measurable_cavityGeneratedObservedRawChartRecordProject
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) :
    Measurable (cavityGeneratedObservedRawChartRecordProject (n:=n) U γ k) := by
  rcases γ with i | (i | u)
  · exact measurable_printedGeneratedVertexMarkedRecordProject k _
  · have hp := measurable_printedGeneratedVertexMarkedRecordProject (n:=n) k
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
        (cavityGeneratedObservedRawChartEdge U i))
    have hr := measurable_observationRefinementProject (E:=AnisotropicObservationState (n+1))
      (S:=Configuration (n+1)) (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth) U.tree
    exact (hp.fst.fst.prodMk (hr.comp hp.fst.snd)).prodMk hp.snd
  · exact measurable_printedGeneratedVertexMarkedRecordProject k _

theorem cavityGeneratedObservedRawChartRecordProject_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hr : cavityGeneratedObservedRawChartCell U γ h r) :
    (anisotropicRecordedProfileTreeLaw D μ a
      ((cavityGeneratedObservedRawChartComponent U γ k).clock
        (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r)))
      (cavityGeneratedObservedRawChartComponent U γ k).tree).map
        (cavityGeneratedObservedRawChartRecordProject U γ k) =
      (printedGeneratedOriginKindProbability D μ a (U.clock h) U.tree
        (cavityGeneratedObservedRawChartOrigin U γ r) k :
          Measure (CavityGeneratedObservedRawComponentRecord n U × k.Mark (Configuration (n+1)))) := by
  rw [cavityGeneratedObservedRawChartComponent_clock U γ k h r hr]
  rcases γ with i | (i | u)
  · exact printedGeneratedVertexMarkedRecordProject_law D μ a _ _ _ k
  · let e := cavityGeneratedObservedRawChartEdge U i
    let v := nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e
    let post := Prod.map
      (Prod.map (id : AnisotropicObservationState (n+1) → AnisotropicObservationState (n+1))
        (observationRefinementProject (E:=AnisotropicObservationState (n+1))
          (S:=Configuration (n+1)) (nativeStreamingEdgeSubdivision e.depth) U.tree))
      (id : k.Mark (Configuration (n+1)) → k.Mark (Configuration (n+1)))
    have hpost : Measurable post :=
      (measurable_id.prodMap (measurable_observationRefinementProject _ U.tree)).prodMap measurable_id
    have hbase := measurable_printedGeneratedVertexMarkedRecordProject (n:=n) k v
    change (anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingEdgeSchedule (U.clock h) e.depth r)
      (finiteCascadeContinuationGraft k.continuation v)).map (post ∘ printedGeneratedVertexMarkedRecordProject k v) = _
    rw [←Measure.map_map hpost hbase,printedGeneratedVertexMarkedRecordProject_law]
    cases k <;> rfl
  · exact printedGeneratedVertexMarkedRecordProject_law D μ a _ _ _ k

theorem cavityGeneratedObservedRawChartTerminalProject_record
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind)
    (z : CavityGeneratedObservedRawComponentRecord n (cavityGeneratedObservedRawChartComponent U γ k)) :
    cavityGeneratedObservedRawChartTerminalProject U γ k
      (finiteCascadeRecordTerminalSpins (cavityGeneratedObservedRawChartComponent U γ k).tree z.2) =
      (finiteCascadeRecordTerminalSpins U.tree (cavityGeneratedObservedRawChartRecordProject U γ k z).1.2,
        (cavityGeneratedObservedRawChartRecordProject U γ k z).2) := by
  rcases γ with i | (i | u)
  · exact nativeStreamingGeneratedVertexTerminalProjection_record k _ z.2
  · change (observationRefinementTerminalProject _ U.tree rfl
      (nativeStreamingGeneratedVertexTerminalProjection k
        (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
          (cavityGeneratedObservedRawChartEdge U i)) (finiteCascadeRecordTerminalSpins _ z.2)).1,
      (nativeStreamingGeneratedVertexTerminalProjection k
        (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
          (cavityGeneratedObservedRawChartEdge U i)) (finiteCascadeRecordTerminalSpins _ z.2)).2) = _
    rw [nativeStreamingGeneratedVertexTerminalProjection_record,observationRefinementTerminalProject_record]
    rfl
  · exact nativeStreamingGeneratedVertexTerminalProjection_record k _ z.2

theorem cavityGeneratedObservedRawChart_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hr : cavityGeneratedObservedRawChartCell U γ h r)
    (G : CavityGeneratedObservedRawComponentTerminal n U × k.Mark (Configuration (n+1)) → ℝ) :
    (∫σ,G (cavityGeneratedObservedRawChartTerminalProject U γ k σ)
      ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a (cavityGeneratedObservedRawChartComponent U γ k)
        (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r))) =
      nativeStreamingTerminalMarkMoment
        (printedGeneratedOriginKindProbability D μ a (U.clock h) U.tree
          (cavityGeneratedObservedRawChartOrigin U γ r) k) G := by
  let V := cavityGeneratedObservedRawChartComponent U γ k
  let H : CavityGeneratedHistory Paper.Overlap (m+1) := Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r)
  let P := anisotropicRecordedProfileTreeLaw D μ a (V.clock H) V.tree
  let ψ : CavityGeneratedObservedRawComponentRecord n V → CavityGeneratedObservedRawComponentTerminal n V :=
    fun z=>finiteCascadeRecordTerminalSpins V.tree z.2
  have hψ : Measurable ψ := (measurable_finiteCascadeRecordTerminalSpins V.tree).comp measurable_snd
  have hmap := integral_map (μ:=P) hψ.aemeasurable
    (measurable_of_finite (fun σ : CavityGeneratedObservedRawComponentTerminal n V=>
      G (cavityGeneratedObservedRawChartTerminalProject U γ k σ))).aestronglyMeasurable
  let f : CavityGeneratedObservedRawComponentRecord n U × k.Mark (Configuration (n+1)) → ℝ :=
    fun z=>G (finiteCascadeRecordTerminalSpins U.tree z.1.2,z.2)
  have hf : Measurable f := (measurable_of_finite G).comp
    (((measurable_finiteCascadeRecordTerminalSpins U.tree).comp measurable_fst.snd).prodMk measurable_snd)
  have hp := measurable_cavityGeneratedObservedRawChartRecordProject (n:=n) U γ k
  have hI := integral_map (μ:=P) hp.aemeasurable hf.aestronglyMeasurable
  have hJ := congrArg (fun M : Measure (CavityGeneratedObservedRawComponentRecord n U ×
    k.Mark (Configuration (n+1)))=>∫z,f z ∂M)
    (cavityGeneratedObservedRawChartRecordProject_law D μ a U γ k h r hr)
  have hreceiver := hI.symm.trans hJ
  refine hmap.trans (Eq.trans ?_ hreceiver)
  apply integral_congr_ae
  exact .of_forall fun z=>congrArg G (cavityGeneratedObservedRawChartTerminalProject_record U γ k z)

theorem cavityGeneratedObservedRawChart_originalFresh_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell U γ h r)
    (F : CavityGeneratedObservedRawComponentTerminal n U → ℝ) (i : ObservationLeaf U.tree) :
    (∫σ,nativeStreamingOriginalFreshSpinTest U.tree F i
      (nativeStreamingOriginCommonClock (U.clock h) U.tree (.vertex (observationLeafVertex U.tree i))
        (cavityGeneratedObservedRawChartOrigin U γ r)) (cavityGeneratedObservedRawChartTerminalProject U γ .single σ)
      ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a (cavityGeneratedObservedRawChartComponent U γ .single)
        (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r))) =
      nativeStreamingPatternMoment D μ a (U.clock h) U.tree F
        (.originalFresh i (cavityGeneratedObservedRawChartOrigin U γ r)) :=
  cavityGeneratedObservedRawChart_terminal_receiver D μ a U γ .single h r hr _

theorem cavityGeneratedObservedRawChart_current_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell U γ h r)
    (F : CavityGeneratedObservedRawComponentTerminal n U → ℝ) :
    (∫σ,nativeStreamingDefectSpinTest U.tree F
      (nativeStreamingOriginLevel (U.clock h) (cavityGeneratedObservedRawChartOrigin U γ r))
      (cavityGeneratedObservedRawChartTerminalProject U γ .current σ)
      ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a (cavityGeneratedObservedRawChartComponent U γ .current)
        (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r))) =
      nativeStreamingPatternMoment D μ a (U.clock h) U.tree F
        (.current (cavityGeneratedObservedRawChartOrigin U γ r)) :=
  cavityGeneratedObservedRawChart_terminal_receiver D μ a U γ .current h r hr _

end QuantitativeFollowup
