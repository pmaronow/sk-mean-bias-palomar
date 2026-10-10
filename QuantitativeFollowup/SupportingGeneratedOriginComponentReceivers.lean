module
public import QuantitativeFollowup.SupportingGeneratedOriginComponentReceiversLaw

@[expose] public section

/-! The full-record projection is also an exact finite terminal test.  The
receiver identity retains every old terminal coordinate and the actual
single or independent current pair, at the original source origin. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def printedGeneratedOriginChartTerminalProject (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (k : NativeStreamingGeneratedVertexKind) :
    CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent U γ k) →
      CavityGeneratedComponentTerminal n U × k.Mark (Configuration (n+1)) :=
  match γ with
  | .inl i => nativeStreamingGeneratedVertexTerminalProjection k (printedGeneratedOriginChartFork U i)
  | .inr (.inl i) => fun σ =>
      let x := nativeStreamingGeneratedVertexTerminalProjection k
        (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i)) σ
      (nativeStreamingGeneratedEdgeTerminalProject U (printedGeneratedOriginChartEdge U i) x.1,x.2)
  | .inr (.inr _) => fun σ =>
      let x := nativeStreamingGeneratedVertexTerminalProjection k
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree)) σ
      (nativeStreamingGeneratedEndpointTerminalProject U x.1,x.2)

theorem printedGeneratedOriginChartTerminalProject_record
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind)
    (z : PrintedGeneratedComponentRecord n (printedGeneratedOriginChartComponent U γ k)) :
    printedGeneratedOriginChartTerminalProject U γ k
      (finiteCascadeRecordTerminalSpins (printedGeneratedOriginChartComponent U γ k).tree z.2) =
    (finiteCascadeRecordTerminalSpins U.tree
      (printedGeneratedOriginChartRecordProject U γ k z).1.2,
      (printedGeneratedOriginChartRecordProject U γ k z).2) := by
  rcases γ with i | (i | u)
  · exact nativeStreamingGeneratedVertexTerminalProjection_record k _ z.2
  · change (nativeStreamingGeneratedEdgeTerminalProject U (printedGeneratedOriginChartEdge U i)
      (nativeStreamingGeneratedVertexTerminalProjection k
        (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i))
          (finiteCascadeRecordTerminalSpins _ z.2)).1,
      (nativeStreamingGeneratedVertexTerminalProjection k
        (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i))
          (finiteCascadeRecordTerminalSpins _ z.2)).2) = _
    rw [nativeStreamingGeneratedVertexTerminalProjection_record,
      nativeStreamingGeneratedEdgeTerminalProject_record]
    rfl
  · change (nativeStreamingGeneratedEndpointTerminalProject U
      (nativeStreamingGeneratedVertexTerminalProjection k
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (finiteCascadeRecordTerminalSpins _ z.2)).1,
      (nativeStreamingGeneratedVertexTerminalProjection k
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (finiteCascadeRecordTerminalSpins _ z.2)).2) = _
    rw [nativeStreamingGeneratedVertexTerminalProjection_record,
      nativeStreamingGeneratedEndpointTerminalProject_record]
    rfl

theorem printedGeneratedOriginChart_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (G : CavityGeneratedComponentTerminal n U × k.Mark (Configuration (n+1)) → ℝ) :
    (∫ σ, G (printedGeneratedOriginChartTerminalProject U γ k σ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a (printedGeneratedOriginChartComponent U γ k)
        (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))) =
      nativeStreamingTerminalMarkMoment
        (printedGeneratedOriginKindProbability D μ a (nativeStreamingGeneratedComponentClock U h)
          U.tree (printedGeneratedOriginChartOrigin U γ r) k) G := by
  let V := printedGeneratedOriginChartComponent U γ k
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (printedGeneratedOriginChartClock U γ h r)
  let ψ : PrintedGeneratedComponentRecord n V → CavityGeneratedComponentTerminal n V :=
    fun z => finiteCascadeRecordTerminalSpins V.tree z.2
  have hψ : Measurable ψ := by
    simpa only [ψ,Function.comp_def] using
      (measurable_finiteCascadeRecordTerminalSpins V.tree).comp measurable_snd
  have hmap := integral_map (μ:=printedGeneratedComponentLaw D μ a V H) hψ.aemeasurable
    (measurable_of_finite (fun σ : CavityGeneratedComponentTerminal n V =>
      G (printedGeneratedOriginChartTerminalProject U γ k σ))).aestronglyMeasurable
  have hp := printedGeneratedOriginChartRecordProject_measurePreserving D μ a U γ k h r hh hr
  let f : PrintedGeneratedComponentRecord n U × k.Mark (Configuration (n+1)) → ℝ :=
    fun z => G (finiteCascadeRecordTerminalSpins U.tree z.1.2,z.2)
  have hf : Measurable f := (measurable_of_finite G).comp
    (((measurable_finiteCascadeRecordTerminalSpins U.tree).comp measurable_fst.snd).prodMk
      measurable_snd)
  have hI := integral_map (μ:=printedGeneratedComponentLaw D μ a V H)
    hp.measurable.aemeasurable hf.aestronglyMeasurable
  have hJ := congrArg
    (fun M : Measure (PrintedGeneratedComponentRecord n U × k.Mark (Configuration (n+1))) =>
      ∫ z, f z ∂M) hp.map_eq
  have hreceiver := hI.symm.trans hJ
  refine hmap.trans ?_
  refine Eq.trans ?_ hreceiver
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G (printedGeneratedOriginChartTerminalProject_record U γ k z)

theorem printedGeneratedOriginChart_originalFresh_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (F : CavityGeneratedComponentTerminal n U → ℝ) (i : ObservationLeaf U.tree) :
    (∫ σ, nativeStreamingOriginalFreshSpinTest U.tree F i
      (nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (.vertex (observationLeafVertex U.tree i)) (printedGeneratedOriginChartOrigin U γ r))
      (printedGeneratedOriginChartTerminalProject U γ .single σ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a (printedGeneratedOriginChartComponent U γ .single)
        (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))) =
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree F (.originalFresh i (printedGeneratedOriginChartOrigin U γ r)) :=
  printedGeneratedOriginChart_terminal_receiver D μ a U γ .single h r hh hr _

theorem printedGeneratedOriginChart_current_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (F : CavityGeneratedComponentTerminal n U → ℝ) :
    (∫ σ, nativeStreamingDefectSpinTest U.tree F
      (nativeStreamingOriginLevel (nativeStreamingGeneratedComponentClock U h)
        (printedGeneratedOriginChartOrigin U γ r))
      (printedGeneratedOriginChartTerminalProject U γ .current σ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a (printedGeneratedOriginChartComponent U γ .current)
        (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))) =
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree F (.current (printedGeneratedOriginChartOrigin U γ r)) :=
  printedGeneratedOriginChart_terminal_receiver D μ a U γ .current h r hh hr _

end QuantitativeFollowup
