module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverTerminalProjection
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverChartLaw

@[expose] public section

/-! The actual chart record law transports every finite terminal test,
including the genuine old-test times fresh-pair defect. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem printedGeneratedOriginCrossChart_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r) (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l)
    (G : CavityGeneratedComponentTerminal n U × (Configuration (n+1)×Configuration (n+1)) → ℝ) :
    (∫σ,G (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k σ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k)
        (printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l)) =
      nativeStreamingTerminalMarkMoment
        (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h) U.tree
          (printedGeneratedOriginCrossChartOrigin U γ₁ r) (printedGeneratedOriginCrossChartOrigin U γ₂ l)) G := by
  let V := printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k
  let H := printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l
  let ψ : PrintedGeneratedComponentRecord n V → CavityGeneratedComponentTerminal n V :=
    fun z=>finiteCascadeRecordTerminalSpins V.tree z.2
  have hψ : Measurable ψ := (measurable_finiteCascadeRecordTerminalSpins V.tree).comp measurable_snd
  have hmap := integral_map (μ:=printedGeneratedComponentLaw D μ a V H) hψ.aemeasurable
    (measurable_of_finite (fun σ=>G (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k σ))).aestronglyMeasurable
  let f : PrintedGeneratedComponentRecord n U × (Configuration (n+1)×Configuration (n+1)) → ℝ :=
    fun z=>G (finiteCascadeRecordTerminalSpins U.tree z.1.2,z.2)
  have hf : Measurable f := (measurable_of_finite G).comp
    (((measurable_finiteCascadeRecordTerminalSpins U.tree).comp measurable_fst.snd).prodMk measurable_snd)
  have hp : (printedGeneratedComponentLaw D μ a V H).map
      (printedGeneratedOriginCrossChartRecordProjection U γ₁ γ₂ k) =
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h) U.tree
        (printedGeneratedOriginCrossChartOrigin U γ₁ r) (printedGeneratedOriginCrossChartOrigin U γ₂ l) : Measure _) := by
    simpa only [V,H,printedGeneratedComponentLaw,printedGeneratedComponentClock_eq_native] using
      printedGeneratedOriginCrossChart_full_record_law D μ a U γ₁ γ₂ k h r l hh hr hl hk
  have hI := integral_map (μ:=printedGeneratedComponentLaw D μ a V H)
    (measurable_printedGeneratedOriginCrossChartRecordProjection U γ₁ γ₂ k).aemeasurable hf.aestronglyMeasurable
  have hJ := congrArg (fun Q : Measure (PrintedGeneratedComponentRecord n U ×
    (Configuration (n+1)×Configuration (n+1)))=>∫z,f z ∂Q) hp
  refine hmap.trans (Eq.trans ?_ (hI.symm.trans hJ))
  apply integral_congr_ae
  exact .of_forall fun z=>congrArg G (printedGeneratedOriginCrossChartTerminalProjection_record U γ₁ γ₂ k z)

theorem printedGeneratedOriginCrossChart_cross_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r) (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l)
    (F : CavityGeneratedComponentTerminal n U → ℝ) :
    (∫σ,nativeStreamingDefectSpinTest U.tree F
      (nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (printedGeneratedOriginCrossChartOrigin U γ₁ r) (printedGeneratedOriginCrossChartOrigin U γ₂ l))
      (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k σ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k)
        (printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l)) =
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock U h) U.tree F
        (.cross (printedGeneratedOriginCrossChartOrigin U γ₁ r) (printedGeneratedOriginCrossChartOrigin U γ₂ l)) :=
  printedGeneratedOriginCrossChart_terminal_receiver D μ a U γ₁ γ₂ k h r l hh hr hl hk _

end QuantitativeFollowup
