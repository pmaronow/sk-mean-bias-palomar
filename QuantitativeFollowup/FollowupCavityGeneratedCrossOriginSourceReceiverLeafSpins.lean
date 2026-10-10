module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverLeafGeometry
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverTerminalProjection

@[expose] public section

/-! Pointwise identification of the actual fresh leaf spins and pair defect.
This is a structural projection identity, with no law identity as a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

private theorem recordFreshPair {E S : Type} {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    (nativeStreamingGeneratedCrossVertexTerminalProjection v w
      (finiteCascadeRecordTerminalSpins _ z)).2 =
      (observationLeafSpin _ (finiteCascadeLinearCrossFirstLeaf v w) z,
        observationLeafSpin _ (finiteCascadeLinearCrossSecondLeaf v w) z) :=
  Prod.ext (nativeStreamingGeneratedCrossVertexTerminalProjection_first_leaf v w z)
    (nativeStreamingGeneratedCrossVertexTerminalProjection_second_leaf v w z)

theorem printedGeneratedOriginCrossChart_fresh_spins {E S : Type}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (z : E × Records E S (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) :
    (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k
      (finiteCascadeRecordTerminalSpins _ z.2)).2 =
      (observationLeafSpin _ (printedGeneratedOriginCrossChartFirstLeaf U γ₁ γ₂ k) z.2,
        observationLeafSpin _ (printedGeneratedOriginCrossChartSecondLeaf U γ₁ γ₂ k) z.2) := by
  rcases γ₁ with i | (i | u) <;> rcases γ₂ with j | (j | v)
  · exact recordFreshPair _ _ z.2
  · exact congrArg Prod.swap (recordFreshPair _ _ z.2)
  · exact recordFreshPair _ _ z.2
  · exact recordFreshPair _ _ z.2
  · exact recordFreshPair _ _ z.2
  · exact recordFreshPair _ _ z.2
  · exact recordFreshPair _ _ z.2
  · exact congrArg Prod.swap (recordFreshPair _ _ z.2)
  · exact recordFreshPair _ _ z.2

theorem printedGeneratedOriginCrossChart_fresh_spins_terminal {S : Type}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : TerminalSpins S (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) :
    (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k σ).2 =
      (observationTerminalSpin _ (printedGeneratedOriginCrossChartFirstLeaf U γ₁ γ₂ k) σ,
        observationTerminalSpin _ (printedGeneratedOriginCrossChartSecondLeaf U γ₁ γ₂ k) σ) := by
  have H := printedGeneratedOriginCrossChart_fresh_spins U γ₁ γ₂ k
    ((),observationUnitRecord (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree σ)
  simpa only [←observationTerminalSpin_record, finiteCascadeRecordTerminalSpins_unit] using H

theorem printedGeneratedOriginCrossChart_literal_defect {E : Type}
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r) (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l)
    (z : E × Records E (Configuration (n+1))
      (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) :
    cavitySpinOverlapDefect n
      (nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (printedGeneratedOriginCrossChartOrigin U γ₁ r) (printedGeneratedOriginCrossChartOrigin U γ₂ l))
      (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k
        (finiteCascadeRecordTerminalSpins _ z.2)).2.1
      (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k
        (finiteCascadeRecordTerminalSpins _ z.2)).2.2 =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k)
        (printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l)
        (observationCommonLevel _ (printedGeneratedOriginCrossChartFirstLeaf U γ₁ γ₂ k)
          (printedGeneratedOriginCrossChartSecondLeaf U γ₁ γ₂ k)))
      (observationLeafSpin _ (printedGeneratedOriginCrossChartFirstLeaf U γ₁ γ₂ k) z.2)
      (observationLeafSpin _ (printedGeneratedOriginCrossChartSecondLeaf U γ₁ γ₂ k) z.2) := by
  rw [printedGeneratedOriginCrossChart_fresh_common_clock U γ₁ γ₂ k h r l hh hr hl hk]
  have hp := printedGeneratedOriginCrossChart_fresh_spins U γ₁ γ₂ k z
  exact congrArg₂ (cavitySpinOverlapDefect n _)
    (congrArg Prod.fst hp) (congrArg Prod.snd hp)

theorem printedGeneratedOriginCrossChart_literal_terminal_defect
    (U : CavityGeneratedConstructedComponent m) (γ₁ γ₂ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ₁ h r) (hl : printedGeneratedOriginChartCell U γ₂ h l)
    (hk : printedGeneratedOriginCrossChartHolds U γ₁ γ₂ k r l)
    (σ : TerminalSpins (Configuration (n+1)) (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k).tree) :
    cavitySpinOverlapDefect n
      (nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (printedGeneratedOriginCrossChartOrigin U γ₁ r) (printedGeneratedOriginCrossChartOrigin U γ₂ l))
      (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k σ).2.1
      (printedGeneratedOriginCrossChartTerminalProjection U γ₁ γ₂ k σ).2.2 =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginCrossChartComponent U γ₁ γ₂ k)
        (printedGeneratedOriginCrossChartAppend U γ₁ γ₂ h r l)
        (observationCommonLevel _ (printedGeneratedOriginCrossChartFirstLeaf U γ₁ γ₂ k)
          (printedGeneratedOriginCrossChartSecondLeaf U γ₁ γ₂ k)))
      (observationTerminalSpin _ (printedGeneratedOriginCrossChartFirstLeaf U γ₁ γ₂ k) σ)
      (observationTerminalSpin _ (printedGeneratedOriginCrossChartSecondLeaf U γ₁ γ₂ k) σ) := by
  rw [printedGeneratedOriginCrossChart_fresh_common_clock U γ₁ γ₂ k h r l hh hr hl hk]
  have hp := printedGeneratedOriginCrossChart_fresh_spins_terminal U γ₁ γ₂ k σ
  exact congrArg₂ (cavitySpinOverlapDefect n _)
    (congrArg Prod.fst hp) (congrArg Prod.snd hp)

end QuantitativeFollowup
