module
public import FourPapersCommon.FiniteProbabilityCoordinateReplacement
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties
public import QuantitativeFollowup.FollowupCavityGeneratedForestContinuity

@[expose] public section

/-! A concrete component replacement retains the joint terminal law of
all untouched trees. Its redundant old selected coordinate has total
probability one; the terminal test is never factored into components. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {m n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedObservedRawForestReplaceComponent_same (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedObservedRawComponent m) :
    (cavityGeneratedObservedRawForestReplaceComponent W c U).component c = U := by
  classical
  change Function.update W.component c U c = U
  exact Function.update_self _ _ _

theorem cavityGeneratedObservedRawForestReplaceComponent_other (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedObservedRawComponent m)
    (i : Fin W.componentCount) (hi : i ≠ c) :
    (cavityGeneratedObservedRawForestReplaceComponent W c U).component i = W.component i := by
  classical
  change Function.update W.component c U i = W.component i
  exact Function.update_of_ne hi _ _

abbrev CavityGeneratedObservedRawComponentTerminal (n : ℕ) (U : CavityGeneratedObservedRawComponent m) :=
  TerminalSpins (Configuration (n+1)) U.tree

def cavityGeneratedObservedRawComponentTerminalMeasure (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) : Measure (CavityGeneratedObservedRawComponentTerminal n U) :=
  (anisotropicRecordedProfileTreeLaw D μ a (U.clock h) U.tree).map
    (fun z => finiteCascadeRecordTerminalSpins U.tree z.2)

instance cavityGeneratedObservedRawComponentTerminalMeasure_probability (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (U : CavityGeneratedObservedRawComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    IsProbabilityMeasure (cavityGeneratedObservedRawComponentTerminalMeasure D μ a U h) := by
  unfold cavityGeneratedObservedRawComponentTerminalMeasure
  infer_instance

theorem cavityGeneratedObservedRawNativeForestTerminalMeasure_eq_components
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (h : CavityGeneratedHistory Paper.Overlap m) :
    (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) =
      Measure.pi (fun i => cavityGeneratedObservedRawComponentTerminalMeasure D μ a (W.component i) h) := by
  change (cavityGeneratedNativeForestLaw D μ a W.depth W.tree
    (W.clock h)).map (cavityGeneratedForestTerminalProjection W.depth W.tree) = _
  unfold cavityGeneratedNativeForestLaw
  exact Measure.pi_map_pi (fun i =>
    ((measurable_finiteCascadeRecordTerminalSpins (W.tree i)).comp measurable_snd).aemeasurable)

def cavityGeneratedObservedRawComponentTerminalCastEquiv
    (U U' : CavityGeneratedObservedRawComponent m) (he : U = U') :
    CavityGeneratedObservedRawComponentTerminal n U ≃ᵐ CavityGeneratedObservedRawComponentTerminal n U' := by
  cases he
  exact MeasurableEquiv.refl _

theorem cavityGeneratedObservedRawComponentTerminalCastEquiv_measurePreserving
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U U' : CavityGeneratedObservedRawComponent m) (he : U = U')
    (h : CavityGeneratedHistory Paper.Overlap m) :
    MeasurePreserving (cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U U' he)
      (cavityGeneratedObservedRawComponentTerminalMeasure D μ a U h)
      (cavityGeneratedObservedRawComponentTerminalMeasure D μ a U' h) := by
  cases he
  exact ⟨measurable_id, Measure.map_id⟩

end QuantitativeFollowup
