module
public import QuantitativeFollowup.SupportingGeneratedObservedRawComponentLaw

@[expose] public section

/-! Genuine replacement of one actual raw component preserves the joint
terminal distribution of every untouched component. Leaf casts transport
the complete old observable and its physical overlap tags. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {m n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedObservedRawComponentLeafCast
    (U V : CavityGeneratedObservedRawComponent m) (he : U=V)
    (i : ObservationLeaf V.tree) : ObservationLeaf U.tree :=
  cast (congrArg (fun K : CavityGeneratedObservedRawComponent m=>ObservationLeaf K.tree) he.symm) i

theorem cavityGeneratedObservedRawComponentLeafCast_commonLevel
    (U V : CavityGeneratedObservedRawComponent m) (he : U=V)
    (i k : ObservationLeaf V.tree) :
    observationCommonLevel U.tree (cavityGeneratedObservedRawComponentLeafCast U V he i)
      (cavityGeneratedObservedRawComponentLeafCast U V he k) = observationCommonLevel V.tree i k := by
  cases he
  rfl

theorem cavityGeneratedObservedRawComponentLeafCast_spin
    (U V : CavityGeneratedObservedRawComponent m) (he : U=V)
    (i : ObservationLeaf V.tree) (σ : CavityGeneratedObservedRawComponentTerminal n U) :
    observationTerminalSpin U.tree (cavityGeneratedObservedRawComponentLeafCast U V he i) σ =
      observationTerminalSpin V.tree i (cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U V he σ) := by
  cases he
  rfl

def cavityGeneratedObservedRawForestReplacementOtherEquiv (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedObservedRawComponent m)
    (i : Fin W.componentCount) (hi : i ≠ c) :=
  cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) (W.component i)
    ((cavityGeneratedObservedRawForestReplaceComponent W c U).component i)
    (cavityGeneratedObservedRawForestReplaceComponent_other W c U i hi).symm

def cavityGeneratedObservedRawForestReplacementSelectedEquiv (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedObservedRawComponent m) :=
  cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U
    ((cavityGeneratedObservedRawForestReplaceComponent W c U).component c)
    (cavityGeneratedObservedRawForestReplaceComponent_same W c U).symm

def cavityGeneratedObservedRawForestReplacementTerminal (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedObservedRawComponent m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
    (τ : CavityGeneratedObservedRawComponentTerminal n U) :
    CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawForestReplaceComponent W c U).depth
      (cavityGeneratedObservedRawForestReplaceComponent W c U).tree :=
  finiteProbabilityCoordinateReplacement c (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) W c U)
    (σ, cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) W c U τ)

theorem integral_cavityGeneratedObservedRawForest_component_replacement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (U : CavityGeneratedObservedRawComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (F : CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawForestReplaceComponent W c U).depth
      (cavityGeneratedObservedRawForestReplaceComponent W c U).tree → ℝ) :
    (∫ σ, ∫ τ, F (cavityGeneratedObservedRawForestReplacementTerminal W c U σ τ)
      ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a U h
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock h) : Measure _)) =
      ∫ σ, F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedObservedRawForestReplaceComponent W c U).depth
        (cavityGeneratedObservedRawForestReplaceComponent W c U).tree
        ((cavityGeneratedObservedRawForestReplaceComponent W c U).clock h) : Measure _) := by
  let V := cavityGeneratedObservedRawForestReplaceComponent W c U
  let M := fun i => cavityGeneratedObservedRawComponentTerminalMeasure D μ a (W.component i) h
  let N := fun i => cavityGeneratedObservedRawComponentTerminalMeasure D μ a (V.component i) h
  let e := cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) W c U
  have he (i : Fin W.componentCount) (hi : i ≠ c) : MeasurePreserving (e i hi) (M i) (N i) :=
    cavityGeneratedObservedRawComponentTerminalCastEquiv_measurePreserving D μ a _ _ _ h
  have hF : Integrable F (Measure.pi N) := by
    simpa only [integrableOn_univ] using
      (IntegrableOn.of_finite (μ:=Measure.pi N) (f:=F) (s:=univ) Set.finite_univ)
  have hp := integral_finiteProbabilityCoordinateReplacement M N c e he F hF
  rw [cavityGeneratedObservedRawNativeForestTerminalMeasure_eq_components,
    cavityGeneratedObservedRawNativeForestTerminalMeasure_eq_components]
  change (∫ σ, ∫ τ, F (cavityGeneratedObservedRawForestReplacementTerminal W c U σ τ)
    ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a U h ∂Measure.pi M) = ∫ σ, F σ ∂Measure.pi N
  refine Eq.trans ?_ hp
  apply integral_congr_ae
  refine .of_forall fun σ => ?_
  have hc := cavityGeneratedObservedRawComponentTerminalCastEquiv_measurePreserving D μ a U
    (V.component c) (cavityGeneratedObservedRawForestReplaceComponent_same W c U).symm h
  exact hc.integral_comp' (fun τ => F (finiteProbabilityCoordinateReplacement c e (σ,τ)))

end QuantitativeFollowup
