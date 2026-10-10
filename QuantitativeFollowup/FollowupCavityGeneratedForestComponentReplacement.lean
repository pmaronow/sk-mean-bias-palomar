module
public import FourPapersCommon.FiniteProbabilityCoordinateReplacement
public import QuantitativeFollowup.SupportingGeneratedAppendBridge
public import QuantitativeFollowup.FollowupCavityGeneratedRetainedVertexGraft

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

def cavityGeneratedForestReplaceComponent (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedConstructedComponent m) :
    CavityGeneratedConstructedForest m :=
  cavityGeneratedForestOfComponents (Function.update W.component c U)

theorem cavityGeneratedForestReplaceComponent_same (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedConstructedComponent m) :
    (cavityGeneratedForestReplaceComponent W c U).component c = U := by
  classical
  change Function.update W.component c U c = U
  exact Function.update_self _ _ _

theorem cavityGeneratedForestReplaceComponent_other (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedConstructedComponent m)
    (i : Fin W.componentCount) (hi : i ≠ c) :
    (cavityGeneratedForestReplaceComponent W c U).component i = W.component i := by
  classical
  change Function.update W.component c U i = W.component i
  exact Function.update_of_ne hi _ _

abbrev CavityGeneratedComponentTerminal (n : ℕ) (U : CavityGeneratedConstructedComponent m) :=
  TerminalSpins (Configuration (n+1)) U.tree

def cavityGeneratedComponentTerminalMeasure (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (U : CavityGeneratedConstructedComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) : Measure (CavityGeneratedComponentTerminal n U) :=
  (printedGeneratedComponentLaw D μ a U h).map
    (fun z => finiteCascadeRecordTerminalSpins U.tree z.2)

instance cavityGeneratedComponentTerminalMeasure_probability (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (U : CavityGeneratedConstructedComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    IsProbabilityMeasure (cavityGeneratedComponentTerminalMeasure D μ a U h) := by
  unfold cavityGeneratedComponentTerminalMeasure
  infer_instance

theorem cavityGeneratedNativeForestTerminalMeasure_eq_components
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (h : CavityGeneratedHistory Paper.Overlap m) :
    (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clockTemplate.clock h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) =
      Measure.pi (fun i => cavityGeneratedComponentTerminalMeasure D μ a (W.component i) h) := by
  change (cavityGeneratedNativeForestLaw D μ a W.depth W.tree
    (W.clockTemplate.clock h)).map (cavityGeneratedForestTerminalProjection W.depth W.tree) = _
  rw [printedGeneratedForestLaw_eq_components]
  exact Measure.pi_map_pi (fun i =>
    ((measurable_finiteCascadeRecordTerminalSpins (W.tree i)).comp measurable_snd).aemeasurable)

def cavityGeneratedComponentTerminalCastEquiv
    (U U' : CavityGeneratedConstructedComponent m) (he : U = U') :
    CavityGeneratedComponentTerminal n U ≃ᵐ CavityGeneratedComponentTerminal n U' := by
  cases he
  exact MeasurableEquiv.refl _

theorem cavityGeneratedComponentTerminalCastEquiv_measurePreserving
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U U' : CavityGeneratedConstructedComponent m) (he : U = U')
    (h : CavityGeneratedHistory Paper.Overlap m) :
    MeasurePreserving (cavityGeneratedComponentTerminalCastEquiv (n:=n) U U' he)
      (cavityGeneratedComponentTerminalMeasure D μ a U h)
      (cavityGeneratedComponentTerminalMeasure D μ a U' h) := by
  cases he
  exact ⟨measurable_id, Measure.map_id⟩

def cavityGeneratedForestReplacementOtherEquiv (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedConstructedComponent m)
    (i : Fin W.componentCount) (hi : i ≠ c) :=
  cavityGeneratedComponentTerminalCastEquiv (n:=n) (W.component i)
    ((cavityGeneratedForestReplaceComponent W c U).component i)
    (cavityGeneratedForestReplaceComponent_other W c U i hi).symm

def cavityGeneratedForestReplacementSelectedEquiv (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedConstructedComponent m) :=
  cavityGeneratedComponentTerminalCastEquiv (n:=n) U
    ((cavityGeneratedForestReplaceComponent W c U).component c)
    (cavityGeneratedForestReplaceComponent_same W c U).symm

def cavityGeneratedForestReplacementTerminal (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (U : CavityGeneratedConstructedComponent m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
    (τ : CavityGeneratedComponentTerminal n U) :
    CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedForestReplaceComponent W c U).depth
      (cavityGeneratedForestReplaceComponent W c U).tree :=
  finiteProbabilityCoordinateReplacement c (cavityGeneratedForestReplacementOtherEquiv (n:=n) W c U)
    (σ, cavityGeneratedForestReplacementSelectedEquiv (n:=n) W c U τ)

theorem integral_cavityGeneratedForest_component_replacement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (F : CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedForestReplaceComponent W c U).depth
      (cavityGeneratedForestReplaceComponent W c U).tree → ℝ) :
    (∫ σ, ∫ τ, F (cavityGeneratedForestReplacementTerminal W c U σ τ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a U h
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure _)) =
      ∫ σ, F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedForestReplaceComponent W c U).depth
        (cavityGeneratedForestReplaceComponent W c U).tree
        ((cavityGeneratedForestReplaceComponent W c U).clockTemplate.clock h) : Measure _) := by
  let V := cavityGeneratedForestReplaceComponent W c U
  let M := fun i => cavityGeneratedComponentTerminalMeasure D μ a (W.component i) h
  let N := fun i => cavityGeneratedComponentTerminalMeasure D μ a (V.component i) h
  let e := cavityGeneratedForestReplacementOtherEquiv (n:=n) W c U
  have he (i : Fin W.componentCount) (hi : i ≠ c) : MeasurePreserving (e i hi) (M i) (N i) :=
    cavityGeneratedComponentTerminalCastEquiv_measurePreserving D μ a _ _ _ h
  have hF : Integrable F (Measure.pi N) := by
    simpa only [integrableOn_univ] using
      (IntegrableOn.of_finite (μ:=Measure.pi N) (f:=F) (s:=univ) Set.finite_univ)
  have hp := integral_finiteProbabilityCoordinateReplacement M N c e he F hF
  rw [cavityGeneratedNativeForestTerminalMeasure_eq_components,
    cavityGeneratedNativeForestTerminalMeasure_eq_components]
  change (∫ σ, ∫ τ, F (cavityGeneratedForestReplacementTerminal W c U σ τ)
    ∂cavityGeneratedComponentTerminalMeasure D μ a U h ∂Measure.pi M) = ∫ σ, F σ ∂Measure.pi N
  refine Eq.trans ?_ hp
  apply integral_congr_ae
  refine .of_forall fun σ => ?_
  have hc := cavityGeneratedComponentTerminalCastEquiv_measurePreserving D μ a U
    (V.component c) (cavityGeneratedForestReplaceComponent_same W c U).symm h
  exact hc.integral_comp' (fun τ => F (finiteProbabilityCoordinateReplacement c e (σ,τ)))

end QuantitativeFollowup
