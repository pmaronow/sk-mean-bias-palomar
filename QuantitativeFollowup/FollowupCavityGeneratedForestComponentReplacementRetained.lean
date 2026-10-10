module
public import QuantitativeFollowup.FollowupCavityGeneratedForestComponentReplacement

@[expose] public section

/-! The single/current continuation receiver for one component is the
expectation of the genuine replaced forest. All old terminal coordinates
remain in the arbitrary joint test, including the selected old tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {m n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem printedGeneratedComponentClock_eq_native (U : CavityGeneratedConstructedComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    printedGeneratedComponentClock U h = nativeStreamingGeneratedComponentClock U h := by
  apply congrArg cavityGeneratedClippedClock
  funext j
  change (if hj : j ≤ U.depth then (U.label ⟨j,by omega⟩).value h else 0) =
    (cavityGeneratedFiniteClockLabels U.label j).value h
  by_cases hj : j ≤ U.depth
  · simp only [cavityGeneratedFiniteClockLabels, dif_pos hj]
  · simp only [cavityGeneratedFiniteClockLabels, dif_neg hj, CavityGeneratedClockLabel.value]

def cavityGeneratedForestRetainedVertexReplacement (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (v : FiniteCascadeRecordVertex (W.tree c))
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels (W.label c) v.depth = .mark b)
    (k : NativeStreamingGeneratedVertexKind) : CavityGeneratedConstructedForest m :=
  cavityGeneratedForestReplaceComponent W c
    (nativeStreamingGeneratedRetainedVertexComponent (W.component c) v b hb k)

def cavityGeneratedForestRetainedVertexProjection (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (v : FiniteCascadeRecordVertex (W.tree c))
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels (W.label c) v.depth = .mark b)
    (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedForestRetainedVertexReplacement W c v b hb k).depth
      (cavityGeneratedForestRetainedVertexReplacement W c v b hb k).tree) :
    CavityGeneratedComponentTerminal n (W.component c) × k.Mark (Configuration (n+1)) :=
  nativeStreamingGeneratedVertexTerminalProjection k v
    ((cavityGeneratedForestReplacementSelectedEquiv (n:=n) W c
      (nativeStreamingGeneratedRetainedVertexComponent (W.component c) v b hb k)).symm (σ c))

def cavityGeneratedForestRetainedVertexOriginal (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (v : FiniteCascadeRecordVertex (W.tree c))
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels (W.label c) v.depth = .mark b)
    (k : NativeStreamingGeneratedVertexKind)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedForestRetainedVertexReplacement W c v b hb k).depth
      (cavityGeneratedForestRetainedVertexReplacement W c v b hb k).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree := by
  classical
  exact fun i => if hi : i = c then
    cast (congrArg (fun j => CavityGeneratedComponentTerminal n (W.component j)) hi.symm)
      (cavityGeneratedForestRetainedVertexProjection W c v b hb k σ).1
    else (cavityGeneratedForestReplacementOtherEquiv (n:=n) W c
      (nativeStreamingGeneratedRetainedVertexComponent (W.component c) v b hb k) i hi).symm (σ i)

def cavityGeneratedForestRetainedVertexTerminalTest (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (v : FiniteCascadeRecordVertex (W.tree c))
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels (W.label c) v.depth = .mark b)
    (k : NativeStreamingGeneratedVertexKind)
    (G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      k.Mark (Configuration (n+1)) → ℝ)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedForestRetainedVertexReplacement W c v b hb k).depth
      (cavityGeneratedForestRetainedVertexReplacement W c v b hb k).tree) : ℝ :=
  G (cavityGeneratedForestRetainedVertexOriginal W c v b hb k σ,
    (cavityGeneratedForestRetainedVertexProjection W c v b hb k σ).2)

theorem cavityGeneratedForestRetainedVertexTerminalTest_replacement
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (v : FiniteCascadeRecordVertex (W.tree c)) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels (W.label c) v.depth = .mark b)
    (k : NativeStreamingGeneratedVertexKind)
    (G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      k.Mark (Configuration (n+1)) → ℝ)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
    (τ : TerminalSpins (Configuration (n+1))
      (finiteCascadeContinuationGraft k.continuation v)) :
    cavityGeneratedForestRetainedVertexTerminalTest W c v b hb k G
      (cavityGeneratedForestReplacementTerminal W c
        (nativeStreamingGeneratedRetainedVertexComponent (W.component c) v b hb k) σ τ) =
      G (Function.update σ c (nativeStreamingGeneratedVertexTerminalProjection k v τ).1,
        (nativeStreamingGeneratedVertexTerminalProjection k v τ).2) := by
  classical
  let U := nativeStreamingGeneratedRetainedVertexComponent (W.component c) v b hb k
  let y := cavityGeneratedForestReplacementTerminal W c U σ τ
  have hp : cavityGeneratedForestRetainedVertexProjection W c v b hb k y =
      nativeStreamingGeneratedVertexTerminalProjection k v τ := by
    unfold cavityGeneratedForestRetainedVertexProjection
    change nativeStreamingGeneratedVertexTerminalProjection k v
      ((cavityGeneratedForestReplacementSelectedEquiv (n:=n) W c U).symm
        (finiteProbabilityCoordinateReplacement c
          (cavityGeneratedForestReplacementOtherEquiv (n:=n) W c U)
          (σ,cavityGeneratedForestReplacementSelectedEquiv (n:=n) W c U τ) c)) = _
    rw [finiteProbabilityCoordinateReplacement_same, MeasurableEquiv.symm_apply_apply]
  have ho : cavityGeneratedForestRetainedVertexOriginal W c v b hb k y =
      Function.update σ c (nativeStreamingGeneratedVertexTerminalProjection k v τ).1 := by
    funext i
    by_cases hi : i = c
    · subst i
      simp [cavityGeneratedForestRetainedVertexOriginal, hp]
    · simp only [cavityGeneratedForestRetainedVertexOriginal, dif_neg hi,
        Function.update_of_ne hi, y, U, cavityGeneratedForestReplacementTerminal,
        finiteProbabilityCoordinateReplacement_other c _ _ i hi]
      exact (cavityGeneratedForestReplacementOtherEquiv (n:=n) W c U i hi).symm_apply_apply (σ i)
  change G (cavityGeneratedForestRetainedVertexOriginal W c v b hb k y,
    (cavityGeneratedForestRetainedVertexProjection W c v b hb k y).2) = _
  rw [ho, hp]

theorem cavityGeneratedComponentTerminalMeasure_retained_vertex_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (G : CavityGeneratedComponentTerminal n W × k.Mark (Configuration (n+1)) → ℝ) :
    (∫ τ, G (nativeStreamingGeneratedVertexTerminalProjection k v τ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a
        (nativeStreamingGeneratedRetainedVertexComponent W v b hb k) h) =
      nativeStreamingGeneratedVertexMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree v k G := by
  let U := nativeStreamingGeneratedRetainedVertexComponent W v b hb k
  let ψ : PrintedGeneratedComponentRecord n U → CavityGeneratedComponentTerminal n U :=
    fun z => finiteCascadeRecordTerminalSpins U.tree z.2
  have hψ : Measurable ψ := by
    simpa only [ψ, Function.comp_def] using
      (measurable_finiteCascadeRecordTerminalSpins U.tree).comp measurable_snd
  have H := integral_map (μ:=printedGeneratedComponentLaw D μ a U h) hψ.aemeasurable
    (measurable_of_finite (fun τ : CavityGeneratedComponentTerminal n U =>
      G (nativeStreamingGeneratedVertexTerminalProjection k v τ))).aestronglyMeasurable
  refine H.trans ?_
  change (∫ z, G (nativeStreamingGeneratedVertexTerminalProjection k v
    (finiteCascadeRecordTerminalSpins (finiteCascadeContinuationGraft k.continuation v) z.2))
      ∂anisotropicRecordedProfileTreeLaw D μ a (printedGeneratedComponentClock U h)
        (finiteCascadeContinuationGraft k.continuation v)) = _
  rw [printedGeneratedComponentClock_eq_native,
    nativeStreamingGeneratedRetainedVertexComponent_clock]
  rfl

theorem cavityGeneratedForest_retained_vertex_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (v : FiniteCascadeRecordVertex (W.tree c)) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels (W.label c) v.depth = .mark b)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (G : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree ×
      k.Mark (Configuration (n+1)) → ℝ) :
    (∫ σ, nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (W.component c) h) (W.tree c) v k
      (fun z => G (Function.update σ c z.1,z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure _)) =
      ∫ σ, cavityGeneratedForestRetainedVertexTerminalTest W c v b hb k G σ
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a
          (cavityGeneratedForestRetainedVertexReplacement W c v b hb k).depth
          (cavityGeneratedForestRetainedVertexReplacement W c v b hb k).tree
          ((cavityGeneratedForestRetainedVertexReplacement W c v b hb k).clockTemplate.clock h) :
          Measure _) := by
  let U := nativeStreamingGeneratedRetainedVertexComponent (W.component c) v b hb k
  let F := cavityGeneratedForestRetainedVertexTerminalTest W c v b hb k G
  calc
    _ = ∫ σ, ∫ τ, F (cavityGeneratedForestReplacementTerminal W c U σ τ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a U h
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure _) := by
      apply integral_congr_ae
      refine .of_forall fun σ => ?_
      have H := cavityGeneratedComponentTerminalMeasure_retained_vertex_integral D μ a
        (W.component c) v b hb k h (fun z => G (Function.update σ c z.1,z.2))
      refine H.symm.trans ?_
      apply integral_congr_ae
      exact .of_forall fun τ =>
        (cavityGeneratedForestRetainedVertexTerminalTest_replacement W c v b hb k G σ τ).symm
    _ = _ := integral_cavityGeneratedForest_component_replacement D μ a W c U h F

end QuantitativeFollowup
