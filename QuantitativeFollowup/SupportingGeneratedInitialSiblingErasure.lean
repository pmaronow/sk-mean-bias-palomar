module
public import QuantitativeFollowup.SupportingGeneratedInitialSiblingErasureKernel
public import QuantitativeFollowup.SupportingGeneratedInitialSourceFamily
public import QuantitativeFollowup.FollowupCavityGeneratedForestComponentReplacementRetained
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsClocks

@[expose] public section

/-! Genuine initial terminal laws and arbitrary terminal tests pass to the
canonical sibling tree by unary erasure. This is a base-law normalization;
selected-origin source transport is a separate theorem. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n J : ℕ}

def printedGeneratedInitialTerminalMeasure (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) : Measure (TerminalSpins (Configuration n) T) :=
  (anisotropicRecordedProfileTreeLaw D μ a q T).map
    (fun z => finiteCascadeRecordTerminalSpins T z.2)

theorem printedGeneratedInitialTerminalMeasure_eq_comp
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J) :
    printedGeneratedInitialTerminalMeasure D μ a q T =
      printedGeneratedInitialTerminalKernel D μ q T ∘ₘ anisotropicObservationInitialLaw D μ a := by
  unfold printedGeneratedInitialTerminalMeasure anisotropicRecordedProfileTreeLaw
  rw [Measure.compProd_eq_comp_prod]
  change ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₘ
    anisotropicObservationInitialLaw D μ a).map
      ((finiteCascadeRecordTerminalSpins T) ∘ Prod.snd) = _
  rw [Measure.map_comp _ _
      ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd),
    Kernel.map_comp_right _ measurable_snd (measurable_finiteCascadeRecordTerminalSpins T),
    ←Kernel.snd_eq,Kernel.snd_prod]
  rfl

theorem printedGeneratedInitialSiblingErasure_terminal_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0 = 1)
    (p : Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (hfork : printedGeneratedInitialForksAt q p T) (htop : q J = 0) :
    (printedGeneratedInitialTerminalMeasure D μ a q T).map
      (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T) =
      printedGeneratedInitialTerminalMeasure D μ a (anisotropicBinaryObservationSchedule p)
        (.advance (printedGeneratedInitialSiblingErasure T).tree) := by
  rw [printedGeneratedInitialTerminalMeasure_eq_comp,Measure.map_comp _ _
    (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T).measurable,
    printedGeneratedInitialTerminalMeasure_eq_comp]
  apply congrArg (fun (K : Kernel (AnisotropicObservationState n)
    (TerminalSpins (Configuration n) (.advance (printedGeneratedInitialSiblingErasure T).tree))) =>
      K ∘ₘ anisotropicObservationInitialLaw D μ a)
  change ((anisotropicRecordedProfileTreeKernel D μ q T).map
    (finiteCascadeRecordTerminalSpins T)).map
      (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T) = _
  rw [←Kernel.map_comp_right _ (measurable_finiteCascadeRecordTerminalSpins T)
    (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T).measurable]
  exact printedGeneratedInitialSiblingErasure_terminal_kernel D μ q hq hzero p T hfork htop

theorem printedGeneratedInitialSiblingErasure_terminal_test
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0 = 1)
    (p : Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (hfork : printedGeneratedInitialForksAt q p T) (htop : q J = 0)
    (F : TerminalSpins (Configuration n) T → ℝ) :
    (∫σ,F σ ∂printedGeneratedInitialTerminalMeasure D μ a q T) =
      ∫τ,F ((printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T).symm τ)
        ∂printedGeneratedInitialTerminalMeasure D μ a (anisotropicBinaryObservationSchedule p)
          (.advance (printedGeneratedInitialSiblingErasure T).tree) := by
  let e := printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T
  have hf : Measurable (fun τ=>F (e.symm τ)) := measurable_of_finite _
  have he := integral_map (μ:=printedGeneratedInitialTerminalMeasure D μ a q T)
    e.measurable.aemeasurable hf.aestronglyMeasurable
  rw [printedGeneratedInitialSiblingErasure_terminal_law D μ a q hq hzero p T hfork htop] at he
  simpa only [e,MeasurableEquiv.symm_apply_apply] using he.symm

theorem printedGeneratedSiblingComponent_clock {m : ℕ}
    (i : Fin m) (S : CavityGeneratedSiblingShape) (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedComponentClock (cavityGeneratedSiblingComponent i S) h =
      anisotropicBinaryObservationSchedule (h i) := by
  funext j
  cases j with
  | zero => exact nativeStreamingGeneratedComponentClock_terminal _ _
  | succ j => cases j with
    | zero =>
        change min (1:Paper.Overlap) (h i) = h i
        exact min_eq_right (h i).property.2
    | succ j =>
        rw [nativeStreamingGeneratedComponentClock_after_initial _ _ _ (by change 2 ≤ j+2; omega)]
        rfl

theorem printedGeneratedInitialSiblingErasure_component_terminal_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0 = 1)
    (p : Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (hfork : printedGeneratedInitialForksAt q p T) (htop : q J = 0) :
    (printedGeneratedInitialTerminalMeasure D μ a q T).map
      (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration (n+1)) T) =
      cavityGeneratedComponentTerminalMeasure D μ a
        (cavityGeneratedSiblingComponent (0:Fin 1) (printedGeneratedInitialSiblingErasure T))
        (printedGeneratedInitialHistory p) := by
  unfold cavityGeneratedComponentTerminalMeasure printedGeneratedComponentLaw
  rw [printedGeneratedComponentClock_eq_native]
  change _ = printedGeneratedInitialTerminalMeasure D μ a
    (nativeStreamingGeneratedComponentClock
      (cavityGeneratedSiblingComponent (0:Fin 1) (printedGeneratedInitialSiblingErasure T))
      (printedGeneratedInitialHistory p)) (.advance (printedGeneratedInitialSiblingErasure T).tree)
  rw [printedGeneratedSiblingComponent_clock]
  exact printedGeneratedInitialSiblingErasure_terminal_law D μ a q hq hzero p T hfork htop

end QuantitativeFollowup
