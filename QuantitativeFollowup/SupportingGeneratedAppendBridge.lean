module
public import QuantitativeFollowup.SupportingGeneratedComponentLaw

@[expose] public section

/-! The independent binary normalizer representation is the genuine law
of the concretely appended finite-index forest, with its old joint record retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem printedGeneratedClippedClock_of_antitone (q : ℕ → Paper.Overlap)
    (hq : Antitone q) : cavityGeneratedClippedClock q = q := by
  funext j
  induction j with
  | zero => rfl
  | succ j ih =>
      change min (cavityGeneratedClippedClock q j) (q (j+1)) = q (j+1)
      rw [ih]
      exact min_eq_right (hq (Nat.le_succ j))

theorem printedGeneratedBinarySchedule_antitone (r : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule r) := by
  apply antitone_nat_of_succ_le
  intro j
  cases j with
  | zero => exact r.property.2
  | succ j =>
      cases j with
      | zero => exact r.property.1
      | succ j => exact le_rfl

theorem printedGeneratedSiblingRawClock_binary
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    printedGeneratedComponentRawClock
      (cavityGeneratedSiblingComponent (Fin.last m) (.fork .single .single)) H =
      anisotropicBinaryObservationSchedule (H (Fin.last m)) := by
  funext j
  cases j with
  | zero => rfl
  | succ j =>
      cases j with
      | zero => rfl
      | succ j =>
          simp [printedGeneratedComponentRawClock, cavityGeneratedSiblingComponent,
            cavityGeneratedSiblingComponentLabels, CavityGeneratedClockLabel.value,
            anisotropicBinaryObservationSchedule]

theorem printedGeneratedSiblingClock_binary
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    printedGeneratedComponentClock
      (cavityGeneratedSiblingComponent (Fin.last m) (.fork .single .single)) H =
      anisotropicBinaryObservationSchedule (H (Fin.last m)) := by
  rw [printedGeneratedComponentClock, printedGeneratedSiblingRawClock_binary,
    printedGeneratedClippedClock_of_antitone _ (printedGeneratedBinarySchedule_antitone _)]

def printedGeneratedAppendSumCoordinateToNative
    (W : CavityGeneratedConstructedForest m) (k : Fin W.componentCount ⊕ Unit) :
    PrintedGeneratedComponentRecord n (printedGeneratedAppendSumComponent W k) →
      AnisotropicObservationState (n+1) ×
        Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
          (printedGeneratedNormalizerTree W.depth W.tree k) := by
  cases k with
  | inl c => exact id
  | inr u => cases u; exact id

def printedGeneratedAppendSumRecordToNative
    (W : CavityGeneratedConstructedForest m)
    (z : (k : Fin W.componentCount ⊕ Unit) →
      PrintedGeneratedComponentRecord n (printedGeneratedAppendSumComponent W k)) :
    CavityGeneratedForestRecord (n:=n) (printedGeneratedNormalizerDepth W.depth)
      (printedGeneratedNormalizerTree W.depth W.tree) :=
  fun k => printedGeneratedAppendSumCoordinateToNative W k (z k)

theorem printedGeneratedAppendSumCoordinateToNative_measurePreserving
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (k : Fin W.componentCount ⊕ Unit) :
    MeasurePreserving (printedGeneratedAppendSumCoordinateToNative (n:=n) W k)
      (printedGeneratedComponentLaw D μ a (printedGeneratedAppendSumComponent W k) (Fin.snoc h r))
      (anisotropicRecordedProfileTreeLaw D μ a
        (printedGeneratedNormalizerClock (W.clockTemplate.clock h) r k)
        (printedGeneratedNormalizerTree W.depth W.tree k)) := by
  cases k with
  | inl c =>
      constructor
      · exact measurable_id
      · change Measure.map id _ = _
        rw [Measure.map_id]
        dsimp only [printedGeneratedAppendSumComponent, printedGeneratedComponentLaw]
        rw [printedGeneratedComponentClock_of_forest,
          printedGeneratedNormalizerAppendedForest_old_clock]
        rfl
  | inr u =>
      cases u
      constructor
      · exact measurable_id
      · change Measure.map id _ = _
        rw [Measure.map_id]
        dsimp only [printedGeneratedAppendSumComponent, printedGeneratedComponentLaw]
        rw [printedGeneratedSiblingClock_binary]
        simp only [Fin.snoc_last]
        rfl

def printedGeneratedAppendRecordToNative
    (W : CavityGeneratedConstructedForest m) :=
  printedGeneratedAppendSumRecordToNative (n:=n) W ∘ printedGeneratedAppendRecordBridge W

def printedGeneratedComponentRecordCastEquiv
    (C C' : CavityGeneratedConstructedComponent m) (h : C=C') :
    PrintedGeneratedComponentRecord n C ≃ᵐ PrintedGeneratedComponentRecord n C' := by
  cases h
  exact MeasurableEquiv.refl _

theorem printedGeneratedComponentRecordCastEquiv_coe
    (C C' : CavityGeneratedConstructedComponent m) (h : C=C') :
    ⇑(printedGeneratedComponentRecordCastEquiv (n:=n) C C' h) =
      cast (congrArg (PrintedGeneratedComponentRecord n) h) := by
  cases h
  rfl

def printedGeneratedAppendRecordEquiv (W : CavityGeneratedConstructedForest m) :
    CavityGeneratedForestRecord (n:=n) (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree ≃ᵐ
      ((k : Fin W.componentCount ⊕ Unit) →
        PrintedGeneratedComponentRecord n (printedGeneratedAppendSumComponent W k)) :=
  ((MeasurableEquiv.piCongrLeft
    (fun c => PrintedGeneratedComponentRecord n ((printedGeneratedNormalizerAppendedForest W).component c))
      (printedGeneratedAppendIndex W.componentCount).symm).symm).trans
    (MeasurableEquiv.piCongrRight (fun k => printedGeneratedComponentRecordCastEquiv _ _
      (printedGeneratedAppendComponent_eq_sum W k)))

theorem printedGeneratedAppendRecordEquiv_coe (W : CavityGeneratedConstructedForest m) :
    ⇑(printedGeneratedAppendRecordEquiv (n:=n) W) = printedGeneratedAppendRecordBridge W := by
  funext z k
  change (printedGeneratedComponentRecordCastEquiv _ _
    (printedGeneratedAppendComponent_eq_sum W k))
      (z ((printedGeneratedAppendIndex W.componentCount).symm k)) = _
  rw [printedGeneratedComponentRecordCastEquiv_coe]
  rfl

def printedGeneratedAppendSumCoordinateEquiv
    (W : CavityGeneratedConstructedForest m) (k : Fin W.componentCount ⊕ Unit) :
    PrintedGeneratedComponentRecord n (printedGeneratedAppendSumComponent W k) ≃ᵐ
      (AnisotropicObservationState (n+1) ×
        Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
          (printedGeneratedNormalizerTree W.depth W.tree k)) := by
  cases k with
  | inl c => exact MeasurableEquiv.refl _
  | inr u => cases u; exact MeasurableEquiv.refl _

def printedGeneratedAppendRecordToNativeEquiv (W : CavityGeneratedConstructedForest m) :
    CavityGeneratedForestRecord (n:=n) (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree ≃ᵐ
      CavityGeneratedForestRecord (n:=n) (printedGeneratedNormalizerDepth W.depth)
        (printedGeneratedNormalizerTree W.depth W.tree) :=
  (printedGeneratedAppendRecordEquiv W).trans
    (MeasurableEquiv.piCongrRight (printedGeneratedAppendSumCoordinateEquiv W))

theorem printedGeneratedAppendRecordToNativeEquiv_coe
    (W : CavityGeneratedConstructedForest m) :
    ⇑(printedGeneratedAppendRecordToNativeEquiv (n:=n) W) = printedGeneratedAppendRecordToNative W := by
  funext z k
  change (printedGeneratedAppendSumCoordinateEquiv W k)
    ((printedGeneratedAppendRecordEquiv W) z k) = _
  rw [printedGeneratedAppendRecordEquiv_coe]
  cases k with
  | inl c => rfl
  | inr u => cases u; rfl

theorem printedGeneratedAppendRecordBridge_measurePreserving_nativeNormalizer
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) :
    MeasurePreserving (printedGeneratedAppendRecordToNative (n:=n) W)
      (cavityGeneratedNativeForestLaw D μ a (printedGeneratedNormalizerAppendedForest W).depth
        (printedGeneratedNormalizerAppendedForest W).tree
        ((printedGeneratedNormalizerAppendedForest W).clockTemplate.clock (Fin.snoc h r)))
      (cavityGeneratedNativeForestLaw D μ a (printedGeneratedNormalizerDepth W.depth)
        (printedGeneratedNormalizerTree W.depth W.tree)
        (printedGeneratedNormalizerClock (W.clockTemplate.clock h) r)) := by
  exact (measurePreserving_pi
    (fun k => printedGeneratedComponentLaw D μ a (printedGeneratedAppendSumComponent W k) (Fin.snoc h r))
    (fun k => anisotropicRecordedProfileTreeLaw D μ a
      (printedGeneratedNormalizerClock (W.clockTemplate.clock h) r k)
      (printedGeneratedNormalizerTree W.depth W.tree k))
    (printedGeneratedAppendSumCoordinateToNative_measurePreserving D μ a W h r)).comp
      (printedGeneratedAppendRecordBridge_measurePreserving D μ a W (Fin.snoc h r))

theorem printedGeneratedNormalizerAppendedForest_terminal_expectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) :
    (∫z, F h (cavityGeneratedForestTerminalProjection W.depth W.tree
          (printedGeneratedNormalizerOldRecord W.depth W.tree
            (printedGeneratedAppendRecordToNative W z)))*
        nativeStreamingNormalizerBinaryTerminalTest n r
          (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree
            (printedGeneratedNormalizerNewRecord W.depth W.tree
              (printedGeneratedAppendRecordToNative W z)).2)
      ∂cavityGeneratedNativeForestLaw D μ a (printedGeneratedNormalizerAppendedForest W).depth
        (printedGeneratedNormalizerAppendedForest W).tree
        ((printedGeneratedNormalizerAppendedForest W).clockTemplate.clock (Fin.snoc h r))) =
      (∫σ, F h σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure _))*
        (∫z, cavitySpinOverlapDefect n r z.2.1 z.2.2 ∂anisotropicFreshTerminalPairLaw D μ a r) := by
  let K : CavityGeneratedForestRecord (n:=n) (printedGeneratedNormalizerDepth W.depth)
      (printedGeneratedNormalizerTree W.depth W.tree) → ℝ := fun z =>
    F h (cavityGeneratedForestTerminalProjection W.depth W.tree
      (printedGeneratedNormalizerOldRecord W.depth W.tree z))*
      nativeStreamingNormalizerBinaryTerminalTest n r
        (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree
          (printedGeneratedNormalizerNewRecord W.depth W.tree z).2)
  have he : MeasurableEmbedding (printedGeneratedAppendRecordToNative (n:=n) W) := by
    rw [←printedGeneratedAppendRecordToNativeEquiv_coe]
    exact (printedGeneratedAppendRecordToNativeEquiv W).measurableEmbedding
  have hp := (printedGeneratedAppendRecordBridge_measurePreserving_nativeNormalizer
    D μ a W h r).integral_comp he K
  exact hp.trans (printedGeneratedNormalizerForest_terminal_expectation D μ a W.depth W.tree
    (W.clockTemplate.clock h) r h F)

end QuantitativeFollowup
