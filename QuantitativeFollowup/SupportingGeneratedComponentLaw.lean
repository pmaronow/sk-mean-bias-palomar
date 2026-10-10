module
public import QuantitativeFollowup.SupportingGeneratedNormalizerForest

@[expose] public section

/-! Component-wise native laws and their genuine casts. These provide a
record-level bridge between the appended finite-index forest and the
independent old-group-plus-binary-component representation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def printedGeneratedComponentRawClock (C : CavityGeneratedConstructedComponent m)
    (H : CavityGeneratedHistory Paper.Overlap m) (j : ℕ) : Paper.Overlap :=
  if hj : j≤C.depth then (C.label ⟨j,by omega⟩).value H else 0

def printedGeneratedComponentClock (C : CavityGeneratedConstructedComponent m)
    (H : CavityGeneratedHistory Paper.Overlap m) : ℕ → Paper.Overlap :=
  cavityGeneratedClippedClock (printedGeneratedComponentRawClock C H)

abbrev PrintedGeneratedComponentRecord (n : ℕ) (C : CavityGeneratedConstructedComponent m) :=
  AnisotropicObservationState (n+1) ×
    Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) C.tree

def printedGeneratedComponentLaw (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (C : CavityGeneratedConstructedComponent m)
    (H : CavityGeneratedHistory Paper.Overlap m) : Measure (PrintedGeneratedComponentRecord n C) :=
  anisotropicRecordedProfileTreeLaw D μ a (printedGeneratedComponentClock C H) C.tree

instance printedGeneratedComponentLaw_probability (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (C : CavityGeneratedConstructedComponent m)
    (H : CavityGeneratedHistory Paper.Overlap m) :
    IsProbabilityMeasure (printedGeneratedComponentLaw D μ a C H) := by
  dsimp only [printedGeneratedComponentLaw]
  infer_instance

theorem printedGeneratedComponentClock_of_forest (W : CavityGeneratedConstructedForest m)
    (H : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    printedGeneratedComponentClock (W.component c) H = W.clockTemplate.clock H c := rfl

theorem printedGeneratedForestLaw_eq_components (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (H : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedNativeForestLaw D μ a W.depth W.tree (W.clockTemplate.clock H) =
      Measure.pi (fun c => printedGeneratedComponentLaw D μ a (W.component c) H) := rfl

theorem printedGeneratedComponent_cast_measurePreserving (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (C C' : CavityGeneratedConstructedComponent m)
    (h : C=C') (H : CavityGeneratedHistory Paper.Overlap m) :
    MeasurePreserving (cast (congrArg (PrintedGeneratedComponentRecord n) h))
      (printedGeneratedComponentLaw D μ a C H) (printedGeneratedComponentLaw D μ a C' H) := by
  cases h
  constructor
  · exact measurable_id
  · change Measure.map id _ = _
    exact Measure.map_id

def printedGeneratedAppendIndex (C : ℕ) : Fin (C+1) ≃ Fin C ⊕ Unit where
  toFun := Fin.lastCases (.inr ()) (fun i => .inl i)
  invFun := fun k => match k with
    | .inl i => i.castSucc
    | .inr _ => Fin.last C
  left_inv := by
    intro i
    cases i using Fin.lastCases <;> simp
  right_inv := by
    rintro (i | u)
    · simp
    · cases u
      simp

def printedGeneratedAppendSumComponent (W : CavityGeneratedConstructedForest m) :
    Fin W.componentCount ⊕ Unit → CavityGeneratedConstructedComponent (m+1)
  | .inl c => (W.reindex Fin.castSucc).component c
  | .inr _ => cavityGeneratedSiblingComponent (Fin.last m) (.fork .single .single)

theorem printedGeneratedAppendComponent_eq_sum (W : CavityGeneratedConstructedForest m)
    (k : Fin W.componentCount ⊕ Unit) :
    (printedGeneratedNormalizerAppendedForest W).component
        ((printedGeneratedAppendIndex W.componentCount).symm k) =
      printedGeneratedAppendSumComponent W k := by
  cases k with
  | inl c => exact printedGeneratedNormalizerAppendedForest_old_component W c
  | inr u => cases u;exact printedGeneratedNormalizerAppendedForest_new_component W

def printedGeneratedAppendRecordBridge (W : CavityGeneratedConstructedForest m)
    (z : CavityGeneratedForestRecord (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    (k : Fin W.componentCount ⊕ Unit) →
      PrintedGeneratedComponentRecord n (printedGeneratedAppendSumComponent W k) :=
  fun k => cast (congrArg (PrintedGeneratedComponentRecord n)
    (printedGeneratedAppendComponent_eq_sum W k))
      (z ((printedGeneratedAppendIndex W.componentCount).symm k))

theorem printedGeneratedAppendRecordBridge_measurePreserving
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    MeasurePreserving (printedGeneratedAppendRecordBridge (n:=n) W)
      (cavityGeneratedNativeForestLaw D μ a (printedGeneratedNormalizerAppendedForest W).depth
        (printedGeneratedNormalizerAppendedForest W).tree
        ((printedGeneratedNormalizerAppendedForest W).clockTemplate.clock H))
      (Measure.pi (fun k => printedGeneratedComponentLaw D μ a
        (printedGeneratedAppendSumComponent W k) H)) := by
  let A := printedGeneratedNormalizerAppendedForest W
  let e := (printedGeneratedAppendIndex W.componentCount).symm
  have hp := measurePreserving_piCongrLeft
    (fun c : Fin A.componentCount => printedGeneratedComponentLaw D μ a (A.component c) H) e
  have hc := measurePreserving_pi
    (fun k => printedGeneratedComponentLaw D μ a (A.component (e k)) H)
    (fun k => printedGeneratedComponentLaw D μ a (printedGeneratedAppendSumComponent W k) H)
    (fun k => printedGeneratedComponent_cast_measurePreserving D μ a _ _
      (printedGeneratedAppendComponent_eq_sum W k) H)
  exact hc.comp hp.symm

end QuantitativeFollowup
