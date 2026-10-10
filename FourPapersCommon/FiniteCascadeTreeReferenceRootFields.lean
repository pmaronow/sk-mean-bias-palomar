module
public import FourPapersCommon.FiniteCascadeTreeReferenceLinearFields

@[expose] public section

/-! Actual retained-field maps on the single Gaussian input, including the
random root field. No spin or field covariance identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]

def finiteCascadeTreeReferenceRootVertexCLM
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (v : Unit ⊕ FieldVertex T) :
    (FiniteStateField S × FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T)) →L[ℝ]
      FiniteStateField S :=
  let root := ContinuousLinearMap.fst ℝ (FiniteStateField S) _ +
    R.comp (finiteGaussianLeft.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _))
  Sum.elim (fun _ => root) (fun w => (finiteCascadeTreeReferenceVertexCLM L T w).comp
    (root.prod (finiteGaussianRight.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _)))) v

def finiteCascadeTreeReferenceRootNoiseVertexCLM
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (v : Unit ⊕ FieldVertex T) :
    FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T) →L[ℝ] FiniteStateField S :=
  (finiteCascadeTreeReferenceRootVertexCLM L T R v).comp
    ((0 : FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T) →L[ℝ] FiniteStateField S).prod
      (ContinuousLinearMap.id ℝ _))

def finiteCascadeTreeRootRecordFieldAt {j : ℕ} (T : FiniteTerminalGenealogy j)
    (p : FiniteStateField S × Records (FiniteStateField S) S T) : Unit ⊕ FieldVertex T → FiniteStateField S :=
  Sum.elim (fun _ => p.1) (recordFieldAt T p.2)

theorem finiteCascadeTreeReferenceRootFlatRecord_field_eq_clm
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (z : FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T)) (σ : TerminalSpins S T)
    (v : Unit ⊕ FieldVertex T) :
    finiteCascadeTreeRootRecordFieldAt T (finiteCascadeTreeReferenceRootFlatRecord L T R H (z,σ)) v =
      finiteCascadeTreeReferenceRootVertexCLM L T R v (H,z) := by
  cases v with
  | inl u => rfl
  | inr w =>
      exact finiteCascadeTreeReferenceFlatRecord_field_eq_clm L T
        (H + R (finiteGaussianLeft z)) (finiteGaussianRight z) σ w

theorem finiteCascadeTreeReferenceRootFlatRecord_zero_field_eq_clm
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (z : FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T)) (σ : TerminalSpins S T)
    (v : Unit ⊕ FieldVertex T) :
    finiteCascadeTreeRootRecordFieldAt T (finiteCascadeTreeReferenceRootFlatRecord L T R 0 (z,σ)) v =
      finiteCascadeTreeReferenceRootNoiseVertexCLM L T R v z :=
  finiteCascadeTreeReferenceRootFlatRecord_field_eq_clm L T R 0 z σ v

def finiteCascadeTreeReferenceRootNoiseFieldsCLM
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) :
    FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T) →L[ℝ]
      ((Unit ⊕ FieldVertex T) → FiniteStateField S) :=
  ContinuousLinearMap.pi (finiteCascadeTreeReferenceRootNoiseVertexCLM L T R)

theorem finiteCascadeTreeReferenceRootFlatRecord_zero_fields_eq_clm
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (z : FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T)) (σ : TerminalSpins S T) :
    finiteCascadeTreeRootRecordFieldAt T (finiteCascadeTreeReferenceRootFlatRecord L T R 0 (z,σ)) =
      finiteCascadeTreeReferenceRootNoiseFieldsCLM L T R z := by
  funext v
  exact finiteCascadeTreeReferenceRootFlatRecord_zero_field_eq_clm L T R z σ v

end FourPapersCommon
