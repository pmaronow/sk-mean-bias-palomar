module
public import FourPapersCommon.FiniteCascadeTreeReferenceRootGaussian

@[expose] public section

/-! Every retained field in the exact Gaussian-coordinate realization is an
actual continuous linear function of the initial field and all edge inputs. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

namespace FiniteTerminalGenealogy

@[reducible] def FieldVertex : {j : ℕ} → FiniteTerminalGenealogy j → Type
  | _, .leaf => Empty
  | _, .advance T => Unit ⊕ FieldVertex T
  | _, .fork T U => FieldVertex T ⊕ FieldVertex U

@[reducible] def fieldVertexFintype :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Fintype (FieldVertex T)
  | _, .leaf => inferInstanceAs (Fintype Empty)
  | _, .advance T => by
      letI := fieldVertexFintype T
      exact inferInstanceAs (Fintype (Unit ⊕ FieldVertex T))
  | _, .fork T U => by
      letI := fieldVertexFintype T
      letI := fieldVertexFintype U
      exact inferInstanceAs (Fintype (FieldVertex T ⊕ FieldVertex U))

instance instFintypeFieldVertex {j : ℕ} (T : FiniteTerminalGenealogy j) : Fintype (FieldVertex T) :=
  fieldVertexFintype T

@[reducible] def recordFieldAt {E S : Type} :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Records E S T → FieldVertex T → E
  | _, .leaf => fun _ v => Empty.elim v
  | _, .advance T => fun z => Sum.elim (fun _ => z.1) (recordFieldAt T z.2)
  | _, .fork T U => fun z => Sum.elim (recordFieldAt T z.1) (recordFieldAt U z.2)

end FiniteTerminalGenealogy

variable {S I : Type} [Fintype S] [Fintype I]

@[reducible] def finiteCascadeTreeReferenceVertexCLM
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → FieldVertex T →
      (FiniteStateField S × FiniteStateGaussianInput (GaussianCoordinateIndex I T) →L[ℝ]
        FiniteStateField S)
  | _, .leaf => fun v => Empty.elim v
  | _, @FiniteTerminalGenealogy.advance j T =>
      let hmap := ContinuousLinearMap.fst ℝ (FiniteStateField S)
          (FiniteStateGaussianInput (I ⊕ GaussianCoordinateIndex I T)) +
        (L j).comp (finiteGaussianLeft.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S)
          (FiniteStateGaussianInput (I ⊕ GaussianCoordinateIndex I T))))
      Sum.elim (fun _ => hmap) (fun v => (finiteCascadeTreeReferenceVertexCLM L T v).comp
        (hmap.prod (finiteGaussianRight.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S)
          (FiniteStateGaussianInput (I ⊕ GaussianCoordinateIndex I T))))))
  | _, .fork T U => Sum.elim
      (fun v => (finiteCascadeTreeReferenceVertexCLM L T v).comp
        ((ContinuousLinearMap.fst ℝ (FiniteStateField S) _).prod
          (finiteGaussianLeft.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _))))
      (fun v => (finiteCascadeTreeReferenceVertexCLM L U v).comp
        ((ContinuousLinearMap.fst ℝ (FiniteStateField S) _).prod
          (finiteGaussianRight.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _))))

theorem finiteCascadeTreeReferenceFlatRecord_field_eq_clm
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T)) (σ : TerminalSpins S T)
    (v : FieldVertex T) :
    recordFieldAt T (finiteCascadeTreeReferenceFlatRecord L T H (z,σ)) v =
      finiteCascadeTreeReferenceVertexCLM L T v (H,z) := by
  induction T generalizing H with
  | leaf => exact Empty.elim v
  | @advance j T ih =>
      cases v with
      | inl u => rfl
      | inr v =>
          exact ih (H + L j (finiteGaussianLeft z)) (finiteGaussianRight z) σ v
  | fork T U ihT ihU =>
      cases v with
      | inl v => exact ihT H (finiteGaussianLeft z) σ.1 v
      | inr v => exact ihU H (finiteGaussianRight z) σ.2 v

def finiteCascadeTreeReferenceFieldsCLM
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (FiniteStateField S × FiniteStateGaussianInput (GaussianCoordinateIndex I T)) →L[ℝ]
      (FieldVertex T → FiniteStateField S) :=
  ContinuousLinearMap.pi (finiteCascadeTreeReferenceVertexCLM L T)

theorem finiteCascadeTreeReferenceFlatRecord_fields_eq_clm
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T)) (σ : TerminalSpins S T) :
    recordFieldAt T (finiteCascadeTreeReferenceFlatRecord L T H (z,σ)) =
      finiteCascadeTreeReferenceFieldsCLM L T (H,z) := by
  funext v
  exact finiteCascadeTreeReferenceFlatRecord_field_eq_clm L T H z σ v

end FourPapersCommon
