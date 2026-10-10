module
public import FourPapersCommon.FiniteCascadeTreeDensity

@[expose] public section

/-! Independent Gaussian coordinates and independent counting spins for the
raw finite-tree reference law. Every advance has its own Gaussian coordinate;
forks retain both independent coordinate families, including zero increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

namespace FiniteTerminalGenealogy

@[reducible] def GaussianCoordinates (I : Type) [Fintype I] :
    {j : ℕ} → FiniteTerminalGenealogy j → Type
  | _, .leaf => Unit
  | _, .advance T => FiniteStateGaussianInput I × GaussianCoordinates I T
  | _, .fork T U => GaussianCoordinates I T × GaussianCoordinates I U

@[reducible] def TerminalSpins (S : Type) :
    {j : ℕ} → FiniteTerminalGenealogy j → Type
  | _, .leaf => S
  | _, .advance T => TerminalSpins S T
  | _, .fork T U => TerminalSpins S T × TerminalSpins S U

@[reducible] def gaussianCoordinateMeasurableSpace (I : Type) [Fintype I] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → MeasurableSpace (GaussianCoordinates I T)
  | _, .leaf => inferInstanceAs (MeasurableSpace Unit)
  | _, .advance T => @Prod.instMeasurableSpace _ _ inferInstance
      (gaussianCoordinateMeasurableSpace I T)
  | _, .fork T U => @Prod.instMeasurableSpace _ _
      (gaussianCoordinateMeasurableSpace I T) (gaussianCoordinateMeasurableSpace I U)

@[reducible] def terminalSpinMeasurableSpace (S : Type) [MeasurableSpace S] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → MeasurableSpace (TerminalSpins S T)
  | _, .leaf => inferInstanceAs (MeasurableSpace S)
  | _, .advance T => terminalSpinMeasurableSpace S T
  | _, .fork T U => @Prod.instMeasurableSpace _ _
      (terminalSpinMeasurableSpace S T) (terminalSpinMeasurableSpace S U)

instance instMeasurableGaussianCoordinates (I : Type) [Fintype I] {j : ℕ}
    (T : FiniteTerminalGenealogy j) : MeasurableSpace (GaussianCoordinates I T) :=
  gaussianCoordinateMeasurableSpace I T

instance instMeasurableTerminalSpins (S : Type) [MeasurableSpace S] {j : ℕ}
    (T : FiniteTerminalGenealogy j) : MeasurableSpace (TerminalSpins S T) :=
  terminalSpinMeasurableSpace S T

@[reducible] def gaussianCoordinateLaw (I : Type) [Fintype I] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Measure (GaussianCoordinates I T)
  | _, .leaf => Measure.dirac ()
  | _, .advance T => (stdGaussian (FiniteStateGaussianInput I)).prod (gaussianCoordinateLaw I T)
  | _, .fork T U => (gaussianCoordinateLaw I T).prod (gaussianCoordinateLaw I U)

@[reducible] def terminalSpinCountingLaw (S : Type) [MeasurableSpace S] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Measure (TerminalSpins S T)
  | _, .leaf => Measure.count
  | _, .advance T => terminalSpinCountingLaw S T
  | _, .fork T U => (terminalSpinCountingLaw S T).prod (terminalSpinCountingLaw S U)

theorem isProbabilityMeasure_gaussianCoordinateLaw (I : Type) [Fintype I]
    {j : ℕ} (T : FiniteTerminalGenealogy j) : IsProbabilityMeasure (gaussianCoordinateLaw I T) := by
  induction T with
  | leaf => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | advance T ih =>
      haveI := ih
      change IsProbabilityMeasure ((stdGaussian _).prod _)
      infer_instance
  | fork T U ihT ihU =>
      haveI := ihT
      haveI := ihU
      change IsProbabilityMeasure ((gaussianCoordinateLaw I T).prod (gaussianCoordinateLaw I U))
      infer_instance

theorem isFiniteMeasure_terminalSpinCountingLaw (S : Type) [Fintype S]
    [MeasurableSpace S] {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsFiniteMeasure (terminalSpinCountingLaw S T) := by
  induction T with
  | leaf => change IsFiniteMeasure (Measure.count : Measure S); infer_instance
  | advance T ih => exact ih
  | fork T U ihT ihU =>
      haveI := ihT
      haveI := ihU
      change IsFiniteMeasure ((terminalSpinCountingLaw S T).prod (terminalSpinCountingLaw S U))
      infer_instance

attribute [local instance] isProbabilityMeasure_gaussianCoordinateLaw
  isFiniteMeasure_terminalSpinCountingLaw

end FiniteTerminalGenealogy

variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

@[reducible] def finiteCascadeTreeReferenceRecord
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → FiniteStateField S →
      GaussianCoordinates I T × TerminalSpins S T → Records (FiniteStateField S) S T
  | _, .leaf => fun _ p => p.2
  | _, @FiniteTerminalGenealogy.advance j T => fun H p =>
      (H + L j p.1.1, finiteCascadeTreeReferenceRecord L T (H + L j p.1.1) (p.1.2,p.2))
  | _, .fork T U => fun H p =>
      (finiteCascadeTreeReferenceRecord L T H (p.1.1,p.2.1),
        finiteCascadeTreeReferenceRecord L U H (p.1.2,p.2.2))

theorem measurable_finiteCascadeTreeReferenceRecord
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (Function.uncurry (finiteCascadeTreeReferenceRecord L T)) := by
  induction T with
  | leaf => exact measurable_snd.comp measurable_snd
  | @advance j T ih =>
      have hh : Measurable (fun p : FiniteStateField S ×
          (GaussianCoordinates I (.advance T) × TerminalSpins S (.advance T)) =>
          p.1 + L j p.2.1.1) :=
        measurable_fst.add ((L j).measurable.comp (measurable_fst.comp (measurable_fst.comp measurable_snd)))
      exact hh.prodMk (ih.comp (hh.prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))))
  | fork T U ihT ihU =>
      exact (ihT.comp (measurable_fst.prodMk
        ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd))))).prodMk
        (ihU.comp (measurable_fst.prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))))

end FourPapersCommon
