module
public import FourPapersCommon.FiniteCascadeTreeReferenceLaw
public import FourPapersCommon.FiniteGaussianSumLaw

@[expose] public section

/-! A single genuine finite-dimensional standard Gaussian realizes every
independent edge input of the reference tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
attribute [local instance] isProbabilityMeasure_gaussianCoordinateLaw
  isFiniteMeasure_terminalSpinCountingLaw

namespace FiniteTerminalGenealogy

private theorem measurable_left {A B : Type} [Fintype A] [Fintype B] :
    Measurable (finiteGaussianLeft (I:=A) (J:=B)) := finiteGaussianLeft.continuous.measurable

private theorem measurable_right {A B : Type} [Fintype A] [Fintype B] :
    Measurable (finiteGaussianRight (I:=A) (J:=B)) := finiteGaussianRight.continuous.measurable

@[reducible] def GaussianCoordinateIndex (I : Type) :
    {j : ℕ} → FiniteTerminalGenealogy j → Type
  | _, .leaf => Empty
  | _, .advance T => I ⊕ GaussianCoordinateIndex I T
  | _, .fork T U => GaussianCoordinateIndex I T ⊕ GaussianCoordinateIndex I U

@[reducible] def gaussianCoordinateIndexFintype (I : Type) [Fintype I] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Fintype (GaussianCoordinateIndex I T)
  | _, .leaf => inferInstanceAs (Fintype Empty)
  | _, .advance T => by
      letI := gaussianCoordinateIndexFintype I T
      exact inferInstanceAs (Fintype (I ⊕ GaussianCoordinateIndex I T))
  | _, .fork T U => by
      letI := gaussianCoordinateIndexFintype I T
      letI := gaussianCoordinateIndexFintype I U
      exact inferInstanceAs (Fintype (GaussianCoordinateIndex I T ⊕ GaussianCoordinateIndex I U))

instance instFintypeGaussianCoordinateIndex (I : Type) [Fintype I] {j : ℕ}
    (T : FiniteTerminalGenealogy j) : Fintype (GaussianCoordinateIndex I T) :=
  gaussianCoordinateIndexFintype I T

@[reducible] def gaussianCoordinateUnflatten (I : Type) [Fintype I] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      FiniteStateGaussianInput (GaussianCoordinateIndex I T) → GaussianCoordinates I T
  | _, .leaf => fun _ => ()
  | _, .advance T => fun z =>
      (finiteGaussianLeft z, gaussianCoordinateUnflatten I T (finiteGaussianRight z))
  | _, .fork T U => fun z =>
      (gaussianCoordinateUnflatten I T (finiteGaussianLeft z),
        gaussianCoordinateUnflatten I U (finiteGaussianRight z))

theorem measurable_gaussianCoordinateUnflatten (I : Type) [Fintype I]
    {j : ℕ} (T : FiniteTerminalGenealogy j) : Measurable (gaussianCoordinateUnflatten I T) := by
  induction T with
  | leaf => exact measurable_const
  | advance T ih => exact measurable_left.prodMk (ih.comp measurable_right)
  | fork T U ihT ihU =>
      exact (ihT.comp measurable_left).prodMk (ihU.comp measurable_right)

theorem stdGaussian_map_gaussianCoordinateUnflatten (I : Type) [Fintype I]
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (stdGaussian (FiniteStateGaussianInput (GaussianCoordinateIndex I T))).map
      (gaussianCoordinateUnflatten I T) = gaussianCoordinateLaw I T := by
  induction T with
  | leaf =>
      change (stdGaussian (FiniteStateGaussianInput Empty)).map (fun _ => ()) = Measure.dirac ()
      simp
  | advance T ih =>
      have he : gaussianCoordinateUnflatten I (.advance T) =
          Prod.map id (gaussianCoordinateUnflatten I T) ∘ finiteGaussianSplit := rfl
      rw [he,←Measure.map_map (measurable_id.prodMap (measurable_gaussianCoordinateUnflatten I T))
        measurable_finiteGaussianSplit,stdGaussian_map_finiteGaussianSplit,
        ←Measure.map_prod_map _ _ measurable_id (measurable_gaussianCoordinateUnflatten I T),
        Measure.map_id,ih]
  | fork T U ihT ihU =>
      have he : gaussianCoordinateUnflatten I (.fork T U) =
          Prod.map (gaussianCoordinateUnflatten I T) (gaussianCoordinateUnflatten I U) ∘
            finiteGaussianSplit := rfl
      rw [he,←Measure.map_map ((measurable_gaussianCoordinateUnflatten I T).prodMap
        (measurable_gaussianCoordinateUnflatten I U)) measurable_finiteGaussianSplit,
        stdGaussian_map_finiteGaussianSplit,←Measure.map_prod_map _ _
          (measurable_gaussianCoordinateUnflatten I T) (measurable_gaussianCoordinateUnflatten I U),
        ihT,ihU]

end FiniteTerminalGenealogy

variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

def finiteCascadeTreeReferenceFlatRecord
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (p : FiniteStateGaussianInput (GaussianCoordinateIndex I T) × TerminalSpins S T) :
    Records (FiniteStateField S) S T :=
  finiteCascadeTreeReferenceRecord L T H (gaussianCoordinateUnflatten I T p.1,p.2)

theorem measurable_finiteCascadeTreeReferenceFlatRecord
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (Function.uncurry (finiteCascadeTreeReferenceFlatRecord L T)) :=
  (measurable_finiteCascadeTreeReferenceRecord L T).comp
    (measurable_fst.prodMk
      (((measurable_gaussianCoordinateUnflatten I T).comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))

theorem finiteCascadeTreeReferenceKernel_eq_flat_gaussian
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S) :
    ((stdGaussian (FiniteStateGaussianInput (GaussianCoordinateIndex I T))).prod
      (terminalSpinCountingLaw S T)).map (finiteCascadeTreeReferenceFlatRecord L T H) =
        finiteCascadeTreeReferenceKernel L T H := by
  rw [←finiteCascadeTreeReferenceKernel_eq_gaussian_coordinates L T H,
    ←stdGaussian_map_gaussianCoordinateUnflatten I T]
  nth_rw 2 [←Measure.map_id (μ:=terminalSpinCountingLaw S T)]
  rw [Measure.map_prod_map _ _ (measurable_gaussianCoordinateUnflatten I T) measurable_id,
    Measure.map_map
      (show Measurable (finiteCascadeTreeReferenceRecord L T H) from
        (measurable_finiteCascadeTreeReferenceRecord L T).comp measurable_prodMk_left)
      ((measurable_gaussianCoordinateUnflatten I T).prodMap measurable_id)]
  rfl

end FourPapersCommon
