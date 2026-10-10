module
public import FourPapersCommon.FiniteCascadeTreeReferenceLaw
public import FourPapersCommon.FiniteStateCascadePosteriorLogDensity
public import QuantitativePaper.VectorHistoryProperties
public import QuantitativeFollowup.FollowupCavityFixedRowSymmetry

@[expose] public section

/-! Chronological independent Gaussian inputs are reindexed into the actual
linear retained genealogy. Every input, including a zero or singular field
increment, is retained; the terminal spin is unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency false

variable {S I : Type} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

@[reducible] def cavityLineTerminalEquiv :
    (N : ℕ) → S ≃ᵐ TerminalSpins S (observationLinearTree N)
  | 0 => MeasurableEquiv.refl S
  | N+1 => cavityLineTerminalEquiv N

theorem cavityLineTerminalEquiv_law (N : ℕ) :
    (Measure.count : Measure S).map (cavityLineTerminalEquiv (S:=S) N) =
      terminalSpinCountingLaw S (observationLinearTree N) := by
  induction N with
  | zero => exact Measure.map_id
  | succ N ih => exact ih

@[reducible] def cavityLineGaussianCoordinates :
    (N : ℕ) → (Fin N → FiniteStateGaussianInput I) →
      GaussianCoordinates I (observationLinearTree N)
  | 0 => fun _ => ()
  | N+1 => fun z => (z 0, cavityLineGaussianCoordinates N (Fin.tail z))

theorem measurable_cavityLineGaussianCoordinates (N : ℕ) :
    Measurable (cavityLineGaussianCoordinates (I:=I) N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      exact (measurable_pi_apply 0).prodMk
        (ih.comp (measurable_pi_iff.2 fun i => measurable_pi_apply i.succ))

theorem cavityLineGaussianCoordinates_law (N : ℕ) :
    (Measure.pi (fun _ : Fin N => stdGaussian (FiniteStateGaussianInput I))).map
        (cavityLineGaussianCoordinates N) =
      gaussianCoordinateLaw I (observationLinearTree N) := by
  induction N with
  | zero =>
      rw [Measure.pi_of_empty]
      exact Measure.map_dirac _
  | succ N ih =>
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (N+1) => FiniteStateGaussianInput I) 0
      have he : (Measure.pi (fun _ : Fin (N+1) => stdGaussian (FiniteStateGaussianInput I))).map e =
          (stdGaussian (FiniteStateGaussianInput I)).prod
            (Measure.pi (fun _ : Fin N => stdGaussian (FiniteStateGaussianInput I))) := by
        simpa only [Fin.zero_succAbove] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (N+1) => stdGaussian (FiniteStateGaussianInput I)) 0).map_eq
      have hf : cavityLineGaussianCoordinates (I:=I) (N+1) =
          (Prod.map id (cavityLineGaussianCoordinates N)) ∘ e := by
        funext z
        rfl
      rw [hf, ←Measure.map_map (measurable_id.prodMap
        (measurable_cavityLineGaussianCoordinates N)) e.measurable, he,
        ←Measure.map_prod_map _ _ measurable_id (measurable_cavityLineGaussianCoordinates N),
        Measure.map_id, ih]

@[reducible] def cavityPosteriorLineRecord
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    (N : ℕ) → FiniteStateField S → ((Fin N → FiniteStateGaussianInput I) × S) →
      Records (FiniteStateField S) S (observationLinearTree N)
  | 0 => fun _ z => z.2
  | N+1 => fun H z =>
      (H + L N (z.1 0), cavityPosteriorLineRecord L N (H + L N (z.1 0)) (Fin.tail z.1,z.2))

theorem cavityPosteriorLineRecord_eq_reference
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) (z : (Fin N → FiniteStateGaussianInput I) × S) :
    cavityPosteriorLineRecord L N H z =
      finiteCascadeTreeReferenceRecord L (observationLinearTree N) H
        (cavityLineGaussianCoordinates N z.1,cavityLineTerminalEquiv (S:=S) N z.2) := by
  induction N generalizing H with
  | zero => rfl
  | succ N ih =>
      change (_, cavityPosteriorLineRecord L N _ _) = (_, finiteCascadeTreeReferenceRecord L _ _ _)
      rw [ih]

theorem measurable_cavityPosteriorLineRecord
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (N : ℕ) :
    Measurable (Function.uncurry (cavityPosteriorLineRecord L N)) := by
  have he : Function.uncurry (cavityPosteriorLineRecord L N) =
      Function.uncurry (finiteCascadeTreeReferenceRecord L (observationLinearTree N)) ∘
        (fun p => (p.1,(cavityLineGaussianCoordinates N p.2.1,cavityLineTerminalEquiv (S:=S) N p.2.2))) := by
    funext p
    exact cavityPosteriorLineRecord_eq_reference L N p.1 p.2
  rw [he]
  exact (measurable_finiteCascadeTreeReferenceRecord L _).comp
    (measurable_fst.prodMk
      (((measurable_cavityLineGaussianCoordinates N).comp
        (measurable_fst.comp measurable_snd)).prodMk
          ((cavityLineTerminalEquiv (S:=S) N).measurable.comp (measurable_snd.comp measurable_snd))))

theorem cavityPosteriorLineRecord_raw_law
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) :
    (cascadePosteriorGaussianBase S I N).map (cavityPosteriorLineRecord L N H) =
      finiteCascadeTreeReferenceKernel L (observationLinearTree N) H := by
  have he : cavityPosteriorLineRecord L N H =
      finiteCascadeTreeReferenceRecord L (observationLinearTree N) H ∘
        Prod.map (cavityLineGaussianCoordinates N) (cavityLineTerminalEquiv (S:=S) N) := by
    funext z
    exact cavityPosteriorLineRecord_eq_reference L N H z
  have hm : Measurable (finiteCascadeTreeReferenceRecord L (observationLinearTree N) H) :=
    (measurable_finiteCascadeTreeReferenceRecord L _).comp
      (show Measurable (fun z => (H,z)) from measurable_const.prodMk measurable_id)
  rw [he, ←Measure.map_map hm
    ((measurable_cavityLineGaussianCoordinates N).prodMap (cavityLineTerminalEquiv (S:=S) N).measurable)]
  unfold cascadePosteriorGaussianBase
  rw [←Measure.map_prod_map _ _ (measurable_cavityLineGaussianCoordinates N) (cavityLineTerminalEquiv (S:=S) N).measurable,
    cavityLineGaussianCoordinates_law, cavityLineTerminalEquiv_law]
  exact finiteCascadeTreeReferenceKernel_eq_gaussian_coordinates L _ H

end QuantitativeFollowup
