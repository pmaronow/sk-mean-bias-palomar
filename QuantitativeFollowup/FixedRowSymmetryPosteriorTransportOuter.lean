module
public import QuantitativeFollowup.FixedRowSymmetryPosteriorTransportDensity
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterMean
public import FourPapersCommon.TiltedPushforward

@[expose] public section

/-! The genuine outer Gaussian posterior pushes to the entire normalized
retained line. Each remaining-depth field observable is therefore exactly
the corresponding affine-coordinate posterior mean. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency false

variable {S J : Type} [Fintype S] [Fintype J] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}

def cavityOuterPosteriorLineRecord
    (L : ℕ → QuantitativePaper.Field n →L[ℝ] FiniteStateField S) (N : ℕ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (p : FiniteStateGaussianInput J × ((Fin N → QuantitativePaper.Field n) × S)) :
    FiniteStateField S × Records (FiniteStateField S) S (observationLinearTree N) :=
  (H+R p.1,cavityPosteriorLineRecord L N (H+R p.1) p.2)

theorem measurable_cavityOuterPosteriorLineRecord
    (L : ℕ → QuantitativePaper.Field n →L[ℝ] FiniteStateField S) (N : ℕ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    Measurable (cavityOuterPosteriorLineRecord L N R H) := by
  have hh : Measurable (fun p : FiniteStateGaussianInput J ×
      ((Fin N → QuantitativePaper.Field n) × S) => H+R p.1) := by fun_prop
  exact hh.prodMk ((measurable_cavityPosteriorLineRecord L N).comp
    (hh.prodMk measurable_snd))

theorem cavityOuterPosteriorLaw_map_lineRecord
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀j,0≤a j)
    (L : ℕ → QuantitativePaper.Field n →L[ℝ] FiniteStateField S)
    (s : ℝ) (N : ℕ) (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) :
    (cavityOuterPosteriorLaw V a L s N R H).map (cavityOuterPosteriorLineRecord L N R H) =
      finiteCascadeTreeGaussianJointLaw V a L s (observationLinearTree N) R H := by
  haveI := cavityPosteriorGaussianKernel_markov V a ha L N
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (observationLinearTree N)
  haveI := isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
    (finiteStateGaussianTerminalCascade V a L N)
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) R H s)
  let Q : FiniteStateGaussianInput J → FiniteStateField S := fun g => H+R g
  have hQ : Measurable Q := by fun_prop
  have hm := measurable_cavityOuterPosteriorLineRecord L N R H
  have hroot : ((stdGaussian (FiniteStateGaussianInput J)).tilted
      (fun g => s*finiteStateGaussianTerminalCascade V a L N (Q g))).map Q =
      (finiteStateGaussianRawKernel R H).tilted
        (fun y => s*finiteStateGaussianTerminalCascade V a L N y) := by
    have h := map_tilted_pullback (stdGaussian (FiniteStateGaussianInput J)) Q hQ
      (fun y => s*finiteStateGaussianTerminalCascade V a L N y)
      ((contDiff_one_finiteStateGaussianTerminalCascade V a ha L N).continuous.measurable.const_mul s)
    simpa only [Q,Function.comp_def,finiteStateGaussianRawKernel_apply] using h
  ext B hB
  rw [Measure.map_apply hm hB]
  unfold cavityOuterPosteriorLaw finiteCascadeTreeGaussianJointLaw
  rw [Measure.compProd_apply (hB.preimage hm), ←hroot, Measure.compProd_apply hB,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hB) hQ]
  apply lintegral_congr
  intro g
  rw [Kernel.comap_apply, cavityPosteriorGaussianKernel_apply V a ha L N,
    ←cavityPosteriorGaussianLaw_map_lineRecord V a ha L N (Q g)]
  have hline : Measurable (cavityPosteriorLineRecord L N (Q g)) :=
    (measurable_cavityPosteriorLineRecord L N).comp
      (show Measurable (fun z => (Q g,z)) from measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hline (hB.preimage measurable_prodMk_left)]
  rfl

theorem cavityFixedRowLineField_outerPosterior_eq
    (L : ℕ → QuantitativePaper.Field n →L[ℝ] FiniteStateField S)
    (N d : ℕ) (hd : d ≤ N)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (p : FiniteStateGaussianInput J × ((Fin N → QuantitativePaper.Field n) × S)) :
    cavityFixedRowLineField N d (cavityOuterPosteriorLineRecord L N R H p).1
        (cavityOuterPosteriorLineRecord L N R H p).2 =
      H+R p.1+cavityPosteriorLineFieldLinear L N d p.2.1 :=
  cavityPosteriorLineRecord_field_affine L N d hd (H+R p.1) p.2.1 p.2.2

theorem cavityOuterPosteriorMean_eq_lineField_integral
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀j,0≤a j)
    (L : ℕ → QuantitativePaper.Field n →L[ℝ] FiniteStateField S)
    (s : ℝ) (N d : ℕ) (hd : d ≤ N)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (f : FiniteStateField S → ℝ) (hf : Measurable f) (H : FiniteStateField S) :
    cavityOuterPosteriorMean V a L s N R f (cavityPosteriorLineFieldLinear L N d) H =
      ∫ z, f (cavityFixedRowLineField N d z.1 z.2)
        ∂finiteCascadeTreeGaussianJointLaw V a L s (observationLinearTree N) R H := by
  rw [←cavityOuterPosteriorLaw_map_lineRecord V a ha L s N R H]
  have hobs : Measurable (fun z : FiniteStateField S ×
      Records (FiniteStateField S) S (observationLinearTree N) =>
        f (cavityFixedRowLineField N d z.1 z.2)) :=
    hf.comp (measurable_cavityFixedRowLineField N d)
  rw [integral_map (measurable_cavityOuterPosteriorLineRecord L N R H).aemeasurable
    hobs.aestronglyMeasurable]
  simp only [cavityFixedRowLineField_outerPosterior_eq L N d hd,
    cavityOuterPosteriorMean]

end QuantitativeFollowup
