module
public import FourPapersCommon.FiniteStateCascadePosteriorDensity
public import FourPapersCommon.FiniteStateGaussianCoordinateSpinLaw
public import FourPapersCommon.HistoryBackwardPrefix

@[expose] public section

/-! A genuine posterior history retaining the last raw Gaussian input.
The field projection need not be injective: zero and singular covariance
maps retain their input coordinates in the second component. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
set_option maxHeartbeats 1200000

abbrev PosteriorCoordinateState (S I : Type*) [Fintype S] [Fintype I] :=
  FiniteStateField S × FiniteStateGaussianInput I

def posteriorCoordinateUpdate
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ)
    (p : PosteriorCoordinateState S I) (z : FiniteStateGaussianInput I) :
    PosteriorCoordinateState S I := (p.1+L (N-1-i) z,z)

theorem measurable_posteriorCoordinateUpdate
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ) :
    Measurable (Function.uncurry (posteriorCoordinateUpdate L N i)) := by
  unfold posteriorCoordinateUpdate
  fun_prop

def posteriorCoordinateRawKernel
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ) :
    Kernel (PosteriorCoordinateState S I) (PosteriorCoordinateState S I) :=
  ((Kernel.id : Kernel (PosteriorCoordinateState S I) (PosteriorCoordinateState S I)) ×ₖ
    Kernel.const (PosteriorCoordinateState S I) (stdGaussian (FiniteStateGaussianInput I))).map
    (Function.uncurry (posteriorCoordinateUpdate L N i))

instance posteriorCoordinateRawKernel_markov
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ) :
    IsMarkovKernel (posteriorCoordinateRawKernel L N i) := by
  unfold posteriorCoordinateRawKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_posteriorCoordinateUpdate L N i)

theorem posteriorCoordinateRawKernel_apply
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ)
    (p : PosteriorCoordinateState S I) :
    posteriorCoordinateRawKernel L N i p =
      (stdGaussian (FiniteStateGaussianInput I)).map (posteriorCoordinateUpdate L N i p) := by
  rw [posteriorCoordinateRawKernel,Kernel.map_apply _ (measurable_posteriorCoordinateUpdate L N i),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (measurable_posteriorCoordinateUpdate L N i) measurable_prodMk_left]
  rfl

def posteriorCoordinateWeight (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ)
    (p q : PosteriorCoordinateState S I) : ℝ≥0∞ :=
  cascadePosteriorTransitionWeight V a L N i p.1 q.1

theorem measurable_posteriorCoordinateWeight (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ) :
    Measurable (Function.uncurry (posteriorCoordinateWeight V a L N i)) :=
  (measurable_cascadePosteriorTransitionWeight V a ha L N i).comp
    (measurable_fst.prodMap measurable_fst)

def posteriorCoordinateKernel (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ) :=
  (posteriorCoordinateRawKernel L N i).withDensity (posteriorCoordinateWeight V a L N i)

theorem posteriorCoordinateKernel_apply (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ)
    (p : PosteriorCoordinateState S I) :
    posteriorCoordinateKernel V a L N i p =
      ((stdGaussian (FiniteStateGaussianInput I)).tilted
        (fun z=>a (N-1-i)*finiteStateGaussianTerminalCascade V a L (N-1-i)
          (p.1+L (N-1-i) z))).map (posteriorCoordinateUpdate L N i p) := by
  have hu : Measurable (posteriorCoordinateUpdate L N i p) := by
    exact (measurable_posteriorCoordinateUpdate L N i).comp
      (measurable_const.prodMk measurable_id)
  have hw : Measurable (posteriorCoordinateWeight V a L N i p) :=
    (measurable_posteriorCoordinateWeight V a ha L N i).comp
    (measurable_const.prodMk measurable_id)
  rw [posteriorCoordinateKernel,Kernel.withDensity_apply _
    (measurable_posteriorCoordinateWeight V a ha L N i),posteriorCoordinateRawKernel_apply]
  rw [Measure.tilted,←map_withDensity_pullback _ _ hu _ hw]
  congr 2
  funext z
  unfold posteriorCoordinateWeight cascadePosteriorTransitionWeight posteriorCoordinateUpdate
  rw [finiteStateGaussianNormalizer,finiteStateGaussianRawKernel_apply,
    integral_map (by fun_prop)
      (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-1-i)).continuous.measurable.const_mul _).exp.aestronglyMeasurable)]

theorem posteriorCoordinateKernel_markov (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ) :
    IsMarkovKernel (posteriorCoordinateKernel V a L N i) := by
  constructor
  intro p
  rw [posteriorCoordinateKernel_apply V a ha L]
  haveI := isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
    _ (finiteStateGaussianTerminalCascade_lipschitz V a ha L (N-1-i)) (L (N-1-i)) p.1 (a (N-1-i)))
  exact (Measure.isProbabilityMeasure_map_iff
    ((measurable_posteriorCoordinateUpdate L N i).comp
      (measurable_const.prodMk measurable_id)).aemeasurable).mpr inferInstance

def posteriorCoordinateHistory
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) (z : Fin N→FiniteStateGaussianInput I) :
    FiniteHistory (PosteriorCoordinateState S I) N :=
  independentHistory (posteriorCoordinateUpdate L N) N ((H,0),z)

theorem measurable_posteriorCoordinateHistory
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) : Measurable (posteriorCoordinateHistory L N H) :=
  (measurable_independentHistory _ (measurable_posteriorCoordinateUpdate L N) N).comp
    (measurable_const.prodMk measurable_id)

end FourPapersCommon
