module
public import QuantitativeFollowup.AnisotropicVarianceNoiseRestart
public import QuantitativeFollowup.AnisotropicTerminalFeatures
public import FourPapersCommon.IndependentNoiseKernel
public import FourPapersCommon.FiniteCascadeTreeRecords

@[expose] public section

/-! Actual finite observation genealogies for an arbitrary Parisi profile.
Every edge uses fresh continuous Wiener noise and the actual restarted
Picard state; forks use a genuine product of the continuation kernels.
The observation schedule is fixed independently of any finite approximation.
Fields below are whitened fields; their physical parameter is identified
explicitly by `anisotropicObservationParameter`. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 128
variable {n : ℕ}

abbrev AnisotropicObservationState (n : ℕ) := AnisotropicDisorder n×Field n

def anisotropicObservationParameter (D : AnisotropicSpinModel n)
    (z : AnisotropicObservationState n) : AnisotropicParameter n :=
  anisotropicDisorderInjection n z.1+anisotropicUnitInput D z.2

theorem measurable_anisotropicObservationParameter (D : AnisotropicSpinModel n) :
    Measurable (anisotropicObservationParameter D) :=
  ((anisotropicDisorderInjection n).measurable.comp measurable_fst).add
    ((anisotropicUnitInput D).measurable.comp measurable_snd)

def anisotropicObservationNoiseAdvance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap)
    (z : AnisotropicObservationState n×VectorWienerPath n) : AnisotropicObservationState n :=
  (z.1.1,anisotropicRestartNoiseStatePath D μ q z ((r:ℝ)-(q:ℝ)))

theorem measurable_anisotropicObservationNoiseAdvance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) :
    Measurable (anisotropicObservationNoiseAdvance D μ q r) := by
  have ht : Measurable (fun z : AnisotropicObservationState n×VectorWienerPath n=>
      (((r:ℝ)-(q:ℝ)),z)) := measurable_const.prodMk measurable_id
  have hX := (measurable_uncurry_anisotropicRestartNoiseStatePath D μ q).comp ht
  have hg : Measurable (fun z : AnisotropicObservationState n×VectorWienerPath n=>z.1.1) :=
    measurable_fst.fst
  have hpair:=hg.prodMk hX
  convert hpair using 1
  rfl

def anisotropicObservationTransition (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) :
    Kernel (AnisotropicObservationState n) (AnisotropicObservationState n) :=
  independentNoiseKernel (vectorWienerMeasure n) (anisotropicObservationNoiseAdvance D μ q r)

instance anisotropicObservationTransition_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) :
    IsMarkovKernel (anisotropicObservationTransition D μ q r) :=
  isMarkovKernel_independentNoiseKernel _ _ (measurable_anisotropicObservationNoiseAdvance D μ q r)

theorem anisotropicObservationTransition_apply (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (z : AnisotropicObservationState n) :
    anisotropicObservationTransition D μ q r z=(vectorWienerMeasure n).map
      (fun W=>(z.1,anisotropicRestartNoiseStatePath D μ q (z,W) ((r:ℝ)-(q:ℝ)))) :=
  independentNoiseKernel_apply _ _ (measurable_anisotropicObservationNoiseAdvance D μ q r) z

@[reducible] def anisotropicRecordedProfileTreeKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) :
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→
      Kernel (AnisotropicObservationState n) (Records (AnisotropicObservationState n) (Configuration n) T)
  | _, .leaf => (anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
      (measurable_anisotropicObservationParameter D)
  | _, @FiniteTerminalGenealogy.advance j T =>
      (Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
        anisotropicObservationTransition D μ (q (j+1)) (q j)
  | _, .fork T U =>
      anisotropicRecordedProfileTreeKernel D μ q T ×ₖ anisotropicRecordedProfileTreeKernel D μ q U

instance anisotropicRecordedProfileTreeKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsMarkovKernel (anisotropicRecordedProfileTreeKernel D μ q T) := by
  induction T with
  | leaf => change IsMarkovKernel ((anisotropicTerminalSpinKernel D).comap _ _);infer_instance
  | advance T ih =>
      haveI:=ih
      change IsMarkovKernel ((_ ×ₖ _) ∘ₖ _)
      infer_instance
  | fork T U ihT ihU =>
      haveI:=ihT
      haveI:=ihU
      change IsMarkovKernel (_ ×ₖ _)
      infer_instance

/-- Disorder is sampled once from the actual tilted Gaussian law. -/
def anisotropicObservationInitialLaw (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : Measure (AnisotropicObservationState n) :=
  (anisotropicMeasureOuterLaw D μ a).map (fun g=>(g,(0:Field n)))

instance anisotropicObservationInitialLaw_probability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : IsProbabilityMeasure (anisotropicObservationInitialLaw D μ a) := by
  unfold anisotropicObservationInitialLaw
  exact (Measure.isProbabilityMeasure_map_iff (measurable_id.prodMk measurable_const).aemeasurable).mpr inferInstance

/-- Full field and terminal-spin records, including the initial disorder. -/
def anisotropicRecordedProfileTreeLaw (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measure (AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T) :=
  anisotropicObservationInitialLaw D μ a ⊗ₘ anisotropicRecordedProfileTreeKernel D μ q T

instance anisotropicRecordedProfileTreeLaw_probability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsProbabilityMeasure (anisotropicRecordedProfileTreeLaw D μ a q T) := by
  unfold anisotropicRecordedProfileTreeLaw
  infer_instance

theorem anisotropicRecordedProfileTreeLaw_initial (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (anisotropicRecordedProfileTreeLaw D μ a q T).fst=anisotropicObservationInitialLaw D μ a :=
  Measure.fst_compProd _ _

end QuantitativeFollowup
