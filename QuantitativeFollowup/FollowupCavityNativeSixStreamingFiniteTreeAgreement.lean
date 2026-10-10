module
public import QuantitativeFollowup.AnisotropicRecordedProfileFiniteTree
public import FourPapersCommon.FiniteObservationTreeLeafPruning
public import FourPapersCommon.FiniteCascadeContinuationGraft

@[expose] public section

/-! Scheme agreement for retained trees of any permitted depth. The
initial tilt remains the actual full-scheme tilt, independently of the
retained tree depth. Linear native continuations are the genuine finite
single-mark graft continuations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def nativeStreamingFiniteRecordedPrefixLaw (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j) :=
  ((anisotropicFiniteInitialLaw D s a).map (anisotropicEnergyMap D)) ⊗ₘ
    finiteCascadeTreeRecordKernel (fun _ : Configuration n => 0) (anisotropicSchemeMass s)
      (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) T

theorem nativeStreamingRecordedProfileLaw_scheme_energy_prefix
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j ≤ k+2) :
    (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T).map
        (Prod.map (anisotropicObservationEnergy D)
          (observationTreeMap (anisotropicObservationEnergy D) T)) =
      nativeStreamingFiniteRecordedPrefixLaw D s a T := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) T
  rw [anisotropicRecordedProfileTreeLaw,
    observationJointLaw_map T _ _ _ (anisotropicObservationEnergy D)
      (measurable_anisotropicObservationEnergy D)
      (anisotropicRecordedProfileTreeKernel_scheme_energy D s T hj),
    anisotropicObservationInitialLaw_scheme_energy]
  rfl

theorem nativeStreamingFiniteRecordedPrefixLaw_full
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) :
    nativeStreamingFiniteRecordedPrefixLaw D s a T =
      anisotropicFiniteRecordedTreeLaw D s a T := by
  unfold nativeStreamingFiniteRecordedPrefixLaw
  rw [anisotropicFiniteInitialLaw_energy]
  rfl

theorem nativeStreamingObservationTreeMap_spins {E F S : Type}
    (f : E → F) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : Records E S T) :
    spins T (observationTreeMap f T z) = spins T z := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih z.2
  | fork T U ihT ihU => exact Prod.ext (ihT z.1) (ihU z.2)

theorem nativeStreamingRecordedProfileLaw_scheme_prefix_spins
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j ≤ k+2) :
    (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T).map (fun z => spins T z.2) =
      (nativeStreamingFiniteRecordedPrefixLaw D s a T).map (fun z => spins T z.2) := by
  have he := congrArg (fun P : Measure (FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) T) =>
      P.map (fun z => spins T z.2))
    (nativeStreamingRecordedProfileLaw_scheme_energy_prefix D s a T hj)
  have hm : Measurable (fun z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) T => spins T z.2) :=
    (measurable_spins T).comp measurable_snd
  rw [Measure.map_map hm
    ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) T))] at he
  simpa only [Function.comp_def, Prod.map_apply', Prod.map_snd,
    nativeStreamingObservationTreeMap_spins] using he

theorem nativeStreamingRecordedProfileLaw_scheme_full_spins
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) :
    (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T).map (fun z => spins T z.2) =
      anisotropicFiniteTreeLaw D s a (asGenealogy T) := by
  rw [nativeStreamingRecordedProfileLaw_scheme_prefix_spins D s a T le_rfl,
    nativeStreamingFiniteRecordedPrefixLaw_full,
    anisotropicFiniteRecordedTreeLaw_spin_marginal]

theorem nativeStreamingLinearTree_eq_finite_linear (j : ℕ) :
    observationLinearTree j = finiteCascadeLinearTerminalTree j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg FiniteTerminalGenealogy.advance ih

theorem nativeStreamingContinuationGraft_eq_vertexGraft
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    finiteCascadeContinuationGraft observationLinearTree v = finiteCascadeVertexGraft v := by
  induction v with
  | root T =>
      exact congrArg (FiniteTerminalGenealogy.fork T)
        (nativeStreamingLinearTree_eq_finite_linear _)
  | child v ih => exact congrArg FiniteTerminalGenealogy.advance ih
  | left v ih => exact congrArg (fun U => FiniteTerminalGenealogy.fork U _) ih
  | right v ih => exact congrArg (fun U => FiniteTerminalGenealogy.fork _ U) ih

end QuantitativeFollowup
