module
public import QuantitativeFollowup.FollowupCavityGeneratedForestMoments
public import QuantitativeFollowup.AnisotropicRecordedMovingLawConvergence
public import FourPapersCommon.FiniteObservationTerminalProjection
public import FourPapersCommon.ProbabilityIntegralContinuity
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

@[expose] public section

/-! Genuine level continuity of the complete independent forest law and
of its terminal-spin tests. This gives measurable mark integrals without
introducing a derivative or moment premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ} {I : Type*} [Fintype I]
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

instance cavityGeneratedForestRecord_opens (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) :
    OpensMeasurableSpace (CavityGeneratedForestRecord (n:=n) J T) := by
  haveI : ∀ i, SecondCountableTopology (AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) (T i)) :=
    fun i => inferInstance
  haveI : ∀ i, OpensMeasurableSpace (AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) (T i)) :=
    fun i => inferInstance
  unfold CavityGeneratedForestRecord
  infer_instance

abbrev CavityGeneratedForestTerminalSample (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) :=
  (i : I) → TerminalSpins (Configuration (n+1)) (T i)

def cavityGeneratedForestTerminalProjection (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) :
    CavityGeneratedForestRecord (n:=n) J T → CavityGeneratedForestTerminalSample (n:=n) J T :=
  fun z i => finiteCascadeRecordTerminalSpins (T i) (z i).2

theorem measurable_cavityGeneratedForestTerminalProjection (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) :
    Measurable (cavityGeneratedForestTerminalProjection (n:=n) J T) := by
  exact Measurable.of_eval fun i =>
    ((measurable_finiteCascadeRecordTerminalSpins (T i)).comp measurable_snd).comp
      (measurable_pi_apply i)

theorem continuous_cavityGeneratedForestTerminalProjection (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) :
    Continuous (cavityGeneratedForestTerminalProjection (n:=n) J T) := by
  exact continuous_pi fun i =>
    ((continuous_finiteCascadeRecordTerminalSpins (T i)).comp continuous_snd).comp
      (continuous_apply i)

def cavityGeneratedNativeForestProbability (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap) :
    ProbabilityMeasure (CavityGeneratedForestRecord (n:=n) J T) :=
  ProbabilityMeasure.pi (fun i => anisotropicRecordedProfileProbability D μ a (q i) (T i))

def cavityGeneratedNativeForestTerminalProbability (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap) :
    ProbabilityMeasure (CavityGeneratedForestTerminalSample (n:=n) J T) :=
  (cavityGeneratedNativeForestProbability D μ a J T q).map
    (cavityGeneratedForestTerminalProjection J T)

theorem cavityGeneratedNativeForest_integral_terminal (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (f : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ) :
    (∫ z, f (cavityGeneratedForestTerminalProjection J T z)
      ∂cavityGeneratedNativeForestLaw D μ a J T q) =
    ∫ σ, f σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _) := by
  exact (integral_map (measurable_cavityGeneratedForestTerminalProjection J T).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable).symm

theorem continuous_cavityGeneratedNativeForestProbability_family
    {H : Type*} [TopologicalSpace H] [FirstCountableTopology H]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : H → I → ℕ → Paper.Overlap)
    (hcts : ∀i p, p ≤ J i → Continuous (fun h => q h i p))
    (hmono : ∀h i p, p < J i → q h i (p+1) ≤ q h i p) :
    Continuous (fun h => cavityGeneratedNativeForestProbability D μ a J T (q h)) := by
  have hc (i : I) : Continuous
      (fun h => anisotropicRecordedProfileProbability D μ a (q h i) (T i)) := by
    apply continuous_iff_continuousAt.mpr
    intro h
    exact tendsto_anisotropicRecordedProfileProbability_moving_schedule D
      (tendsto_const_nhds (x:=μ)) a (fun z => q z i) (q h i) (T i)
      (fun p hp => (hcts i p hp).continuousAt) (fun z => hmono z i) (hmono h i)
  exact ProbabilityMeasure.continuous_pi.comp (continuous_pi hc)

theorem continuous_cavityGeneratedNativeForestTerminalProbability_family
    {H : Type*} [TopologicalSpace H] [FirstCountableTopology H]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : H → I → ℕ → Paper.Overlap)
    (hcts : ∀i p, p ≤ J i → Continuous (fun h => q h i p))
    (hmono : ∀h i p, p < J i → q h i (p+1) ≤ q h i p) :
    Continuous (fun h => cavityGeneratedNativeForestTerminalProbability D μ a J T (q h)) := by
  exact (ProbabilityMeasure.continuous_map
    (continuous_cavityGeneratedForestTerminalProjection J T)).comp
      (continuous_cavityGeneratedNativeForestProbability_family D μ a J T q hcts hmono)

end QuantitativeFollowup
