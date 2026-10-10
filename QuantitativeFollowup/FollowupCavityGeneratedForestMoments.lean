module
public import QuantitativeFollowup.FollowupCavityPairCubic
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! Three physical defects in a finite forest of genuinely independent
native recorded trees. Pair deletion is proved on each actual component;
the forest's unused components integrate to one. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ} {I : Type*} [Fintype I]
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

abbrev CavityGeneratedForestRecord (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) :=
  (i : I) → AnisotropicObservationState (n+1) ×
    Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) (T i)

def cavityGeneratedNativeForestLaw (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap) :
    Measure (CavityGeneratedForestRecord (n:=n) J T) :=
  Measure.pi (fun i => anisotropicRecordedProfileTreeLaw D μ a (q i) (T i))

instance cavityGeneratedNativeForestLaw_probability (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap) :
    IsProbabilityMeasure (cavityGeneratedNativeForestLaw D μ a J T q) := by
  unfold cavityGeneratedNativeForestLaw
  infer_instance

theorem cavityGeneratedNativeForestLaw_component (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap) (c : I) :
    (cavityGeneratedNativeForestLaw D μ a J T q).map (Function.eval c) =
      anisotropicRecordedProfileTreeLaw D μ a (q c) (T c) := by
  exact (measurePreserving_eval
    (fun i => anisotropicRecordedProfileTreeLaw D μ a (q i) (T i)) c).map_eq

theorem cavityGeneratedNativeForest_pair_cubic_eq (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (hzero : ∀i, q i 0 = 1) (hroot : ∀i, q i (J i) = 0)
    (hq : ∀i l, l < J i → q i (l+1) ≤ q i l)
    (c : I) (b e : ObservationLeaf (T c)) (hbe : b ≠ e) :
    (∫ z, |cavityRestOverlap n (observationLeafSpin (T c) b (z c).2)
      (observationLeafSpin (T c) e (z c).2) -
        (q c (observationCommonLevel (T c) b e) : ℝ)|^3
      ∂cavityGeneratedNativeForestLaw D μ a J T q) =
      cavityCubicPairMoment D μ a (q c (observationCommonLevel (T c) b e)) := by
  let f : (AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) (T c)) → ℝ :=
    fun z => |cavityRestOverlap n (observationLeafSpin (T c) b z.2)
      (observationLeafSpin (T c) e z.2) -
        (q c (observationCommonLevel (T c) b e) : ℝ)|^3
  have hf : Measurable f := by
    exact (((measurable_of_finite (Function.uncurry (cavityRestOverlap n))).comp
      (((measurable_observationLeafSpin (T c) b).comp measurable_snd).prodMk
        ((measurable_observationLeafSpin (T c) e).comp measurable_snd))).sub
      measurable_const).abs.pow_const 3
  have he := integral_map (μ:=cavityGeneratedNativeForestLaw D μ a J T q)
    (measurable_pi_apply c).aemeasurable hf.aestronglyMeasurable
  rw [cavityGeneratedNativeForestLaw_component D μ a J T q c] at he
  exact he.symm.trans (cavityRecorded_leafPair_cubic_eq D μ a (q c)
    (hzero c) (T c) (hroot c) (hq c) b e hbe)

theorem cavityGeneratedNativeForest_three_defects_le (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (hzero : ∀i, q i 0 = 1) (hroot : ∀i, q i (J i) = 0)
    (hq : ∀i l, l < J i → q i (l+1) ≤ q i l)
    (c : Fin 3 → I) (b e : (r : Fin 3) → ObservationLeaf (T (c r)))
    (hbe : ∀r, b r ≠ e r) :
    (∫ z, |cavitySpinOverlapDefect n (q (c 0) (observationCommonLevel (T (c 0)) (b 0) (e 0)))
        (observationLeafSpin (T (c 0)) (b 0) (z (c 0)).2)
        (observationLeafSpin (T (c 0)) (e 0) (z (c 0)).2) *
      cavitySpinOverlapDefect n (q (c 1) (observationCommonLevel (T (c 1)) (b 1) (e 1)))
        (observationLeafSpin (T (c 1)) (b 1) (z (c 1)).2)
        (observationLeafSpin (T (c 1)) (e 1) (z (c 1)).2) *
      cavitySpinOverlapDefect n (q (c 2) (observationCommonLevel (T (c 2)) (b 2) (e 2)))
        (observationLeafSpin (T (c 2)) (b 2) (z (c 2)).2)
        (observationLeafSpin (T (c 2)) (e 2) (z (c 2)).2)|
      ∂cavityGeneratedNativeForestLaw D μ a J T q) ≤
    (cavityCubicPairMoment D μ a (q (c 0) (observationCommonLevel (T (c 0)) (b 0) (e 0))) +
      cavityCubicPairMoment D μ a (q (c 1) (observationCommonLevel (T (c 1)) (b 1) (e 1))) +
      cavityCubicPairMoment D μ a (q (c 2) (observationCommonLevel (T (c 2)) (b 2) (e 2)))) / 3 := by
  have hh := integral_cavityThreeDefectProduct_le_cubic_moments
    (cavityGeneratedNativeForestLaw D μ a J T q) n
    (fun r _ => q (c r) (observationCommonLevel (T (c r)) (b r) (e r)))
    (fun _ => measurable_const)
    (fun r z => observationLeafSpin (T (c r)) (b r) (z (c r)).2)
    (fun r z => observationLeafSpin (T (c r)) (e r) (z (c r)).2)
    (fun r => ((measurable_observationLeafSpin (T (c r)) (b r)).comp
      measurable_snd).comp (measurable_pi_apply (c r)))
    (fun r => ((measurable_observationLeafSpin (T (c r)) (e r)).comp
      measurable_snd).comp (measurable_pi_apply (c r)))
  rw [cavityGeneratedNativeForest_pair_cubic_eq D μ a J T q hzero hroot hq
      (c 0) (b 0) (e 0) (hbe 0),
    cavityGeneratedNativeForest_pair_cubic_eq D μ a J T q hzero hroot hq
      (c 1) (b 1) (e 1) (hbe 1),
    cavityGeneratedNativeForest_pair_cubic_eq D μ a J T q hzero hroot hq
      (c 2) (b 2) (e 2) (hbe 2)] at hh
  exact hh

end QuantitativeFollowup
