module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingNormalizerDefectIntegral

@[expose] public section

/-! The independent normalizer is a second actual native terminal tree.
The tree has fixed depth two, its clock is (1,l,0), and its terminal test
depends only on n and l. Equal endpoint clocks retain two Gibbs draws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def nativeStreamingNormalizerBinaryTerminalTest (n : ℕ) (l : Paper.Overlap) :
    TerminalSpins (Configuration (n+1)) anisotropicBinaryObservationTree → ℝ :=
  fun σ => cavitySpinOverlapDefect n l σ.1 σ.2

theorem nativeStreamingNormalizerBinaryTerminalTest_record (n : ℕ) (l : Paper.Overlap)
    (z : Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
      anisotropicBinaryObservationTree) :
    nativeStreamingNormalizerBinaryTerminalTest n l
      (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree z) =
      cavitySpinOverlapDefect n l (anisotropicBinaryObservationSpins z).1
        (anisotropicBinaryObservationSpins z).2 := rfl

theorem nativeStreamingNormalizer_binary_terminal_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (l : Paper.Overlap) :
    (anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule l)
      anisotropicBinaryObservationTree).map
      (fun z => finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree z.2) =
      (anisotropicFreshTerminalPairLaw D μ a l).snd := by
  change (anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule l)
    anisotropicBinaryObservationTree).map (anisotropicBinaryObservationSpins ∘ Prod.snd) = _
  exact anisotropicBinaryObservationTree_spin_law D μ a l

theorem nativeStreamingNormalizer_binary_eq_freshDefectMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (l : Paper.Overlap) :
    nativeStreamingOldTerminalExpectation D μ a (anisotropicBinaryObservationSchedule l)
      anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n l) =
      nativeStreamingFreshDefectMoment D μ a l := by
  let f : Configuration (n+1) × Configuration (n+1) → ℝ :=
    fun σ => cavitySpinOverlapDefect n l σ.1 σ.2
  have h := integral_map_of_stronglyMeasurable
    (μ := anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule l)
      anisotropicBinaryObservationTree)
    (measurable_anisotropicBinaryObservationSpins.comp measurable_snd)
    (measurable_of_finite f).stronglyMeasurable
  rw [anisotropicBinaryObservationTree_spin_law] at h
  rw [nativeStreamingFreshDefectMoment,anisotropicBinarySpinProbability_eq_fresh_pair]
  change (∫z, f (anisotropicBinaryObservationSpins z.2)
    ∂anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule l)
      anisotropicBinaryObservationTree) = _
  simpa only [Function.comp_apply,f] using h.symm

theorem nativeStreamingNormalizer_binary_terminal_expectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (l : Paper.Overlap) :
    nativeStreamingOldTerminalExpectation D μ a (anisotropicBinaryObservationSchedule l)
      anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n l) =
      ∫z, cavitySpinOverlapDefect n l z.2.1 z.2.2
        ∂anisotropicFreshTerminalPairLaw D μ a l :=
  (nativeStreamingNormalizer_binary_eq_freshDefectMoment D μ a l).trans
    (nativeStreamingFreshDefectMoment_eq_fresh D μ a l)

theorem nativeStreamingPatternMoment_normalizer_eq_terminal_product
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (l : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.normalizer l) =
      nativeStreamingOldTerminalExpectation D μ a q T F *
        nativeStreamingOldTerminalExpectation D μ a (anisotropicBinaryObservationSchedule l)
          anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n l) := by
  rw [nativeStreamingPatternMoment_normalizer_independent,
    ←nativeStreamingNormalizer_binary_terminal_expectation D μ a l]

theorem nativeStreamingPatternMoment_normalizer_eq_independent_terminal_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (l : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.normalizer l) =
      ∫z, F (finiteCascadeRecordTerminalSpins T z.1.2) *
        nativeStreamingNormalizerBinaryTerminalTest n l
          (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree z.2.2)
        ∂(anisotropicRecordedProfileTreeLaw D μ a q T).prod
          (anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule l)
            anisotropicBinaryObservationTree) := by
  rw [nativeStreamingPatternMoment_normalizer_eq_terminal_product]
  exact (integral_prod_mul
    (μ := anisotropicRecordedProfileTreeLaw D μ a q T)
    (ν := anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule l)
      anisotropicBinaryObservationTree)
    (fun z => F (finiteCascadeRecordTerminalSpins T z.2))
    (fun z => nativeStreamingNormalizerBinaryTerminalTest n l
      (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree z.2))).symm

theorem nativeStreamingSourceNormalizerTerm_eq_binary_terminal_product
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingSourceNormalizerTerm D μ a q T F =
      a*nativeStreamingOldTerminalExpectation D μ a q T F *
        (∫l, nativeStreamingOldTerminalExpectation D μ a
          (anisotropicBinaryObservationSchedule l) anisotropicBinaryObservationTree
          (nativeStreamingNormalizerBinaryTerminalTest n l) ∂parisiFreeMeasure μ a) := by
  rw [nativeStreamingSourceNormalizerTerm_eq_independent]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun l => (nativeStreamingNormalizer_binary_terminal_expectation D μ a l).symm

end QuantitativeFollowup
