module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairFamilyMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingNormalizerDefectIntegral

@[expose] public section

/-! Actual pattern values inherit the old terminal-test bound. Every
marked law is a probability, and the normalizer remains a product of
independent actual expectations. The original diagonal stays zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem abs_nativeStreamingOldTerminalExpectation_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hF : ∀σ, |F σ| ≤ C) :
    |nativeStreamingOldTerminalExpectation D μ a q T F| ≤ C := by
  simpa only [nativeStreamingOldTerminalExpectation,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ := anisotropicRecordedProfileTreeLaw D μ a q T)
      (f := fun z => F (finiteCascadeRecordTerminalSpins T z.2)) (C := C)
      (.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using (hF (finiteCascadeRecordTerminalSpins T z.2)))

theorem abs_nativeStreamingPatternMoment_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C)
    (P : NativeStreamingAttachmentPattern T) :
    |nativeStreamingPatternMoment D μ a q T F P| ≤ 2*C := by
  classical
  cases P with
  | original i k =>
      by_cases hik : i=k
      · simp only [nativeStreamingPatternMoment,hik,ite_true,abs_zero]
        exact mul_nonneg (by norm_num) hC
      · simp only [nativeStreamingPatternMoment,if_neg hik]
        simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
          norm_integral_le_of_norm_le_const
            (μ := anisotropicRecordedProfileTreeLaw D μ a q T)
            (f := fun z => F (finiteCascadeRecordTerminalSpins T z.2) *
              cavitySpinOverlapDefect n (q (observationCommonLevel T i k))
                (observationLeafSpin T i z.2) (observationLeafSpin T k z.2))
            (C := 2*C) (.of_forall fun z => by
              simpa only [Real.norm_eq_abs,nativeStreamingDefectSpinTest] using
                nativeStreamingDefectSpinTest_abs_le T F C hC hF
                  (q (observationCommonLevel T i k))
                  (finiteCascadeRecordTerminalSpins T z.2,
                    (observationLeafSpin T i z.2,observationLeafSpin T k z.2)))
  | originalFresh i o =>
      let G := nativeStreamingOriginalFreshSpinTest T F i
        (nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i)) o)
      simpa only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,
        Real.norm_eq_abs,probReal_univ,mul_one,G] using
        norm_integral_le_of_norm_le_const
          (μ := (nativeStreamingOriginSingleProbability D μ a q T o :
            Measure ((AnisotropicObservationState (n+1) ×
              Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
                Configuration (n+1))))
          (f := fun z => G (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
          (C := 2*C) (.of_forall fun z => by
            simpa only [Real.norm_eq_abs,G] using
              nativeStreamingOriginalFreshSpinTest_abs_le T F C hC hF i
                (nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i)) o)
                (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
  | cross o p =>
      exact nativeStreamingTerminalMarkMoment_abs_le_bound
        (nativeStreamingOriginCrossProbability D μ a q T o p)
        (nativeStreamingDefectSpinTest T F (nativeStreamingOriginCommonClock q T o p))
        (2*C) (fun σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
  | current o =>
      exact nativeStreamingTerminalMarkMoment_abs_le_bound
        (nativeStreamingOriginCurrentProbability D μ a q T o)
        (nativeStreamingDefectSpinTest T F (nativeStreamingOriginLevel q o))
        (2*C) (fun σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
  | future o j l =>
      exact nativeStreamingTerminalMarkMoment_abs_le_bound
        (nativeStreamingOriginFutureProbability D μ a q T o j l)
        (nativeStreamingDefectSpinTest T F l)
        (2*C) (fun σ => nativeStreamingDefectSpinTest_abs_le T F C hC hF _ σ)
  | normalizer l =>
      rw [nativeStreamingPatternMoment_normalizer_independent,
        ←nativeStreamingFreshDefectMoment_eq_fresh D μ a l,abs_mul]
      exact (mul_le_mul (abs_nativeStreamingOldTerminalExpectation_le D μ a q T F C hF)
        (nativeStreamingFreshDefectMoment_abs_le D μ a l) (abs_nonneg _) hC).trans_eq (by ring)

end QuantitativeFollowup
