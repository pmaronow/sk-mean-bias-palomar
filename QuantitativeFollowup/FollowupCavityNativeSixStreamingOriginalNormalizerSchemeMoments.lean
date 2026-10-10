module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossCurrentSchemeMoments
public import QuantitativeFollowup.FollowupCavitySixTermStreaming

@[expose] public section

/-! The remaining uncharged finite terms are the genuine native original
leaf-pair and independent normalizer expectations.  Terminal diagonals
vanish structurally, while the independent fresh law keeps all atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem nativeStreamingOldTerminalMoment_scheme_trimmed
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (G : TerminalSpins (Configuration n) T → ℝ) :
    (∫z,G (finiteCascadeRecordTerminalSpins T z.2)
      ∂anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
        (anisotropicRecordedSchemeSchedule s) T) =
      ∫z,G (finiteCascadeRecordTerminalSpins T z.2)
        ∂anisotropicTrimmedRecordedTreeLaw D s a T.advance := by
  have hmap := nativeStreamingRecordedProfileLaw_scheme_energy_prefix D s a T (by omega)
  rw [nativeStreamingFiniteRecordedPrefixLaw_trimmed D s a hq T] at hmap
  have hm : Measurable (Prod.map (anisotropicObservationEnergy D)
      (observationTreeMap (S:=Configuration n) (anisotropicObservationEnergy D) T)) :=
    (measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) T)
  have hG : Measurable (fun z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) T =>
      G (finiteCascadeRecordTerminalSpins T z.2)) :=
    (measurable_of_finite G).comp ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)
  have H := integral_map (μ:=anisotropicRecordedProfileTreeLaw D
      (Paper.parisiSchemeMeasure s) a (anisotropicRecordedSchemeSchedule s) T)
    hm.aemeasurable hG.aestronglyMeasurable
  rw [hmap] at H
  simpa only [Prod.map_snd,finiteCascadeRecordTerminalSpins_treeMap] using H.symm

private theorem integrable_old_terminal_test
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+1)) (G : TerminalSpins (Configuration n) T→ℝ) :
    Integrable (fun z=>G (finiteCascadeRecordTerminalSpins T z.2))
      (anisotropicTrimmedRecordedTreeLaw D s a T.advance) := by
  classical
  letI : IsProbabilityMeasure (anisotropicTrimmedRecordedTreeLaw D s a T.advance) :=
    anisotropicTrimmedRecordedTreeLaw_probability D s a T.advance
  let C := ∑σ : TerminalSpins (Configuration n) T,|G σ|
  apply (integrable_const (c:=C)).mono'
    ((measurable_of_finite G).comp
      ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)).aestronglyMeasurable
  exact .of_forall fun z=>by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f:=fun σ=>|G σ|)
      (fun _ _=>abs_nonneg _) (Finset.mem_univ _)

 theorem cavityOriginalOriginalExpectation_eq_native_original_patterns
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    (∫z,F (finiteCascadeRecordTerminalSpins T z.2)*
      cavityOriginalDistinctLeafDefect n s T.advance z
        ∂anisotropicTrimmedRecordedTreeLaw D s a T.advance) =
      nativeStreamingSourceOriginalTerm D (Paper.parisiSchemeMeasure s) a
        (anisotropicRecordedSchemeSchedule s) T F := by
  classical
  let P := anisotropicTrimmedRecordedTreeLaw D s a T.advance
  let G := fun (i l : ObservationLeaf T) (σ : TerminalSpins (Configuration (n+1)) T)=>
    F σ*cavitySpinOverlapDefect n (anisotropicRecordedSchemeSchedule s
      (observationCommonLevel T i l)) (observationTerminalSpin T i σ)
        (observationTerminalSpin T l σ)
  have hi (i l : ObservationLeaf T) : Integrable
      (fun z=>G i l (finiteCascadeRecordTerminalSpins T z.2)) P :=
    integrable_old_terminal_test D s a T (G i l)
  have he (i l : ObservationLeaf T) : nativeStreamingPatternMoment D
      (Paper.parisiSchemeMeasure s) a (anisotropicRecordedSchemeSchedule s) T F
      (.original i l) = ∫z,G i l (finiteCascadeRecordTerminalSpins T z.2) ∂P := by
    by_cases hil : i=l
    · subst l
      simp only [nativeStreamingPatternMoment,ite_true,G,observationCommonLevel_self,
        nativeStreamingSchemeSchedule_zero,Set.Icc.coe_one,
        cavitySpinOverlapDefect_self n hn,mul_zero,integral_zero]
    · simp only [nativeStreamingPatternMoment,if_neg hil,G,observationTerminalSpin_record]
      simpa only [G,P,observationTerminalSpin_record] using
        nativeStreamingOldTerminalMoment_scheme_trimmed D s a hq T (G i l)
  have hpoint (z) : F (finiteCascadeRecordTerminalSpins T z.2)*
      cavityOriginalDistinctLeafDefect n s T.advance z =
        ∑i : ObservationLeaf T,∑l : ObservationLeaf T,
          G i l (finiteCascadeRecordTerminalSpins T z.2) := by
    rw [cavityOriginalDistinctLeafDefect_eq_leaves hn D s T.advance z]
    simp_rw [nativeStreamingObservationLeaves_sum,Finset.mul_sum]
    simp only [G,cavityRecordedLeafPairDefect,observationTerminalSpin_record,
      nativeStreamingSchemeSchedule_eq_profileLevel]
  simp_rw [hpoint]
  rw [integral_finset_sum Finset.univ (fun i _=>integrable_finset_sum Finset.univ (fun l _=>hi i l))]
  simp_rw [integral_finset_sum Finset.univ (fun l _=>hi _ l)]
  unfold nativeStreamingSourceOriginalTerm
  simp_rw [he]

 theorem cavityNormalizerExpectation_eq_native_normalizer_pattern
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    a*(∫z,F (finiteCascadeRecordTerminalSpins T z.2)
      ∂anisotropicTrimmedRecordedTreeLaw D s a T.advance)*
      cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a =
      nativeStreamingSourceNormalizerTerm D (Paper.parisiSchemeMeasure s) a
        (anisotropicRecordedSchemeSchedule s) T F := by
  rw [nativeStreamingSourceNormalizerTerm_eq_independent]
  unfold nativeStreamingOldTerminalExpectation
  rw [nativeStreamingOldTerminalMoment_scheme_trimmed D s a hq T F]
  rfl

end QuantitativeFollowup
