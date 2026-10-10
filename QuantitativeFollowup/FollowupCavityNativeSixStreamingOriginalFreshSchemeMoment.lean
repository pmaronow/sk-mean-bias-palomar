module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSchemeTerminalMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCharges
public import QuantitativeFollowup.FollowupCavityOriginalStreamingCubic
public import QuantitativeFollowup.FollowupCavityMarkedFiveTerms
public import FourPapersCommon.ListSignedGram

@[expose] public section

/-! The actual finite original/fresh term is exactly the sum of the
native vertex patterns. Terminal leaves are enumerated by their actual
structural indices, independently of whether spin values coincide. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingSchemeSchedule_eq_profileLevel (s : RSBScheme k) (j : ℕ) :
    anisotropicRecordedSchemeSchedule s j=cavityProfileLevel s j := by
  apply Subtype.ext
  rw [anisotropicRecordedSchemeSchedule,
    anisotropicFiniteMeshNode_coe s _ (Nat.sub_le _ _), cavityProfileLevel_coe_for_streaming]

theorem nativeStreamingObservationLeaves_sum (T : FiniteTerminalGenealogy J)
    (f : ObservationLeaf T → ℝ) :
    ((observationLeaves T).map f).sum=∑i : ObservationLeaf T, f i := by
  induction T with
  | leaf => simp [observationLeaves]
  | advance T ih => exact ih f
  | fork T U ihT ihU =>
      simp only [observationLeaves, List.map_append, List.map_map,
        List.sum_append, Function.comp_def]
      rw [ihT,ihU]
      exact (Fintype.sum_sum_type f).symm

theorem nativeStreamingPatternMoment_originalFresh_scheme_vertex
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T F (.originalFresh i (.vertex v)) =
      ∫z, F (finiteCascadeRecordTerminalSpins T z.1.2) *
        cavitySpinOverlapDefect n
          (cavityProfileLevel s (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v))
          (observationLeafSpin T i z.1.2) z.2
        ∂anisotropicSingleVertexMarkedLaw D s a T.advance v := by
  change nativeStreamingTerminalMarkMoment
    (nativeStreamingSingleVertexProbability D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T v)
    (nativeStreamingOriginalFreshSpinTest T F i
      (anisotropicRecordedSchemeSchedule s
        (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v))) = _
  rw [nativeStreamingSingleTerminalMoment_scheme_trimmed D s a hq T v,
    nativeStreamingSchemeSchedule_eq_profileLevel]
  simp only [nativeStreamingOriginalFreshSpinTest, observationTerminalSpin_record]

private theorem integrable_finite_terminal_single_test
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+1)) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration (n+1)) T × Configuration (n+1) → ℝ) :
    Integrable (fun z => G (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
      (anisotropicSingleVertexMarkedLaw D s a T.advance v) := by
  classical
  haveI := anisotropicSingleVertexMarkedLaw_probability D s a T.advance v
  let C := ∑x : TerminalSpins (Configuration (n+1)) T × Configuration (n+1), |G x|
  have hm : Measurable (fun z : (FiniteStateField (Configuration (n+1)) ×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) T) ×
      Configuration (n+1) => (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    ((measurable_finiteCascadeRecordTerminalSpins T).comp
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  apply (integrable_const (c := C)).mono'
    ((measurable_of_finite G).comp hm).aestronglyMeasurable
  exact .of_forall fun z => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun x => |G x|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ _)

theorem cavityOriginalFreshExpectation_eq_native_vertex_patterns
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    cavityOriginalFreshExpectation D s a T.advance
      (fun z => F (finiteCascadeRecordTerminalSpins T z.2)) =
      ∑i : ObservationLeaf T,
        nativeStreamingVertexChargeSum (anisotropicSchemeMass s) a T
          (fun v => nativeStreamingPatternMoment D (Paper.parisiSchemeMeasure s) a
            (anisotropicRecordedSchemeSchedule s) T F (.originalFresh i (.vertex v))) := by
  classical
  have hi (v : FiniteCascadeRecordVertex T) (i : ObservationLeaf T) :
      Integrable (fun z => F (finiteCascadeRecordTerminalSpins T z.1.2) *
        cavitySpinOverlapDefect n
          (cavityProfileLevel s (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v))
          (observationLeafSpin T i z.1.2) z.2)
        (anisotropicSingleVertexMarkedLaw D s a T.advance v) := by
    simpa only [nativeStreamingOriginalFreshSpinTest, observationTerminalSpin_record] using
      integrable_finite_terminal_single_test D s a T v
        (nativeStreamingOriginalFreshSpinTest T F i
          (cavityProfileLevel s (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v)))
  have he (v : FiniteCascadeRecordVertex T) :
      (∫z, F (finiteCascadeRecordTerminalSpins T z.1.2) *
        cavityOriginalVertexOverlapSum n s T.advance v
          (finiteCascadeRecordTerminalSpins T z.1.2) z.2
        ∂anisotropicSingleVertexMarkedLaw D s a T.advance v) =
      ((observationLeaves T).map (fun i => nativeStreamingPatternMoment D
        (Paper.parisiSchemeMeasure s) a (anisotropicRecordedSchemeSchedule s) T F
          (.originalFresh i (.vertex v)))).sum := by
    simp_rw [cavityOriginalVertexOverlapSum_eq_leaves s T.advance,
      ←List.sum_map_mul_left]
    rw [integral_list_map_sum_real _ _ _ (hi v)]
    simp_rw [←nativeStreamingPatternMoment_originalFresh_scheme_vertex D s a hq T F]
  unfold cavityOriginalFreshExpectation
  simp_rw [he, ←List.sum_map_mul_left]
  rw [list_double_sum_comm_real]
  rw [nativeStreamingObservationLeaves_sum]
  rfl

end QuantitativeFollowup
