module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginalFreshSchemeMoment
public import QuantitativeFollowup.FollowupCavityPairProductBounds

@[expose] public section

/-! The actual finite current and two-vertex marked terms are the native
patterns under the identical scheme law. Both cross charges remain on
the original tree; no moment or probability identity is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingPatternMoment_current_scheme_vertex
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T F (.current (.vertex v)) =
      ∫z, F (finiteCascadeRecordTerminalSpins T z.1.2) *
        cavitySpinOverlapDefect n (anisotropicVertexOverlap s (T := T.advance) v) z.2.1 z.2.2
        ∂anisotropicCrossVertexMarkedLaw D s a T.advance v v := by
  change nativeStreamingTerminalMarkMoment
    (nativeStreamingCurrentPairProbability D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T v)
    (nativeStreamingDefectSpinTest T F (anisotropicRecordedSchemeSchedule s v.depth)) = _
  rw [nativeStreamingCurrentTerminalMoment_scheme_trimmed D s a hq T v,
    nativeStreamingSchemeSchedule_eq_profileLevel]
  rfl

theorem nativeStreamingPatternMoment_cross_scheme_vertices
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v w : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T F (.cross (.vertex v) (.vertex w)) =
      ∫z, F (finiteCascadeRecordTerminalSpins T z.1.2) *
        cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s T v w) z.2.1 z.2.2
        ∂anisotropicCrossVertexMarkedLaw D s a T.advance v w := by
  change nativeStreamingTerminalMarkMoment
    (nativeStreamingCrossVertexProbability D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T v w)
    (nativeStreamingDefectSpinTest T F (anisotropicRecordedSchemeSchedule s
      (finiteCascadeCommonPathDepth T v w))) = _
  rw [nativeStreamingCrossTerminalMoment_scheme_trimmed D s a hq T v w,
    nativeStreamingSchemeSchedule_eq_profileLevel,
    cavityPhysicalCommonOverlap_eq_profileLevel]
  rfl

theorem cavityCurrentFreshExpectation_eq_native_vertex_patterns
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    cavityCurrentFreshExpectation D s a T.advance
      (fun z => F (finiteCascadeRecordTerminalSpins T z.2)) =
      nativeStreamingVertexChargeSum (anisotropicSchemeMass s) a T
        (fun v => Paper.parisiCDF (Paper.parisiSchemeMeasure s)
          (anisotropicRecordedSchemeSchedule s v.depth) *
          nativeStreamingPatternMoment D (Paper.parisiSchemeMeasure s) a
            (anisotropicRecordedSchemeSchedule s) T F (.current (.vertex v))) := by
  unfold cavityCurrentFreshExpectation nativeStreamingVertexChargeSum
  simp_rw [nativeStreamingPatternMoment_current_scheme_vertex D s a hq T F,
    nativeStreamingSchemeSchedule_eq_profileLevel]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  change c.1 * Paper.parisiCDF (Paper.parisiSchemeMeasure s)
    (cavityProfileLevel s c.2.depth) * _ = _
  ring

theorem cavityFreshFreshExpectation_eq_native_vertex_patterns
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    cavityFreshFreshExpectation D s a T.advance
      (fun z => F (finiteCascadeRecordTerminalSpins T z.2)) =
      nativeStreamingVertexChargeSum (anisotropicSchemeMass s) a T (fun v =>
        nativeStreamingVertexChargeSum (anisotropicSchemeMass s) a T (fun w =>
          nativeStreamingPatternMoment D (Paper.parisiSchemeMeasure s) a
            (anisotropicRecordedSchemeSchedule s) T F (.cross (.vertex v) (.vertex w)))) := by
  unfold cavityFreshFreshExpectation nativeStreamingVertexChargeSum
  simp_rw [nativeStreamingPatternMoment_cross_scheme_vertices D s a hq T F,
    ←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  ring

end QuantitativeFollowup
