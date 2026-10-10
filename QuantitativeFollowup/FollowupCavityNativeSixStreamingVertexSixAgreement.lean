module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFutureSchemeIntegrals

@[expose] public section

/-! All six genuine physical finite streaming terms have the literal
native terminal-pattern form before the attachment weights are regrouped.
Both cross charges are evaluated on the same original genealogy. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k J : ℕ}
set_option maxHeartbeats 1400000

def nativeStreamingVertexSixBracket (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (b : ℕ → ℝ) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  nativeStreamingSourceOriginalTerm D μ a q T F -
    2*(∑i : ObservationLeaf T,nativeStreamingVertexChargeSum b a T
      (fun v=>nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.vertex v)))) +
    nativeStreamingVertexChargeSum b a T (fun v=>nativeStreamingVertexChargeSum b a T
      (fun w=>nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.vertex w)))) +
    nativeStreamingVertexChargeSum b a T (fun v=>Paper.parisiCDF μ (q v.depth)*
      nativeStreamingPatternMoment D μ a q T F (.current (.vertex v))) +
    nativeStreamingVertexChargeSum b a T
      (fun v=>nativeStreamingPatternFutureIntegral D μ a q T F (.vertex v)) +
    nativeStreamingSourceNormalizerTerm D μ a q T F

theorem cavityMarkedSixExpectation_eq_native_vertex_six_bracket
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    cavityMarkedSixExpectation D s a T.advance
      (fun z=>F (finiteCascadeRecordTerminalSpins T z.2)) =
      nativeStreamingVertexSixBracket D (Paper.parisiSchemeMeasure s) a
        (anisotropicRecordedSchemeSchedule s) (anisotropicSchemeMass s) T F := by
  unfold cavityMarkedSixExpectation cavityMarkedFiveExpectation nativeStreamingVertexSixBracket
  rw [cavityOriginalOriginalExpectation_eq_native_original_patterns hn D s a hq T F,
    cavityOriginalFreshExpectation_eq_native_vertex_patterns D s a hq T F,
    cavityFreshFreshExpectation_eq_native_vertex_patterns D s a hq T F,
    cavityCurrentFreshExpectation_eq_native_vertex_patterns D s a hq T F,
    cavityFutureFreshExpectation_eq_native_vertex_patterns D s a ha has hq T F,
    cavityNormalizerExpectation_eq_native_normalizer_pattern D s a hq T F]

end QuantitativeFollowup
