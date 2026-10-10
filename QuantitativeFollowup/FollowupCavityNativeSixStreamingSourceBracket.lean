module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginWeightIntegral

@[expose] public section

/-! The six source terms are literal marked-law expectations with actual
Stieltjes attachment weights.  This definition is not a differentiation
theorem.  In particular both cross weights are evaluated on the original
tree, and the final term retains a genuinely independent fresh law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

instance nativeStreamingObservationLeafFintype : {j : ℕ} →
    (T : FiniteTerminalGenealogy j) → Fintype (ObservationLeaf T)
  | _, .leaf => inferInstance
  | _, .advance T => nativeStreamingObservationLeafFintype T
  | _, .fork T U => by
      letI := nativeStreamingObservationLeafFintype T
      letI := nativeStreamingObservationLeafFintype U
      exact inferInstance

def nativeStreamingPatternFutureIntegral (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (o : NativeStreamingOrigin T) : ℝ :=
  ∑j∈Finset.range J, ∫l in Ioc (q (j+1)) (q j),
    if nativeStreamingOriginLevel q o<l then
      nativeStreamingPatternMoment D μ a q T F (.future o j l) else 0
      ∂parisiFreeMeasure μ a

def nativeStreamingSourceOriginalTerm (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  ∑i : ObservationLeaf T, ∑k : ObservationLeaf T,
    nativeStreamingPatternMoment D μ a q T F (.original i k)

def nativeStreamingSourceOriginalFreshTerm (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  -2*∑i : ObservationLeaf T, nativeStreamingOriginWeightIntegral μ a q T a
    (fun o => nativeStreamingPatternMoment D μ a q T F (.originalFresh i o))

def nativeStreamingSourceCrossTerm (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  nativeStreamingOriginWeightIntegral μ a q T a (fun o =>
    nativeStreamingOriginWeightIntegral μ a q T a (fun p =>
      nativeStreamingPatternMoment D μ a q T F (.cross o p)))

def nativeStreamingSourceCurrentTerm (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  nativeStreamingOriginWeightIntegral μ a q T a (fun o =>
    Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
      nativeStreamingPatternMoment D μ a q T F (.current o))

def nativeStreamingSourceFutureTerm (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  nativeStreamingOriginWeightIntegral μ a q T a
    (nativeStreamingPatternFutureIntegral D μ a q T F)

def nativeStreamingSourceNormalizerTerm (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  a*∫l, nativeStreamingPatternMoment D μ a q T F (.normalizer l)
    ∂parisiFreeMeasure μ a

def nativeStreamingSourceSixBracket (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  nativeStreamingSourceOriginalTerm D μ a q T F +
    nativeStreamingSourceOriginalFreshTerm D μ a q T F +
    nativeStreamingSourceCrossTerm D μ a q T F +
    nativeStreamingSourceCurrentTerm D μ a q T F +
    nativeStreamingSourceFutureTerm D μ a q T F +
    nativeStreamingSourceNormalizerTerm D μ a q T F

theorem nativeStreamingSourceNormalizerTerm_eq_independent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingSourceNormalizerTerm D μ a q T F =
      a*nativeStreamingOldTerminalExpectation D μ a q T F *
        (∫l, ∫z, cavitySpinOverlapDefect n l z.2.1 z.2.2
          ∂anisotropicFreshTerminalPairLaw D μ a l ∂parisiFreeMeasure μ a) := by
  simp only [nativeStreamingSourceNormalizerTerm, nativeStreamingPatternMoment]
  rw [integral_const_mul]
  ring

end QuantitativeFollowup
