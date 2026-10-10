module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSimpleSourceLimits
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginalFreshOriginLimit
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCurrentOriginLimit
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossOriginLimit
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFutureOriginLimit

@[expose] public section

/-! Convergence of the literal complete six source terms, each under its
actual marked law and recursive Stieltjes weight. This is a genuine
formula-limit theorem and does not itself assert a differentiation rule. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1200000

theorem tendsto_nativeStreamingSourceSixBracket
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hcuts : ∀j, j≤J → q j∈S)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    Tendsto (fun N => nativeStreamingSourceSixBracket D (FRSB.preservingMeasure μ S N)
      a q T F) atTop (𝓝 (nativeStreamingSourceSixBracket D μ a q T F)) := by
  unfold nativeStreamingSourceSixBracket
  exact (((((tendsto_nativeStreamingSourceOriginalTerm D
    (FRSB.tendsto_preservingMeasure μ S) a q hq T F).add
      (tendsto_nativeStreamingSourceOriginalFreshTerm D μ a ha hμ q hq T S hzero hcuts F)).add
      (tendsto_nativeStreamingSourceCrossTerm D μ a ha hμ q hq T S hzero hcuts F)).add
      (tendsto_nativeStreamingSourceCurrentTerm D μ a ha hμ q hq T S hzero hcuts F)).add
      (tendsto_nativeStreamingSourceFutureTerm D μ a ha hμ q hq T S hzero hcuts F)).add
      (tendsto_nativeStreamingSourceNormalizerTerm D μ a ha hμ q hq T F S hzero)

end QuantitativeFollowup
