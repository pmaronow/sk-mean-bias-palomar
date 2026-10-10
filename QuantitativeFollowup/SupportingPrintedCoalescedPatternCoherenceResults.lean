module
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceNested

@[expose] public section

/-! Model-only native contracts. Every test on the finite terminal-spin
space has the required envelope, so no test bound or coherence is supplied
as an input to the canonical first-six rewrite. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000

private theorem nativeCoalesced_finite_test_bound
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    ∃C : ℝ, 0≤C ∧ ∀σ, |F σ|≤C := by
  classical
  refine ⟨∑σ, |F σ|, Finset.sum_nonneg (fun σ _ => abs_nonneg (F σ)), ?_⟩
  intro σ
  exact Finset.single_le_sum (fun τ _ => abs_nonneg (F τ)) (Finset.mem_univ σ)

theorem nativeCoalescedOriginCoherent_current_all_tests
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeCoalescedOriginCoherent μ a q T (fun o => Paper.parisiCDF μ (nativeStreamingOriginLevel q o) *
      nativeStreamingPatternMoment D μ a q T F (.current o)) := by
  obtain ⟨C,hC,hF⟩ := nativeCoalesced_finite_test_bound T F
  exact nativeCoalescedOriginCoherent_current D μ a q hq hzero T F C hC hF

theorem nativeCoalescedOriginCoherent_future_all_tests
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeCoalescedOriginCoherent μ a q T
      (nativeStreamingPatternFutureIntegral D μ a q T F) := by
  obtain ⟨C,hC,hF⟩ := nativeCoalesced_finite_test_bound T F
  exact nativeCoalescedOriginCoherent_future D μ a q hq hzero T F C hC hF

theorem nativeCoalescedOriginCoherent_cross_weight_all_tests
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) (s : ℝ) :
    nativeCoalescedOriginCoherent μ a q T (fun o => nativeStreamingOriginWeightIntegral μ a q T s
      (fun p => nativeStreamingPatternMoment D μ a q T F (.cross o p))) := by
  obtain ⟨C,hC,hF⟩ := nativeCoalesced_finite_test_bound T F
  exact nativeCoalescedOriginCoherent_cross_weight D μ a q hq hzero T F C hC hF s

end QuantitativeFollowup
