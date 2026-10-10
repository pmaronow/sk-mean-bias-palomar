module
public import QuantitativeFollowup.SupportingPrintedCoalescedSourceSixBracket
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceResults
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingActualSource

@[expose] public section

/-! The genuine first six-term formula with literal physical branch
charges and branch atoms assigned outside open edge cells. The actual
marked laws discharge every callback condition internally. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingSourceSixBracket_eq_printed_actual
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hq0 : q 0=1)
    (T : FiniteTerminalGenealogy J) (hqJ : q J=zeroOverlap)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingSourceSixBracket D μ a q T F =
      printedNativeSourceSixBracket D μ a q T F := by
  apply nativeStreamingSourceSixBracket_eq_printed_of_coherence D μ a ha hμ q hq hq0 T hqJ F
  · exact nativeCoalescedOriginCoherent_originalFresh D μ a q hq hq0 T F
  · intro v
    exact nativeCoalescedOriginCoherent_cross_right D μ a q hq hq0 T F (.vertex v) trivial
  · intro e r hr
    exact nativeCoalescedOriginCoherent_cross_right D μ a q hq hq0 T F (.edge e r)
      ⟨hr.1.le,hr.2.le⟩
  · exact nativeCoalescedOriginCoherent_cross_weight_all_tests D μ a q hq hq0 T F a
  · exact nativeCoalescedOriginCoherent_current_all_tests D μ a q hq hq0 T F
  · exact nativeCoalescedOriginCoherent_future_all_tests D μ a q hq hq0 T F

theorem nativeStreamingSource_derivative_printed_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0 : ℝ)=1) (htop : (q J : ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u∈Icc (0 : ℝ) 1) :
    withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0 : ℝ) 1) 1 u =
      (followupCavityAlpha n β ρ/2)*printedNativeSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F := by
  rw [nativeStreamingSource_derivative_actual hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F u hu]
  rw [nativeStreamingSourceSixBracket_eq_printed_actual _ μ a ha hfloor q hq
    (Subtype.ext hzero) T (Subtype.ext htop) F]

theorem hasDerivWithinAt_nativeStreamingSource_printed_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0 : ℝ)=1) (htop : (q J : ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u∈Icc (0 : ℝ) 1) :
    HasDerivWithinAt (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      ((followupCavityAlpha n β ρ/2)*printedNativeSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) (Icc (0 : ℝ) 1) u := by
  have h := hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F u hu
  rw [nativeStreamingSourceSixBracket_eq_printed_actual _ μ a ha hfloor q hq
    (Subtype.ext hzero) T (Subtype.ext htop) F] at h
  exact h

end QuantitativeFollowup
