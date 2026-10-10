module
public import HexagonPaper.CavityCoefficients

@[expose] public section

/-! The revised Chapter 7 streaming lemma, for the physical arbitrary-profile
tree law.  Its six terms are the already proved literal marked expectations,
with coalesced branch charges, positive-length open edges and an independent
normalizer component.  The second bracket applies the same source functional
to those genuine representing trees, with the product rule for independent
components.  Both endpoints use within derivatives on the closed interval.

This theorem reuses the previous kernel proof of the same physical law.  That
proof obtains the general profile law internally; its conclusion is not a
premise.  The new coefficient argument in `CavityCoefficients` works directly
with the fixed arbitrary profile.
-/
noncomputable section
open Set MeasureTheory
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
set_option autoImplicit false
variable {n J : ℕ}

theorem cavity_streaming_arbitrary_profile
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    ContDiffOn ℝ 2 (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) ∧
    (∀u (hu : u∈Icc (0:ℝ) 1), HasDerivWithinAt
      (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      ((followupCavityAlpha n β ρ/2)*printedNativeSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) (Icc (0:ℝ) 1) u) ∧
    (∀u (hu : u∈Icc (0:ℝ) 1), HasDerivWithinAt
      (nativeStreamingPrintedSourceSixParameterBracket β ρ hβ hρ μ a q T F)
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceTermwiseSecondBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) (Icc (0:ℝ) 1) u) ∧
    (∀u (hu : u∈Icc (0:ℝ) 1), withinJet
      (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F) (Icc (0:ℝ) 1) 2 u =
      (followupCavityAlpha n β ρ/2)^2*nativeStreamingSourceTermwiseSecondBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) ∧
    (0 ≤ cavity_source_coefficient_envelope μ a q T ∧
      cavity_source_coefficient_envelope μ a q T ≤
        4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
          2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1) := by
  have H := nativeStreamingSource_general_profiles_printed_actual hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F
  exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2,
    cavity_source_coefficient_envelope_nonneg_le μ a ha hfloor q hq T⟩

end HexagonPaper
