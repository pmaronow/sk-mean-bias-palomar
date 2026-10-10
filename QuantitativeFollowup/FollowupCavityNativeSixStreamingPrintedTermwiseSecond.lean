module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingActualTermwiseSecond
public import QuantitativeFollowup.SupportingPrintedCoalescedSourceActual

@[expose] public section

/-! The general-profile formula in the literal coalesced presentation.
The physical equality of the two first brackets holds at every parameter;
its derivative is transported from the actual termwise integral calculus.
The explicit second bracket is the source response on each genuine
representing tree, including the independent normalizer product. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingPrintedSourceSixParameterBracket
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (u : ℝ) : ℝ :=
  if hu : u∈Icc (0:ℝ) 1 then
    printedNativeSourceSixBracket (followupCavitySpinModel n β ρ hβ hρ u hu)
      μ a q T F else 0

theorem nativeStreamingPrintedSourceSixParameterBracket_eq_native
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    nativeStreamingPrintedSourceSixParameterBracket β ρ hβ hρ μ a q T F u =
      nativeStreamingSourceSixParameterBracket β ρ hβ hρ μ a q T F u := by
  rw [nativeStreamingSourceSixParameterBracket_eq_actual β ρ hβ hρ μ a q T F u hu]
  simp only [nativeStreamingPrintedSourceSixParameterBracket,dif_pos hu]
  exact (nativeStreamingSourceSixBracket_eq_printed_actual _ μ a ha hfloor q hq
    (Subtype.ext hzero) T (Subtype.ext htop) F).symm

theorem hasDerivWithinAt_nativeStreamingPrintedSourceSixBracket_termwise_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPrintedSourceSixParameterBracket β ρ hβ hρ μ a q T F)
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceTermwiseSecondBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) (Icc (0:ℝ) 1) u := by
  have h := (nativeStreamingSource_c2_termwise_actual hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F).2.1 u hu
  apply h.congr_of_mem ?_ hu
  intro v hv
  exact nativeStreamingPrintedSourceSixParameterBracket_eq_native β ρ hβ hρ μ a ha
    hfloor q hq hzero htop T F v hv

theorem nativeStreamingSource_general_profiles_printed_actual
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
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F) := by
  have h := nativeStreamingSource_c2_termwise_actual hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F
  refine ⟨h.1,?_,?_,h.2.2⟩
  · intro u hu
    exact hasDerivWithinAt_nativeStreamingSource_printed_actual hn β ρ hβ hρ μ a ha hfloor
      q hq hJ hzero htop T F u hu
  · intro u hu
    exact hasDerivWithinAt_nativeStreamingPrintedSourceSixBracket_termwise_actual hn β ρ hβ hρ
      μ a ha hfloor q hq hJ hzero htop T F u hu

end QuantitativeFollowup
