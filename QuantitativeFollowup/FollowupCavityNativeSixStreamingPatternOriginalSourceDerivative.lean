module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexSourceDerivatives

@[expose] public section

/-! The original leaf-pair source integrand is an actual terminal test.
The diagonal remains zero and requires no added terminal spin. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeStreamingPatternOriginalTerminalTest
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i k : ObservationLeaf T) (σ : TerminalSpins (Configuration (n+1)) T) : ℝ :=
  if i=k then 0 else F σ*cavitySpinOverlapDefect n (q (observationCommonLevel T i k))
    (observationTerminalSpin T i σ) (observationTerminalSpin T k σ)

theorem nativeStreamingPatternMoment_original_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (i k : ObservationLeaf T) :
    nativeStreamingPatternMoment D μ a q T F (.original i k) =
      nativeStreamingOldTerminalExpectation D μ a q T
        (nativeStreamingPatternOriginalTerminalTest q T F i k) := by
  by_cases hik : i=k
  · subst k
    simp only [nativeStreamingPatternMoment,ite_true,nativeStreamingOldTerminalExpectation,
      nativeStreamingPatternOriginalTerminalTest,integral_zero]
  · simp only [nativeStreamingPatternMoment,if_neg hik,nativeStreamingOldTerminalExpectation]
    apply integral_congr_ae
    exact .of_forall fun z => by
      simp only [nativeStreamingPatternOriginalTerminalTest,if_neg hik,
        observationTerminalSpin_record]

theorem hasDerivWithinAt_nativeStreamingPattern_original_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i k : ObservationLeaf T) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.original i k))
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T
        (nativeStreamingPatternOriginalTerminalTest q T F i k)) (Icc (0:ℝ) 1) u := by
  exact hasDerivWithinAt_nativeStreamingPattern_of_terminalRepresentation hn β ρ hβ hρ
    μ a ha hfloor q hq hJ hzero htop T T F _ _
    (fun D=>nativeStreamingPatternMoment_original_terminalRepresentation D μ a q T F i k) u hu

end QuantitativeFollowup
