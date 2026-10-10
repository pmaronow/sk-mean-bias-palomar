module
public import QuantitativeFollowup.FollowupCavitySixCubicBudget
public import QuantitativeFollowup.FollowupCavitySixTermEndpoints
public import FourPapersCommon.FiniteObservationTerminalProjection

@[expose] public section

/-! Genuine closed-interval streaming of the terminal two-pair
observable, with its actual cubic bound and literal six-term response. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityTerminalPairProduct (s : RSBScheme k) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i l : Fin 2→ObservationLeaf T) (σ : TerminalSpins (Configuration (n+1)) T) : ℝ :=
  cavitySpinOverlapDefect n (cavityProfileLevel s (observationCommonLevel T (i 0) (l 0)))
    (observationTerminalSpin T (i 0) σ) (observationTerminalSpin T (l 0) σ)*
  cavitySpinOverlapDefect n (cavityProfileLevel s (observationCommonLevel T (i 1) (l 1)))
    (observationTerminalSpin T (i 1) σ) (observationTerminalSpin T (l 1) σ)

def cavityPairProductSampleObservable (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2))
    (i l : Fin 2→ObservationLeaf (trimRoot T))
    (σ : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)) : ℝ :=
  cavityTerminalPairProduct s (trimRoot T) i l
    ((terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm ((trimmedSpinEquiv (S:=Configuration (n+1)) T).symm σ))

theorem cavityPairProductSampleObservable_record (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2→ObservationLeaf (trimRoot T)) :
    followupCavityPhysicalRecordObservable n T (cavityPairProductSampleObservable s T i l)=
      cavityRecordedPairProduct s (trimRoot T) i l := by
  funext r
  unfold followupCavityPhysicalRecordObservable cavityPairProductSampleObservable
  rw [(trimmedSpinEquiv (S:=Configuration (n+1)) T).symm_apply_apply,←terminalSampleEquiv_recordSpins,
    (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm_apply_apply]
  simp only [cavityTerminalPairProduct,cavityRecordedPairProduct,cavityRecordedLeafPairDefect,
    observationTerminalSpin_record]

def followupCavityPairProductExpectation (n:ℕ)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(T:FiniteTerminalGenealogy (k+2))
    (i l:Fin 2→ObservationLeaf (trimRoot T)) : ℝ→ℝ :=
  followupCavityPhysicalExpectation n β ρ hβ hρ s a T (cavityPairProductSampleObservable s T i l)

theorem followupCavityPairProductExpectation_eq_integral
    (β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(hq:s.q 1=0)(T:FiniteTerminalGenealogy (k+2))
    (i l:Fin 2→ObservationLeaf (trimRoot T))(u:ℝ)(hu:u∈Icc (0:ℝ) 1):
    followupCavityPairProductExpectation n β ρ hβ hρ s a T i l u=
      ∫z,cavityRecordedPairProduct s (trimRoot T) i l z
        ∂anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T := by
  rw [followupCavityPairProductExpectation,followupCavityPhysicalExpectation_eq_record_integral
    n β ρ hβ hρ s a hq T _ u hu,cavityPairProductSampleObservable_record]

theorem hasDerivWithinAt_followupCavityPairProductExpectation
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))(i l:Fin 2→ObservationLeaf (trimRoot T))
    (u:ℝ)(hu:u∈Icc (0:ℝ) 1):
    HasDerivWithinAt (followupCavityPairProductExpectation n β ρ hβ hρ s a T i l)
      (followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
        (cavityRecordedPairProduct s (trimRoot T) i l)) (Icc (0:ℝ) 1) u := by
  have hh:=hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ
    s a ha has hq T (cavityPairProductSampleObservable s T i l) u hu
  rw [cavityPairProductSampleObservable_record] at hh
  exact hh

theorem followupCavityPairProductResponse_cubic_le
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))(i l:Fin 2→ObservationLeaf (trimRoot T))
    (u:ℝ)(hu:u∈Icc (0:ℝ) 1):
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a T
      (cavityRecordedPairProduct s (trimRoot T) i l)| ≤
      followupCavityAlpha n β ρ/2*(15*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  have hα:=followupCavityAlpha_nonneg n β ρ hρ.2
  rw [abs_mul,abs_of_nonneg (by positivity:0≤followupCavityAlpha n β ρ/2)]
  exact (mul_le_mul_of_nonneg_left (cavityMarkedSix_pairProduct_cubic_le hn
    (followupCavitySpinModel n β ρ hβ hρ u hu) s a ha has hq T i l) (by positivity)).trans_eq (by ring)

end QuantitativeFollowup
