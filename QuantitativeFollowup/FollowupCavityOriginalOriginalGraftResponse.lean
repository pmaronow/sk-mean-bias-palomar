module
public import QuantitativeFollowup.FollowupCavitySingleGraftResponse
public import QuantitativeFollowup.FollowupCavityOriginalLeafPairs
public import QuantitativeFollowup.FollowupCavityOriginalStreamingCubic
public import QuantitativeFollowup.FollowupCavityTerminalObservable

@[expose] public section

/-! The original-original distinct-leaf defect is a fixed terminal-spin test.
Its physical expectation therefore has the genuine closed-interval six-term
streaming derivative, including the zero-variance endpoint. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityOriginalOriginalTerminalDefect (n : ℕ) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2))
    (τ : TerminalSpins (Configuration (n+1)) (trimRoot T)) : ℝ := by
  classical
  let xs := finiteCascadeTerminalVertices (trimRoot T) τ
  exact (xs.map (fun c => (xs.map (fun d => if c.1=d.1 then 0 else
    cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.1 d.1)
      c.2 d.2)).sum)).sum

theorem cavityOriginalOriginalTerminalDefect_record (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2))
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityOriginalOriginalTerminalDefect n s T
      (finiteCascadeRecordTerminalSpins (trimRoot T) r.2) =
      cavityOriginalDistinctLeafDefect n s T r := rfl

def cavityOriginalOriginalGraftSampleObservable (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T) → ℝ)
    (σ : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)) : ℝ :=
  let τ := (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm
    ((trimmedSpinEquiv (S:=Configuration (n+1)) T).symm σ)
  F τ * cavityOriginalOriginalTerminalDefect n s T τ

theorem cavityOriginalOriginalGraftSampleObservable_record (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T) → ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    followupCavityPhysicalRecordObservable n T
      (cavityOriginalOriginalGraftSampleObservable s T F) r =
      F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2) *
        cavityOriginalDistinctLeafDefect n s T r := by
  dsimp only [followupCavityPhysicalRecordObservable,
    cavityOriginalOriginalGraftSampleObservable]
  rw [(trimmedSpinEquiv (S:=Configuration (n+1)) T).symm_apply_apply,
    ←terminalSampleEquiv_recordSpins,
    (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm_apply_apply,
    cavityOriginalOriginalTerminalDefect_record]

def followupCavityOriginalOriginalGraftExpectation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ ∈ Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T) → ℝ) (u : ℝ) : ℝ :=
  followupCavityPhysicalExpectation n β ρ hβ hρ s a T
    (cavityOriginalOriginalGraftSampleObservable s T F) u

theorem followupCavityOriginalOriginalGraftExpectation_eq_record_integral
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    followupCavityOriginalOriginalGraftExpectation n β ρ hβ hρ s a T F u =
      ∫r, F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2) *
        cavityOriginalDistinctLeafDefect n s T r
        ∂anisotropicTrimmedRecordedTreeLaw
          (followupCavitySpinModel n β ρ hβ hρ u hu) s a T := by
  rw [followupCavityOriginalOriginalGraftExpectation,
    followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq T
      (cavityOriginalOriginalGraftSampleObservable s T F) u hu]
  apply integral_congr_ae
  exact .of_forall fun r => cavityOriginalOriginalGraftSampleObservable_record s T F r

theorem hasDerivWithinAt_followupCavityOriginalOriginalGraftExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityOriginalOriginalGraftExpectation n β ρ hβ hρ s a T F)
      (followupCavityAlpha n β ρ/2 * cavityMarkedSixExpectation
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
        (fun r => F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2) *
          cavityOriginalDistinctLeafDefect n s T r)) (Icc (0:ℝ) 1) u := by
  have h := hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn
    β ρ hβ hρ s a ha has hq T (cavityOriginalOriginalGraftSampleObservable s T F) u hu
  have he : followupCavityPhysicalRecordObservable n T
      (cavityOriginalOriginalGraftSampleObservable s T F) =
      fun r => F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2) *
        cavityOriginalDistinctLeafDefect n s T r :=
    funext fun r => cavityOriginalOriginalGraftSampleObservable_record s T F r
  rw [he] at h
  exact h

def followupCavityOriginalOriginalSampleExpectation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ ∈ Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1))
      (asGenealogy (trimRoot T)) → ℝ) (u : ℝ) : ℝ :=
  followupCavityOriginalOriginalGraftExpectation n β ρ hβ hρ s a T
    (fun τ => F (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) τ)) u

theorem followupCavityOriginalOriginalSampleExpectation_eq_record_integral
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1))
      (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    followupCavityOriginalOriginalSampleExpectation n β ρ hβ hρ s a T F u =
      ∫r, F (spins (trimRoot T) r.2) * cavityOriginalDistinctLeafDefect n s T r
        ∂anisotropicTrimmedRecordedTreeLaw
          (followupCavitySpinModel n β ρ hβ hρ u hu) s a T := by
  simpa only [followupCavityOriginalOriginalSampleExpectation,
    terminalSampleEquiv_recordSpins] using
      followupCavityOriginalOriginalGraftExpectation_eq_record_integral β ρ hβ hρ s a hq T
        (fun τ => F (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) τ)) u hu

theorem hasDerivWithinAt_followupCavityOriginalOriginalSampleExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1))
      (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityOriginalOriginalSampleExpectation n β ρ hβ hρ s a T F)
      (followupCavityAlpha n β ρ/2 * cavityMarkedSixExpectation
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
        (fun r => F (spins (trimRoot T) r.2) * cavityOriginalDistinctLeafDefect n s T r))
      (Icc (0:ℝ) 1) u := by
  change HasDerivWithinAt (followupCavityOriginalOriginalGraftExpectation n β ρ hβ hρ s a T
    (fun τ => F (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) τ))) _ _ _
  simpa only [terminalSampleEquiv_recordSpins] using
      hasDerivWithinAt_followupCavityOriginalOriginalGraftExpectation hn β ρ hβ hρ s a ha has hq T
        (fun τ => F (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) τ)) u hu

end QuantitativeFollowup
