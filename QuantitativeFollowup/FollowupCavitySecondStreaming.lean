module
public import QuantitativeFollowup.FollowupCavityChargedOriginalResponse
public import QuantitativeFollowup.FollowupCavityOriginalOriginalGraftResponse
public import QuantitativeFollowup.FollowupCavityFutureGraftResponseCharged
public import QuantitativeFollowup.FollowupCavityNormalizerGraftResponseStieltjes

@[expose] public section

/-! A genuine second application of the physical streaming law. The
complete first bracket is a sum of fixed-spin enlarged-tree families and
an independent product; every derivative below comes from those laws. -/
noncomputable section
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityFullTestToTrim (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (σ : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))) : ℝ :=
  F (trimmedSpinEquiv (S:=Configuration (n+1)) T σ)

def cavityFullTestToTerminal (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (σ : TerminalSpins (Configuration (n+1)) (trimRoot T)) : ℝ :=
  cavityFullTestToTrim T F (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) σ)

theorem cavityFullTestToTrim_record (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityFullTestToTrim T F (spins (trimRoot T) r.2)=followupCavityPhysicalRecordObservable n T F r := rfl

theorem cavityFullTestToTerminal_record (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityFullTestToTerminal T F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)=
      followupCavityPhysicalRecordObservable n T F r := by
  simp only [cavityFullTestToTerminal,terminalSampleEquiv_recordSpins]
  rfl

def followupCavityStreamingBracket (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ) (u : ℝ) : ℝ :=
  followupCavityOriginalOriginalSampleExpectation n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u-
    2*followupCavityOriginalGraftFamily n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u+
    followupCavityCrossGraftFamily n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u+
    followupCavityCurrentGraftFamily n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u+
    followupCavityFutureGraftStreamingExpectation n β ρ hβ hρ s a T (cavityFullTestToTerminal T F) u+
    followupCavitySixthGraftExpectation n β ρ hβ hρ s a T F u

theorem followupCavityStreamingBracket_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityStreamingBracket n β ρ hβ hρ s a T F u=
      cavityMarkedSixExpectation (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
        (followupCavityPhysicalRecordObservable n T F) := by
  unfold followupCavityStreamingBracket
  rw [followupCavityOriginalOriginalSampleExpectation_eq_record_integral β ρ hβ hρ s a hq T _ u hu,
    followupCavityOriginalGraftFamily_eq_actual β ρ hβ hρ s a hq T _ u hu,
    followupCavityCrossGraftFamily_eq_actual β ρ hβ hρ s a hq T _ u hu,
    followupCavityCurrentGraftFamily_eq_actual β ρ hβ hρ s a hq T _ u hu,
    followupCavityFutureGraftStreamingExpectation_eq_actual β ρ hβ hρ s a ha has hq T _ u hu,
    followupCavitySixthGraftExpectation_eq_actual β ρ hβ hρ s a ha has hq T F u hu]
  simp only [cavityFullTestToTrim_record,cavityFullTestToTerminal_record]
  rfl

def followupCavitySecondStreamingResponse (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : ℝ :=
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a T
      (fun r=>followupCavityPhysicalRecordObservable n T F r*cavityOriginalDistinctLeafDefect n s T r)-
    2*followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu+
    followupCavityCrossGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu+
    followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T (cavityFullTestToTrim T F) u hu+
    followupCavityAlpha n β ρ/2*followupCavityFutureGraftStreamingResponse D s a T (cavityFullTestToTerminal T F)+
    a*(followupCavityAlpha n β ρ/2)*
      (cavityMarkedSixExpectation D s a T (followupCavityPhysicalRecordObservable n T F)*
          cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
        (∫r,followupCavityPhysicalRecordObservable n T F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*
          cavityNormalizerGraftStreamingResponse D s a)

theorem hasDerivWithinAt_followupCavityStreamingBracket
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityStreamingBracket n β ρ hβ hρ s a T F)
      (followupCavitySecondStreamingResponse n β ρ hβ hρ s a T F u hu) (Icc (0:ℝ) 1) u := by
  have hOO:=hasDerivWithinAt_followupCavityOriginalOriginalSampleExpectation hn β ρ hβ hρ s a ha has hq T (cavityFullTestToTrim T F) u hu
  have hOF:=hasDerivWithinAt_followupCavityOriginalGraftFamily hn β ρ hβ hρ s a ha has hq T (cavityFullTestToTrim T F) u hu
  have hFF:=hasDerivWithinAt_followupCavityCrossGraftFamily hn β ρ hβ hρ s a ha has hq T (cavityFullTestToTrim T F) u hu
  have hCF:=hasDerivWithinAt_followupCavityCurrentGraftFamily hn β ρ hβ hρ s a ha has hq T (cavityFullTestToTrim T F) u hu
  have hFU:=hasDerivWithinAt_followupCavityFutureGraftStreamingExpectation hn β ρ hβ hρ s a ha has hq T (cavityFullTestToTerminal T F) u hu
  have hR:=hasDerivWithinAt_followupCavitySixthGraftExpectation hn β ρ hβ hρ s a ha has hq T F u hu
  have hh:=((((hOO.fun_sub (hOF.const_mul 2)).fun_add hFF).fun_add hCF).fun_add hFU).fun_add hR
  convert! hh using 1

theorem hasDerivWithinAt_followupCavityPhysicalExpectation_streamingBracket
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F)
      (followupCavityAlpha n β ρ/2*followupCavityStreamingBracket n β ρ hβ hρ s a T F u)
      (Icc (0:ℝ) 1) u := by
  rw [followupCavityStreamingBracket_eq_actual β ρ hβ hρ s a ha.1 has hq T F u hu]
  exact hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ s a ha has hq T F u hu

theorem hasDerivWithinAt_followupCavityPhysicalExpectation_derivWithin
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (derivWithin (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F) (Icc (0:ℝ) 1))
      (followupCavityAlpha n β ρ/2*followupCavitySecondStreamingResponse n β ρ hβ hρ s a T F u hu)
      (Icc (0:ℝ) 1) u := by
  have hh:=(hasDerivWithinAt_followupCavityStreamingBracket hn β ρ hβ hρ s a ha has hq T F u hu).const_mul
    (followupCavityAlpha n β ρ/2)
  have he : (derivWithin (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F) (Icc (0:ℝ) 1))=ᶠ[𝓝[Icc (0:ℝ) 1] u]
      (fun y=>followupCavityAlpha n β ρ/2*followupCavityStreamingBracket n β ρ hβ hρ s a T F y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hasDerivWithinAt_followupCavityPhysicalExpectation_streamingBracket hn β ρ hβ hρ s a ha has hq T F y hy).derivWithin
      (uniqueDiffOn_Icc_zero_one y hy)
  exact hh.congr_of_eventuallyEq_of_mem he hu

end QuantitativeFollowup
