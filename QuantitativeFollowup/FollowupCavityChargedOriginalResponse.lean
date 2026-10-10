module
public import QuantitativeFollowup.FollowupCavityChargedCrossResponse
public import QuantitativeFollowup.FollowupCavitySingleGraftResponse

@[expose] public section

/-! The original--fresh branch is a fixed charge sum of actual
single-continuation tree expectations. Its derivative is obtained from
the physical streaming law of each enlarged tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityOriginalGraftPairObservable (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (z : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) × Configuration (n+1)) : ℝ :=
  F z.1*cavityOriginalVertexOverlapSum n s T v
    ((terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm z.1) z.2

theorem cavityOriginalGraftPairObservable_record
    (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (z : CavityPathRecordSpace (trimRoot T) (n+1) × Configuration (n+1)) :
    cavityOriginalGraftPairObservable s T v F (spins (trimRoot T) z.1.2,z.2)=
      F (spins (trimRoot T) z.1.2)*cavityOriginalVertexOverlapSum n s T v
        (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2) z.2 := by
  unfold cavityOriginalGraftPairObservable
  rw [←terminalSampleEquiv_recordSpins,
    (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm_apply_apply]

def followupCavityOriginalGraftFamily (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c =>
    c.1*followupCavityPhysicalExpectation n β ρ hβ hρ s a (.advance (finiteCascadeVertexGraft c.2))
      (cavitySingleGraftSampleObservable T c.2 (cavityOriginalGraftPairObservable s T c.2 F)) u)).sum

def followupCavityOriginalGraftDerivative (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c =>
    c.1*(followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
      (followupCavitySpinModel n β ρ hβ hρ u hu) s a (.advance (finiteCascadeVertexGraft c.2))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft c.2))
        (cavitySingleGraftSampleObservable T c.2 (cavityOriginalGraftPairObservable s T c.2 F)))))).sum

theorem followupCavityOriginalGraftFamily_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    followupCavityOriginalGraftFamily n β ρ hβ hρ s a T F u=
      cavityOriginalFreshExpectation (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
        (fun r => F (spins (trimRoot T) r.2)) := by
  unfold followupCavityOriginalGraftFamily cavityOriginalFreshExpectation
  simp_rw [followupCavitySingleGraftExpectation_eq_marked β ρ hβ hρ s a hq T _ _ u hu,
    cavityOriginalGraftPairObservable_record]

theorem hasDerivWithinAt_followupCavityOriginalGraftFamily
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (followupCavityOriginalGraftFamily n β ρ hβ hρ s a T F)
      (followupCavityOriginalGraftDerivative n β ρ hβ hρ s a T F u hu) (Icc (0 : ℝ) 1) u := by
  have hh := hasDerivWithinAt_weighted_list
    (finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T))
    (fun v => followupCavityPhysicalExpectation n β ρ hβ hρ s a (.advance (finiteCascadeVertexGraft v))
      (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)))
    (fun v => followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
      (followupCavitySpinModel n β ρ hβ hρ u hu) s a (.advance (finiteCascadeVertexGraft v))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
        (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)))) (Icc (0 : ℝ) 1) u
    (fun v => hasDerivWithinAt_followupCavitySingleGraftExpectation hn β ρ hβ hρ s a ha has hq T v _ u hu)
  unfold followupCavityOriginalGraftFamily followupCavityOriginalGraftDerivative
  convert! hh using 1

end QuantitativeFollowup
