module
public import QuantitativeFollowup.FollowupCavityInterpolationCovariance
public import QuantitativeFollowup.FollowupCavityIncidentIndexSum

@[expose] public section

/-! The true simultaneous derivative of the physical one-site row model.
It is an actual retained-record covariance, before the separate conditional
mark expansion and the variance-zero endpoint passage. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def followupCavityPhysicalExpectation (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc 0 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ) (u : ℝ) : ℝ:=
  cavityInterpolationMarkedExpectation
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
    (cavityIncidentRootMask n) s a (Fin.last n) (trimRoot T)
    (fun σ=>F (trimmedSpinEquiv (S:=Configuration (n+1)) T
      (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) σ)))
    u (followupCavityB n β ρ u)

theorem followupCavityPhysicalExpectation_eq_actual (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc 0 1) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc 0 1) :
    followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u=
      ∫σ,F σ∂anisotropicFiniteTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a (asGenealogy T) :=
  (followupCavityTreeExpectation_eq_interpolation n β ρ hβ hρ s a hq T F u hu).symm

theorem followupCavity_interpolation_recordedLaw_eq_actual (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc 0 1) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (u : ℝ) (hu : u∈Icc 0 1) :
    cavityInterpolationRecordedLaw
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
      (cavityIncidentRootMask n) s a (Fin.last n) (trimRoot T) u (followupCavityB n β ρ u)=
    anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T := by
  unfold cavityInterpolationRecordedLaw cavityPathRecordedLaw anisotropicTrimmedRecordedTreeLaw
  rw [followupCavitySpinModel_eq_scaled_root_and_path n β ρ hβ hρ u hu,
    anisotropicRootEnergyMap_replaceVariance]
  rfl

def followupCavityPhysicalRecordObservable (n : ℕ) {k : ℕ}
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ:=
  F (trimmedSpinEquiv (S:=Configuration (n+1)) T (spins (trimRoot T) r.2))

def followupCavityPhysicalRecordScore (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc 0 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (u : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ:=
  cavityInterpolationRecordScore
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
    (cavityIncidentRootMask n) s a (Fin.last n) (trimRoot T)
    (followupCavityAlpha n β ρ) (followupCavityB n β ρ u) r

theorem hasDerivAt_followupCavityPhysicalExpectation_recorded_covariance (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc 0 1) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Ioc 0 1) :
    HasDerivAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F)
      ((∫r,followupCavityPhysicalRecordObservable n T F r*followupCavityPhysicalRecordScore n β ρ hβ hρ s a T u r
          ∂anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩) s a T)-
        followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u*
          (∫r,followupCavityPhysicalRecordScore n β ρ hβ hρ s a T u r
            ∂anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩) s a T)) u := by
  classical
  have hb : 0<followupCavityB n β ρ u:=
    (mul_pos (sq_pos_of_pos hβ) hρ.1).trans_le (followupCavityB_window n β ρ u hρ.2 ⟨hu.1.le,hu.2⟩).1
  have h:=hasDerivAt_cavityInterpolationMarkedExpectation_recorded_covariance
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
    (cavityIncidentRootMask n) s a (Fin.last n) (trimRoot T) (by omega)
    (fun σ=>F (trimmedSpinEquiv (S:=Configuration (n+1)) T
      (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) σ)))
    (followupCavityD n β ρ) (followupCavityAlpha n β ρ) u
    (followupCavityAlpha_nonneg n β ρ hρ.2) hu.1 hb
  change HasDerivAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F) _ u at h
  have hm:=followupCavity_interpolation_recordedLaw_eq_actual n β ρ hβ hρ s a T u ⟨hu.1.le,hu.2⟩
  dsimp only [followupCavityB] at hm
  rw [hm] at h
  convert! h using 1
  congr 1
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only [followupCavityPhysicalRecordObservable,followupCavityPhysicalRecordScore,followupCavityB]
    rw [terminalSampleEquiv_recordSpins]

end QuantitativeFollowup
