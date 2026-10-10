module
public import QuantitativeFollowup.FollowupCavityStreamingFuture

@[expose] public section

/-! Conditional cavity scores depend on actual covariance inputs; changing
only the independently sampled root disorder leaves these functions equal. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityRecordedStreamingDefect_congr_input
    (D E : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (b c : ℝ)
    (hL : cavityFiniteEnergyInput (anisotropicReplaceVariance D (Fin.last n) b) s=
      cavityFiniteEnergyInput (anisotropicReplaceVariance E (Fin.last n) c) s)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityRecordedStreamingDefect n D s a T b r=cavityRecordedStreamingDefect n E s a T c r := by
  unfold cavityRecordedStreamingDefect cavityRecordedIncidentScore cavityRecordedIncidentCurrent
    cavityRecordedIncidentFuture cavityRecordedPathCurrent cavityRecordedPathFuture
    cavityPathRecordClockGram cavityPathRecordSignedMarks cavityPathRecordMean
    cavityPathRecordFutureSquare anisotropicVertexMean anisotropicVertexFutureSquare cavityFiniteFutureSquare
  change (fun j=>(anisotropicEnergyMap (anisotropicReplaceVariance D (Fin.last n) b)).comp
    (anisotropicSchemeInput (anisotropicReplaceVariance D (Fin.last n) b) s j))=
      (fun j=>(anisotropicEnergyMap (anisotropicReplaceVariance E (Fin.last n) c)).comp
        (anisotropicSchemeInput (anisotropicReplaceVariance E (Fin.last n) c) s j)) at hL
  unfold cavityFiniteEnergyInput
  simp_rw [hL]

theorem followupCavityPhysicalRecordScore_eq_actual_model_defect
    (n : ℕ) (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc 0 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (u : ℝ) (hu : u∈Icc 0 1)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    followupCavityPhysicalRecordScore n β ρ hβ hρ s a T u r=
      (followupCavityAlpha n β ρ/2)*cavityRecordedStreamingDefect n
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
          ((followupCavitySpinModel n β ρ hβ hρ u hu).variance (Fin.last n)) r := by
  rw [followupCavityPhysicalRecordScore_eq_overlap_defect n hn β ρ hβ hρ s a ha has hq T u r]
  apply congrArg (fun y : ℝ=>(followupCavityAlpha n β ρ/2)*y)
  let D0:=followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩
  let Du:=followupCavitySpinModel n β ρ hβ hρ u hu
  have hL : cavityFiniteEnergyInput (anisotropicReplaceVariance D0 (Fin.last n)
      (followupCavityB n β ρ u)) s=
      cavityFiniteEnergyInput (anisotropicReplaceVariance Du (Fin.last n) (Du.variance (Fin.last n))) s := by
    rw [anisotropicReplaceVariance_self]
    dsimp only [Du]
    rw [followupCavitySpinModel_eq_scaled_root_and_path n β ρ hβ hρ u hu]
    funext j
    exact (cavityFiniteEnergyInput_scaleRootCouplings_variance D0 (cavityIncidentRootMask n)
      u (Fin.last n) (followupCavityB n β ρ u) s j).symm
  exact cavityRecordedStreamingDefect_congr_input D0 Du s a T _ _ hL r

end QuantitativeFollowup
