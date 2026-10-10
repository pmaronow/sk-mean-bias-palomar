module
public import QuantitativeFollowup.FollowupCavityNativeComparison

@[expose] public section

/-! Literal terminal-spin tests of the finite physical cavity law are
the corresponding tests of its complete retained Gaussian records. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityTerminalSampleObservable {j : ℕ} (T : FiniteTerminalGenealogy j)
    (F : TerminalSpins (Configuration n) T → ℝ)
    (σ : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy T)) : ℝ :=
  F ((terminalSampleEquiv (S := Configuration n) T).symm σ)

theorem followupCavityPhysicalExpectation_terminal_integral
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    followupCavityPhysicalExpectation n β ρ hβ hρ s a T (cavityTerminalSampleObservable T F) u =
      ∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T := by
  let G := cavityTerminalSampleObservable T F
  rw [followupCavityPhysicalExpectation_eq_actual n β ρ hβ hρ s a hq T G u hu,
    ←anisotropicFiniteRecordedTreeLaw_spin_marginal]
  have hG : Measurable G := (measurable_of_finite F).comp (terminalSampleEquiv (S := Configuration (n+1)) T).symm.measurable
  rw [integral_map (φ := fun z : CavityPathRecordSpace T (n+1) => spins T z.2)
    ((measurable_spins T).comp measurable_snd).aemeasurable hG.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun z => by
    dsimp only [G,cavityTerminalSampleObservable]
    rw [←terminalSampleEquiv_recordSpins,(terminalSampleEquiv (S := Configuration (n+1)) T).symm_apply_apply]

end QuantitativeFollowup
