module
public import QuantitativePaper.VectorNoisePathTrajectoryStability

@[expose] public section

/-! Drift equality along a fixed initial parameter gives actual path equality.
This uses the constructed Picard equations and uniqueness. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 350000

theorem vectorNoiseStatePath_drift_congr (d e : VectorAdditiveDriftData n)
    (σ : ℝ) (T : ℝ≥0) (p q : Couplings n×ℝ) (x : Field n) (W : VectorWienerPath n)
    (hde : ∀u : ℝ≥0,u≤T→∀y,d.drift u p y=e.drift u q y)
    (r : ℝ) (hr : r∈Icc (0:ℝ) T) :
    vectorNoiseStatePath d σ T ((p,x),W) r=vectorNoiseStatePath e σ T ((q,x),W) r := by
  have hh:=norm_vectorNoiseStatePath_sub_le_of_trajectory_forcing d e σ T p q x x W
    (fun _=>0) (intervalIntegrable_const) (fun _ _=>le_rfl)
    (fun u hu=>by rw [hde u hu];simp) r hr
  have hn : ‖vectorNoiseStatePath d σ T ((p,x),W) r-
      vectorNoiseStatePath e σ T ((q,x),W) r‖≤0 := by simpa using hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

end QuantitativePaper
