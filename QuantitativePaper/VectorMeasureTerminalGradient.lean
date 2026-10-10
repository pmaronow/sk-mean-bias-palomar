module
public import QuantitativePaper.VectorMeasureGradient
public import QuantitativePaper.VectorAffineControl
public import QuantitativePaper.VectorTerminalStrict

@[expose] public section

/-! The actual arbitrary-profile endpoint gradient is the true finite-spin
Gibbs magnetization, with strict endpoint overlap at positive system size. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 500000
variable {n : ℕ}

theorem vectorMeasureGradient_one (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureGradient μ β t 1 p x=
      WithLp.toLp 2 (vectorTerminalMagnetization n β t p x) := by
  have he : vectorMeasureTailPotential μ β t 1 p=vectorTerminalPotential n β t p :=
    funext (vectorMeasureTailPotential_one μ β t ht p)
  rw [vectorMeasureGradient_eq_gradient μ β t ht]
  change gradient (vectorMeasureTailPotential μ β t 1 p) x=_
  rw [he]
  change gradient (vectorTerminalPotential n β t p) x=
    WithLp.toLp 2 (fun i=>terminalMean (vectorTerminalExponent n β t p x)
      (fun σ=>Paper.spinSign (σ i)))
  simpa only [vectorTerminalGradient,vectorMagnetization,vectorObservableResponse,
    vectorTerminalObservable,terminalTilt_zero,vectorTerminalMagnetization] using
      vectorTerminalGradient_eq_magnetization β t p x

theorem vectorMeasureGradient_one_norm_sq_lt (μ : Paper.ParisiMeasure) (hn : 0<n)
    (β t : ℝ) (ht : t≤1) (p : Couplings n×ℝ) (x : Field n) :
    ‖vectorMeasureGradient μ β t 1 p x‖^2<(n : ℝ) := by
  rw [vectorMeasureGradient_one μ β t ht]
  exact vectorTerminalMagnetization_norm_sq_lt hn β t p x

end QuantitativePaper
