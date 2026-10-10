module
public import QuantitativePaper.ResponseC1Convergence

@[expose] public section

/-! Literal response signal and denominator convergence for the genuine
common-grid measure mixtures, including the Stieltjes atom terms. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1200000

theorem tendsto_responseC1Signal_grid (μ ν : Paper.ParisiMeasure)
    (β t lam θ : ℝ) (ht : t<1) (hθ : θ∈Icc (0:ℝ) 1) (w : ResponseC1Test) :
    Tendsto (fun j=>responseC1Signal (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w) atTop
      (nhds (responseC1Signal (n:=n) μ ν β t lam θ ht.le w)):=by
  have hh:=tendsto_integral_response_C1_signal_grid (n:=n) μ ν (Paper.parisiMix μ ν θ) β t lam ht w
  convert hh using 1
  · funext j
    unfold responseC1Signal
    rw [parisiGridMeasure_mix μ ν (vectorDyadicIndex j) θ hθ]
  · rfl

theorem tendsto_responseC1EnergyDenominator_grid (μ ν : Paper.ParisiMeasure)
    (β t lam θ : ℝ) (ht : t<1) (hθ : θ∈Icc (0:ℝ) 1) (w : ResponseC1Test) :
    Tendsto (fun j=>responseC1EnergyDenominator (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w) atTop
      (nhds (responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w)):=by
  have hb:=tendsto_integral_response_C1_mean_grid (n:=n) (Paper.parisiMix μ ν θ) β t lam ht.le w
  have hz:=tendsto_integral_response_C1_curvature_grid (n:=n) (Paper.parisiMix μ ν θ) β t lam ht w
  have hh:=hb.add ((tendsto_const_nhds (x:=2*(1-t)*β)).mul hz)
  convert hh using 1
  · funext j
    unfold responseC1EnergyDenominator
    rw [parisiGridMeasure_mix μ ν (vectorDyadicIndex j) θ hθ]
  · rfl

theorem responseC1EnergyDenominator_nonneg (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β t lam θ : ℝ) (hβ : 0<β) (ht : t<1) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseC1Test) :
    0≤responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w:=by
  exact ge_of_tendsto (tendsto_responseC1EnergyDenominator_grid μ ν β t lam θ ht
    ⟨hθ.1.le,hθ.2.le⟩ w) (.of_forall fun j=>response_grid_C1_denominator_nonneg hn μ ν j
      β t lam θ hβ ht hθ w)

end QuantitativePaper
