module
public import QuantitativePaper.ResponseTentConvergence

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

theorem tendsto_responseTentSignal_grid (μ ν : Paper.ParisiMeasure)
    (β t lam θ : ℝ) (ht : t<1) (hθ : θ∈Icc (0:ℝ) 1) (ell : ℝ) :
    Tendsto (fun j=>responseTentSignal (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le ell) atTop
      (nhds (responseTentSignal (n:=n) μ ν β t lam θ ht.le ell)):=by
  have hh:=tendsto_integral_response_tent_signal_grid (n:=n) μ ν (Paper.parisiMix μ ν θ) β t lam ht ell
  convert hh using 1
  · funext j
    unfold responseTentSignal
    rw [parisiGridMeasure_mix μ ν (vectorDyadicIndex j) θ hθ]
  · rfl

theorem tendsto_responseTentEnergyDenominator_grid (μ ν : Paper.ParisiMeasure)
    (β t lam θ : ℝ) (ht : t<1) (hθ : θ∈Icc (0:ℝ) 1) (ell : ℝ) :
    Tendsto (fun j=>responseTentEnergyDenominator (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le ell) atTop
      (nhds (responseTentEnergyDenominator (n:=n) μ ν β t lam θ ht.le ell)):=by
  have hb:=tendsto_integral_response_tent_mean_grid (n:=n) (Paper.parisiMix μ ν θ) β t lam ht.le ell
  have hz:=tendsto_integral_response_tent_curvature_grid (n:=n) (Paper.parisiMix μ ν θ) β t lam ht ell
  have hh:=hb.add ((tendsto_const_nhds (x:=2*(1-t)*β)).mul hz)
  convert hh using 1
  · funext j
    unfold responseTentEnergyDenominator
    rw [parisiGridMeasure_mix μ ν (vectorDyadicIndex j) θ hθ]
  · rfl


end QuantitativePaper
