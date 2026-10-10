module
public import QuantitativePaper.ResponseGridMidpoint
public import QuantitativePaper.ResponseC1Limits

@[expose] public section

/-! Closed response bounds for arbitrary probability measures. Actual finite
Gaussian response estimates, weak-measure convergence, and Fatou's lemma
supply the bound without assuming second differentiability of the limit. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1800000

theorem response_C1_midpoint_lower (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β t lam : ℝ) (hβ : 0<β) (ht : t<1) (hlam : 0≤lam)
    (w : ResponseC1Test) (Y : ℝ→ℝ) (C a : ℝ)
    (hC : 0≤C) (ha : 0≤a) (ham : a≤1/2)
    (hY : ∀θ∈Ioo a (1-a),0<Y θ)
    (hD : ∀θ∈Ioo a (1-a),responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w≤Y θ)
    (hS : ∀θ∈Ioo a (1-a),C*Y θ≤(1-t)^3*
      (responseC1Signal (n:=n) μ ν β t lam θ ht.le w)^2) :
    C*(1/4-a^2)≤responseEnergyFunctional n μ β t lam+
      responseEnergyFunctional n ν β t lam-
        2*responseEnergyFunctional n (Paper.parisiMix μ ν (1/2)) β t lam:=by
  apply response_midpoint_lower_of_grid_response hn μ ν β t lam hβ ht hlam
    (fun j θ=>responseC1Signal (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w)
    (fun j θ=>responseC1EnergyDenominator (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w)
    (fun θ=>responseC1Signal (n:=n) μ ν β t lam θ ht.le w)
    (fun θ=>responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w) Y C a hC ha ham
  · intro θ hθ
    exact tendsto_responseC1Signal_grid μ ν β t lam θ ht ⟨hθ.1.le,hθ.2.le⟩ w
  · intro θ hθ
    exact tendsto_responseC1EnergyDenominator_grid μ ν β t lam θ ht ⟨hθ.1.le,hθ.2.le⟩ w
  · intro j θ hθ
    exact response_grid_C1_functional_curvature_bound hn μ ν j β t lam θ hβ ht hlam hθ w
  · exact hY
  · exact hD
  · exact hS

theorem response_C1_middle_midpoint_lower (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β t lam : ℝ) (hβ : 0<β) (ht : t<1) (hlam : 0≤lam)
    (w : ResponseC1Test) (Y : ℝ→ℝ) (C : ℝ) (hC : 0≤C)
    (hY : ∀θ∈Ioo (1/4:ℝ) (3/4),0<Y θ)
    (hD : ∀θ∈Ioo (1/4:ℝ) (3/4),responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w≤Y θ)
    (hS : ∀θ∈Ioo (1/4:ℝ) (3/4),C*Y θ≤(1-t)^3*
      (responseC1Signal (n:=n) μ ν β t lam θ ht.le w)^2) :
    3*C/16≤responseEnergyFunctional n μ β t lam+
      responseEnergyFunctional n ν β t lam-
        2*responseEnergyFunctional n (Paper.parisiMix μ ν (1/2)) β t lam:=by
  have hh:=response_C1_midpoint_lower hn μ ν β t lam hβ ht hlam w Y C (1/4) hC
    (by norm_num) (by norm_num) (by norm_num at *; exact hY) (by norm_num at *; exact hD) (by norm_num at *; exact hS)
  convert hh using 1 <;> ring

theorem response_C1_full_midpoint_lower (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β t lam : ℝ) (hβ : 0<β) (ht : t<1) (hlam : 0≤lam)
    (w : ResponseC1Test) (Y : ℝ→ℝ) (C : ℝ) (hC : 0≤C)
    (hY : ∀θ∈Ioo (0:ℝ) 1,0<Y θ)
    (hD : ∀θ∈Ioo (0:ℝ) 1,responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w≤Y θ)
    (hS : ∀θ∈Ioo (0:ℝ) 1,C*Y θ≤(1-t)^3*
      (responseC1Signal (n:=n) μ ν β t lam θ ht.le w)^2) :
    C/4≤responseEnergyFunctional n μ β t lam+
      responseEnergyFunctional n ν β t lam-
        2*responseEnergyFunctional n (Paper.parisiMix μ ν (1/2)) β t lam:=by
  have hh:=response_C1_midpoint_lower hn μ ν β t lam hβ ht hlam w Y C 0 hC
    (by norm_num) (by norm_num) (by norm_num at *; exact hY) (by norm_num at *; exact hD) (by norm_num at *; exact hS)
  convert hh using 1 <;> ring

end QuantitativePaper
