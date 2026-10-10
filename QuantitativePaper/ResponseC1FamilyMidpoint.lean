module
public import QuantitativePaper.ResponseC1Midpoint

@[expose] public section

/-! Pointwise adaptive C¹ response tests. A different genuine test may be
selected at each profile parameter; Fatou acts on the actual measurable
finite curvature densities, so no measurable selection is needed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1800000

theorem response_C1_family_midpoint_lower (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β t lam C a : ℝ) (hβ : 0<β) (ht : t<1) (hlam : 0≤lam)
    (hC : 0≤C) (ha : 0≤a) (ham : a≤1/2)
    (htests : ∀θ∈Ioo a (1-a),∃w : ResponseC1Test,∃Y : ℝ,0<Y ∧
      responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w≤Y ∧
      C*Y≤(1-t)^3*(responseC1Signal (n:=n) μ ν β t lam θ ht.le w)^2) :
    C*(1/4-a^2)≤responseEnergyFunctional n μ β t lam+
      responseEnergyFunctional n ν β t lam-
        2*responseEnergyFunctional n (Paper.parisiMix μ ν (1/2)) β t lam:=by
  let F₂:=fun j=>iteratedDeriv 2 (responseGridMixFunctional (n:=n) μ ν j β t lam)
  let Gapj:=fun j=>responseGridMixFunctional (n:=n) μ ν j β t lam 0+
    responseGridMixFunctional (n:=n) μ ν j β t lam 1-2*responseGridMixFunctional (n:=n) μ ν j β t lam (1/2)
  have hg:=((tendsto_responseGridMixFunctional hn μ ν β t lam 0 ht.le (by norm_num)).add
    (tendsto_responseGridMixFunctional hn μ ν β t lam 1 ht.le (by norm_num))).sub
      ((tendsto_const_nhds (x:=2)).mul
        (tendsto_responseGridMixFunctional hn μ ν β t lam (1/2) ht.le (by norm_num)))
  have hg' : Tendsto Gapj atTop (nhds (responseEnergyFunctional n μ β t lam+
      responseEnergyFunctional n ν β t lam-2*responseEnergyFunctional n (Paper.parisiMix μ ν (1/2)) β t lam)):=by
    simpa only [Gapj,Paper.parisiMix_zero,Paper.parisiMix_one] using hg
  refine response_midpoint_of_curvature_limit_lower F₂ Gapj _ C a hC ha ham
    (fun j=>(responseGridMix_weighted_curvature_bound hn μ ν j β t lam hβ ht hlam).1)
    (fun j θ hθ=>iteratedDeriv2_vectorGridResponseFunctional_mix_nonneg hn μ ν j β t lam θ hβ ht hlam hθ)
    (fun j=>(responseGridMix_weighted_curvature_bound hn μ ν j β t lam hβ ht hlam).2) hg' ?_
  intro θ hθ
  obtain ⟨w,Y,hY,hD,hSig⟩:=htests θ hθ
  have hθ01 : θ∈Ioo (0:ℝ) 1:=⟨ha.trans_lt hθ.1,by linarith [hθ.2]⟩
  exact response_curvature_lower_sequence
    (fun j=>responseC1Signal (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w)
    (fun j=>responseC1EnergyDenominator (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) β t lam θ ht.le w)
    (fun j=>F₂ j θ) (responseC1Signal (n:=n) μ ν β t lam θ ht.le w)
    (responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w) Y ((1-t)^3) C
    (tendsto_responseC1Signal_grid μ ν β t lam θ ht ⟨hθ01.1.le,hθ01.2.le⟩ w)
    (tendsto_responseC1EnergyDenominator_grid μ ν β t lam θ ht ⟨hθ01.1.le,hθ01.2.le⟩ w)
    hY hD hSig
    (fun j=>iteratedDeriv2_vectorGridResponseFunctional_mix_nonneg hn μ ν j β t lam θ hβ ht hlam hθ01)
    (fun j=>response_grid_C1_functional_curvature_bound hn μ ν j β t lam θ hβ ht hlam hθ01 w)

theorem response_C1_family_full_midpoint_lower (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β t lam C : ℝ) (hβ : 0<β) (ht : t<1) (hlam : 0≤lam) (hC : 0≤C)
    (htests : ∀θ∈Ioo (0:ℝ) 1,∃w : ResponseC1Test,∃Y : ℝ,0<Y ∧
      responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w≤Y ∧
      C*Y≤(1-t)^3*(responseC1Signal (n:=n) μ ν β t lam θ ht.le w)^2) :
    C/4≤responseEnergyFunctional n μ β t lam+
      responseEnergyFunctional n ν β t lam-
        2*responseEnergyFunctional n (Paper.parisiMix μ ν (1/2)) β t lam:=by
  have hh:=response_C1_family_midpoint_lower hn μ ν β t lam C 0 hβ ht hlam hC
    (by norm_num) (by norm_num) (by simpa using htests)
  convert hh using 1 <;> ring

end QuantitativePaper
