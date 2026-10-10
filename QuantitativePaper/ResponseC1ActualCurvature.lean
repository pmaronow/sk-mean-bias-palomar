module
public import QuantitativePaper.VectorMeasureFunctionalProfileDerivativeLimit
public import QuantitativePaper.ResponseC1Limits

@[expose] public section

/-! The actual arbitrary-measure second response satisfies the squared
C¹ test inequality. Genuine uniform functional-jet convergence identifies
the limiting finite curvature with the literal second derivative. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem tendsto_iteratedDeriv_two_response_grid_mix (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t lam θ : ℝ) (hβ : β≠0) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) :
    Tendsto (fun j=>iteratedDeriv 2 (fun y=>responseEnergyFunctional n
      (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) y) β t lam) θ) atTop
      (𝓝 (iteratedDeriv 2 (fun y=>responseEnergyFunctional n (Paper.parisiMix μ ν y)
        β t lam) θ)) := by
  have hu:=(tendstoUniformlyOn_responseEnergyFunctional_mix_derivatives hn μ ν β t lam hβ ht).2.tendsto_at hθ
  have he (j : ℕ) : (fun y=>responseEnergyFunctional n
      (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) y) β t lam)=ᶠ[𝓝 θ]
      vectorGridProfileFunctional (n:=n) μ ν β t lam j := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
    have hyc : y∈Icc (0:ℝ) 1:=⟨hy.1.le,hy.2.le⟩
    rw [←parisiGridMeasure_mix μ ν (vectorDyadicIndex j) y hyc,
      ←vectorProfile_grid_functional_eq μ ν j β t lam y ht.le hyc,
      vectorProfileFiniteEnergyFunctional_eq_affine _ _ β t lam y hyc]
    rfl
  have heq : (fun j=>iteratedDeriv 2 (fun y=>responseEnergyFunctional n
      (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) y) β t lam) θ)=
      (fun j=>deriv (deriv (vectorGridProfileFunctional (n:=n) μ ν β t lam j)) θ):=by
    funext j
    rw [(he j).iteratedDeriv_eq 2]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [heq]
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hu

theorem response_C1_actual_functional_curvature_bound (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t lam θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hlam : 0≤lam) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseC1Test) :
    (1-t)^3*(responseC1Signal (n:=n) μ ν β t lam θ ht.le w)^2≤
      iteratedDeriv 2 (fun y=>responseEnergyFunctional n (Paper.parisiMix μ ν y) β t lam) θ*
        responseC1EnergyDenominator (n:=n) μ ν β t lam θ ht.le w := by
  have hc:=tendsto_iteratedDeriv_two_response_grid_mix hn μ ν β t lam θ hβ.ne' ht hθ
  have hs:=tendsto_responseC1Signal_grid (n:=n) μ ν β t lam θ ht ⟨hθ.1.le,hθ.2.le⟩ w
  have hd:=tendsto_responseC1EnergyDenominator_grid (n:=n) μ ν β t lam θ ht ⟨hθ.1.le,hθ.2.le⟩ w
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul (hs.pow 2)) (hc.mul hd)
    (.of_forall fun j=>response_grid_C1_functional_curvature_bound hn μ ν j β t lam θ hβ ht hlam hθ w)

end QuantitativePaper
