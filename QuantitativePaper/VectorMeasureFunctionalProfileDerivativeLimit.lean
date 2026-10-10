module
public import QuantitativePaper.VectorMeasureFunctionalProfileC2

@[expose] public section

/-! The closed limiting jets are the literal ordinary functional derivatives
at every interior profile point. Hence actual finite curvature converges
uniformly there, without a curvature-limit assumption. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem tendstoUniformlyOn_responseEnergyFunctional_mix_derivatives (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t lam : ℝ) (hβ : β≠0) (ht : t<1) :
    TendstoUniformlyOn
      (fun j=>deriv (vectorGridProfileFunctional (n:=n) μ ν β t lam j))
      (deriv (fun θ=>responseEnergyFunctional n (Paper.parisiMix μ ν θ) β t lam))
      atTop (Ioo (0:ℝ) 1) ∧
    TendstoUniformlyOn
      (fun j=>deriv (deriv (vectorGridProfileFunctional (n:=n) μ ν β t lam j)))
      (deriv (deriv (fun θ=>responseEnergyFunctional n (Paper.parisiMix μ ν θ) β t lam)))
      atTop (Ioo (0:ℝ) 1) := by
  let f:=fun θ=>responseEnergyFunctional n (Paper.parisiMix μ ν θ) β t lam
  obtain ⟨D₁,D₂,_,_,hU₁,hU₂,hd₁,hd₂,_⟩:=
    responseEnergyFunctional_mix_closed_jets hn μ ν β t lam hβ ht
  have he₁ : EqOn D₁ (deriv f) (Ioo (0:ℝ) 1):=by
    intro θ hθ
    exact ((hd₁ θ ⟨hθ.1.le,hθ.2.le⟩).hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)).deriv.symm
  have he₂ : EqOn D₂ (deriv (deriv f)) (Ioo (0:ℝ) 1):=by
    intro θ hθ
    have he : deriv f=ᶠ[𝓝 θ] D₁:=by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
      exact (he₁ hy).symm
    exact (((hd₂ θ ⟨hθ.1.le,hθ.2.le⟩).hasDerivAt
      (Icc_mem_nhds hθ.1 hθ.2)).congr_of_eventuallyEq he).deriv.symm
  exact ⟨(hU₁.mono Ioo_subset_Icc_self).congr_right he₁,
    (hU₂.mono Ioo_subset_Icc_self).congr_right he₂⟩

end QuantitativePaper
