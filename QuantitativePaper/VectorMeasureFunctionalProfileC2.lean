module
public import QuantitativePaper.VectorGridProfileFunctionalJetBounds
public import FourPapersCommon.ClosedSecondOrderUniformLimit

@[expose] public section

/-! Closed C² affine-profile regularity of the actual arbitrary-measure
fractional response functional. Every real outer tilt, including zero,
is handled by the genuine Gaussian normalized partition. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem responseEnergyFunctional_mix_closed_jets (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t lam : ℝ) (hβ : β≠0) (ht : t<1) :
    ∃D₁ D₂ : ℝ→ℝ,
      ContinuousOn D₁ (Icc (0:ℝ) 1) ∧ ContinuousOn D₂ (Icc (0:ℝ) 1) ∧
      TendstoUniformlyOn (fun j=>deriv (vectorGridProfileFunctional (n:=n) μ ν β t lam j)) D₁
        atTop (Icc (0:ℝ) 1) ∧
      TendstoUniformlyOn (fun j=>deriv (deriv (vectorGridProfileFunctional (n:=n) μ ν β t lam j))) D₂
        atTop (Icc (0:ℝ) 1) ∧
      (∀θ∈Icc (0:ℝ) 1,HasDerivWithinAt
        (fun φ=>responseEnergyFunctional n (Paper.parisiMix μ ν φ) β t lam)
          (D₁ θ) (Icc (0:ℝ) 1) θ) ∧
      (∀θ∈Icc (0:ℝ) 1,HasDerivWithinAt D₁ (D₂ θ) (Icc (0:ℝ) 1) θ) ∧
      ContDiffOn ℝ 2 (fun θ=>responseEnergyFunctional n (Paper.parisiMix μ ν θ) β t lam)
        (Icc (0:ℝ) 1) := by
  exact closed_second_order_uniform_limit (vectorGridProfileFunctional (n:=n) μ ν β t lam)
    (fun θ=>responseEnergyFunctional n (Paper.parisiMix μ ν θ) β t lam)
    (contDiff_vectorGridProfileFunctional μ ν β t lam)
    (vectorProfileFunctionalSecondJetBound n β t lam)
    (vectorProfileFunctionalThirdJetBound n β t lam)
    (vectorProfileFunctionalSecondJetBound_nonneg n β t lam ht.le)
    (vectorProfileFunctionalThirdJetBound_nonneg n β t lam ht.le)
    (fun j θ hθ=>abs_vectorGridProfileFunctional_second_deriv_le μ ν j β t hβ ht lam θ hθ)
    (fun j θ hθ=>abs_vectorGridProfileFunctional_third_deriv_le μ ν j β t hβ ht lam θ hθ)
    (tendstoUniformlyOn_vectorGridProfileFunctional hn μ ν β t lam ht.le)

theorem contDiffOn_responseEnergyFunctional_mix_two (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t lam : ℝ) (hβ : β≠0) (ht : t<1) :
    ContDiffOn ℝ 2 (fun θ=>responseEnergyFunctional n (Paper.parisiMix μ ν θ) β t lam)
      (Icc (0:ℝ) 1) := by
  obtain ⟨D₁,D₂,_,_,_,_,_,_,hC⟩:=responseEnergyFunctional_mix_closed_jets hn μ ν β t lam hβ ht
  exact hC

end QuantitativePaper
