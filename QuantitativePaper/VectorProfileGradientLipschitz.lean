module
public import QuantitativePaper.VectorProfileUniformGradientVariation
public import QuantitativePaper.VectorProfileEndpointInverse
public import QuantitativePaper.VectorMeasureGradient
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-! Genuine profile-Lipschitz continuity of the arbitrary-measure field
gradient, obtained from depth-independent actual finite score estimates.
This assertion does not substitute for profile second differentiability. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorGridProfileTailGradient_lipschitzOn_profile
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    LipschitzOnWith (vectorProfileGradientVariationBound n β t).toNNReal
      (fun θ=>gradient (vectorProfileTailRecursion
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t q θ p
          (vectorDyadicIndex j+3)) x) (Icc (0:ℝ) 1) := by
  let d:=vectorDyadicIndex j
  let s₀:=Paper.parisiGridRSBScheme μ d
  let s₁:=Paper.parisiGridRSBScheme ν d
  let f : ℝ→Field n:=fun θ=>gradient (vectorProfileTailRecursion s₀ s₁ β t q θ p (d+3)) x
  have hs (θ : ℝ) : ContDiffAt ℝ ∞ f θ := by
    have hG:=contDiffAt_vectorProfileJointGradient_all_theta s₀ s₁ β t q (d+3) le_rfl ((θ,p),x)
    exact ContDiffAt.comp (f := fun φ : ℝ=>((φ,p),x))
      (g := vectorProfileJointGradient s₀ s₁ β t q (d+3)) θ hG (by fun_prop)
  have hc : Continuous f:=continuous_iff_continuousAt.mpr fun θ=>(hs θ).continuousAt
  have hK:=vectorProfileGradientVariationBound_nonneg n β t ht.le
  have hLip : LipschitzOnWith (vectorProfileGradientVariationBound n β t).toNNReal f (Ioo (0:ℝ) 1) := by
    apply (convex_Ioo (0:ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
      (fun θ _=>(hs θ).differentiableAt (by simp))
    intro θ hθ
    rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal _ hK]
    exact norm_vectorGridProfileTailRecursion_gradient_profile_deriv_le μ ν j β t hβ ht q p x θ hθ
  simpa only [closure_Ioo zero_ne_one] using hLip.closure hc.continuousOn

theorem vectorGridProfileTailGradient_tendsto_mix (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    Tendsto (fun j=>gradient (vectorProfileTailRecursion
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t q θ p
        (vectorDyadicIndex j+3)) x) atTop
      (𝓝 (vectorMeasureGradient (Paper.parisiMix μ ν θ) β t q p x)) := by
  have he (j : ℕ) : gradient (vectorProfileTailRecursion
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t q θ p
        (vectorDyadicIndex j+3)) x=vectorDyadicTailGradient (Paper.parisiMix μ ν θ) β t q j p x := by
    rw [vectorProfileTailRecursion_eq_scheme _ _ β t q θ hθ,
      vector_grid_profile_scheme_eq_mix μ ν (vectorDyadicIndex j) θ hθ]
    rfl
  simp_rw [he]
  exact tendsto_vectorDyadicTailGradient (Paper.parisiMix μ ν θ) β t ht q p x

theorem vectorMeasureGradient_mix_lipschitzOn_profile
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    LipschitzOnWith (vectorProfileGradientVariationBound n β t).toNNReal
      (fun θ=>vectorMeasureGradient (Paper.parisiMix μ ν θ) β t q p x) (Icc (0:ℝ) 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro θ hθ φ hφ
  apply le_of_tendsto ((vectorGridProfileTailGradient_tendsto_mix μ ν β t ht.le q p x θ hθ).dist
    (vectorGridProfileTailGradient_tendsto_mix μ ν β t ht.le q p x φ hφ))
  exact .of_forall fun j=>
    (vectorGridProfileTailGradient_lipschitzOn_profile μ ν j β t hβ ht q p x).dist_le_mul θ hθ φ hφ

end QuantitativePaper
