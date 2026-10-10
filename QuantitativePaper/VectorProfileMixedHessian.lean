module
public import QuantitativePaper.VectorProfileHessianVariations
public import FourPapersCommon.PartialHessianCommutation

@[expose] public section

/-! The profile jets in the inverse-Hessian variations are the actual
spatial Hessians of the first and second Legendre variations. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileLegendreFirstVariation (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n) : ℝ:=
  deriv (fun α=>vectorProfileEnergyLegendrePotential s₀ s₁ β t q j α p m) θ

def vectorProfileLegendreSecondVariation (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n) : ℝ:=
  deriv (deriv (fun α=>vectorProfileEnergyLegendrePotential s₀ s₁ β t q j α p m)) θ

def vectorProfileLegendreB (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n) : Field n→L[ℝ]Field n:=
  hessianOperator (vectorProfileLegendreFirstVariation s₀ s₁ β t q j θ p) m

theorem contDiffAt_vectorProfileEnergyLegendre_theta_m (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (j : ℕ) (hj : j ≤ k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0 : ℝ) 1) (p : Couplings n×ℝ)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : ℝ×Field n=>
      vectorProfileEnergyLegendrePotential s₀ s₁ β t q j z.1 p z.2) (θ,m):=
  ContDiffAt.comp (f := fun z : ℝ×Field n=>((z.1,p),z.2))
    (g := fun z : VectorProfileParameter n×Field n=>
      vectorProfileEnergyLegendrePotential s₀ s₁ β t q j z.1.1 z.1.2 z.2) (θ,m)
    (contDiffAt_vectorProfileEnergyLegendrePotential_joint s₀ s₁ β t ht q j hj (θ,p) hθ m hm)
    (by fun_prop)

theorem deriv_vectorProfileEnergyHessian_eq_B (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (j : ℕ) (hj : j ≤ k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0 : ℝ) 1) (p : Couplings n×ℝ)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun α=>vectorProfileEnergyHessian s₀ s₁ β t q j α p m) θ=
      vectorProfileLegendreB s₀ s₁ β t q j θ p m :=
  deriv_partial_hessian _ θ m
    (contDiffAt_vectorProfileEnergyLegendre_theta_m s₀ s₁ β t ht q j hj θ hθ p m hm)

theorem deriv_deriv_vectorProfileEnergyHessian (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (j : ℕ) (hj : j ≤ k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0 : ℝ) 1) (p : Couplings n×ℝ)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (deriv (fun α=>vectorProfileEnergyHessian s₀ s₁ β t q j α p m)) θ=
      hessianOperator (vectorProfileLegendreSecondVariation s₀ s₁ β t q j θ p) m := by
  let U : ℝ×Field n→ℝ:=fun z=>vectorProfileEnergyLegendrePotential s₀ s₁ β t q j z.1 p z.2
  have hU : ContDiffAt ℝ ∞ U (θ,m):=
    contDiffAt_vectorProfileEnergyLegendre_theta_m s₀ s₁ β t ht q j hj θ hθ p m hm
  have he : deriv (fun α=>vectorProfileEnergyHessian s₀ s₁ β t q j α p m)=ᶠ[𝓝 θ]
      (fun α=>hessianOperator (fun y=>deriv (fun δ=>U (δ,y)) α) m):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with α hα
    exact deriv_vectorProfileEnergyHessian_eq_B s₀ s₁ β t ht q j hj α hα p m hm
  rw [he.deriv_eq]
  exact deriv_partial_hessian (partialParamDerivative (1 : ℝ) U) θ m
    (contDiffAt_partialParamDerivative 1 U (θ,m) hU)

theorem hasDerivAt_vectorProfilePhysicalHessian_B (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t ≤ 1) (q : Paper.Overlap) (j : ℕ) (hj : j ≤ k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0 : ℝ) 1) (p : Couplings n×ℝ)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun α=>vectorProfilePhysicalHessian s₀ s₁ β t q j α p m)
      (-(vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m)*
        vectorProfileLegendreB s₀ s₁ β t q j θ p m*
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m) θ := by
  rw [←deriv_vectorProfileEnergyHessian_eq_B s₀ s₁ β t ht q j hj θ hθ p m hm]
  exact hasDerivAt_vectorProfilePhysicalHessian_parameter s₀ s₁ β t hβ ht q j hj θ hθ p m hm

theorem hasDerivAt_deriv_vectorProfilePhysicalHessian_B_z (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t ≤ 1) (q : Paper.Overlap) (j : ℕ) (hj : j ≤ k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0 : ℝ) 1) (p : Couplings n×ℝ)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (deriv (fun α=>vectorProfilePhysicalHessian s₀ s₁ β t q j α p m))
      ((2 : ℝ) • (vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m*
        vectorProfileLegendreB s₀ s₁ β t q j θ p m*
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m*
        vectorProfileLegendreB s₀ s₁ β t q j θ p m*
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m)-
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m*
        hessianOperator (vectorProfileLegendreSecondVariation s₀ s₁ β t q j θ p) m*
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m) θ := by
  rw [←deriv_vectorProfileEnergyHessian_eq_B s₀ s₁ β t ht q j hj θ hθ p m hm,
    ←deriv_deriv_vectorProfileEnergyHessian s₀ s₁ β t ht q j hj θ hθ p m hm]
  exact hasDerivAt_deriv_vectorProfilePhysicalHessian_parameter s₀ s₁ β t hβ ht q j hj θ hθ p m hm

end QuantitativePaper
