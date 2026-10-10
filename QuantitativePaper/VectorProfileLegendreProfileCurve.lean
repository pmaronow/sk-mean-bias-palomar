module
public import QuantitativePaper.VectorProfileFieldSources

@[expose] public section

/-! The actual profile derivative of the chosen Legendre inverse is obtained
from its genuine gradient stationarity equation on the strict cell. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem hasDerivAt_vectorProfileCellLegendreField_profile_curve
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun θ=>vectorProfileCellLegendreField s₀ s₁ β t i ((a.1,θ,a.2.2),m))
      (-((Ring.inverse (hessianOperator
        (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i (a,x))
        (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))))
        (gradient (fun x=>deriv (fun θ=>vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,θ,a.2.2),x)) a.2.1)
          (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))))) a.2.1 := by
  let U : ℝ×Field n→ℝ:=fun z=>vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,z.1,a.2.2),z.2)
  let Y : ℝ→Field n:=fun θ=>vectorProfileCellLegendreField s₀ s₁ β t i ((a.1,θ,a.2.2),m)
  have hU : ContDiffAt ℝ ∞ U (a.2.1,Y a.2.1):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((a.1,z.1,a.2.2),z.2))
    (g := vectorProfileCellJointPotential s₀ s₁ β t i) (a.2.1,Y a.2.1)
    (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,Y a.2.1) hq.2 hθ)
    (by fun_prop)
  have hY : ContDiffAt ℝ ∞ Y a.2.1:=ContDiffAt.comp
    (f := fun θ : ℝ=>((a.1,θ,a.2.2),m))
    (g := vectorProfileCellLegendreField s₀ s₁ β t i) a.2.1
    (contDiffAt_vectorProfileCellLegendreField s₀ s₁ β t hβ ht i hi a hq hθ m hm)
    (by fun_prop)
  have hStationary : (fun θ=>gradient (fun x=>U (θ,x)) (Y θ))=ᶠ[𝓝 a.2.1](fun _=>m):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    change vectorProfileCellJointGradient s₀ s₁ β t i ((a.1,θ,a.2.2),Y θ)=m
    rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi (a.1,θ,a.2.2)
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ'.1.le,hθ'.2.le⟩]
    exact vectorMagnetization_legendreField _ β t a.2.2 (k+2) m hm
  have hUnit : IsUnit (hessianOperator (fun x=>U (a.2.1,x)) (Y a.2.1)):=by
    change IsUnit (hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i (a,x)) (Y a.2.1))
    rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi a
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩]
    exact vectorFieldHessian_isUnit _ β t a.2.2 (k+2) _
  exact hasDerivAt_stationary_inverse_curve U Y a.2.1 m hU
    (hY.differentiableAt (by simp)) hStationary hUnit


end QuantitativePaper
