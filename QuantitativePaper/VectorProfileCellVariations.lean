module
public import QuantitativePaper.VectorProfileCellLegendrePDE
public import QuantitativePaper.VectorProfileMixedHessian
public import FourPapersCommon.RealParameterCommutation

@[expose] public section

/-! Genuine local time/profile jets of the actual Legendre potential. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileCellFirstVariation (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : ℝ:=
  deriv (fun θ=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((a.1,θ,a.2.2),m)) a.2.1

def vectorProfileCellSecondVariation (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : ℝ:=
  deriv (deriv (fun θ=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((a.1,θ,a.2.2),m))) a.2.1

def vectorProfileCellB (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : Field n→L[ℝ]Field n:=
  hessianOperator (vectorProfileCellFirstVariation s₀ s₁ β t i a) m

theorem contDiffAt_vectorProfileCellEnergyHessian (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellEnergyHessian s₀ s₁ β t i z.1 z.2) (a,m) :=
  contDiffAt_partial_hessian _ (a,m)
    (contDiffAt_vectorProfileCellEnergyLegendrePotential s₀ s₁ β t hβ ht i hi a hq hθ m hm)

theorem contDiffAt_vectorProfileCellPhysicalHessian (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPhysicalHessian s₀ s₁ β t i z.1 z.2) (a,m) := by
  let A : VectorProfileCellParameter n×Field n→(Field n→L[ℝ]Field n):=
    fun z=>vectorProfileCellEnergyHessian s₀ s₁ β t i z.1 z.2
  have hu : IsUnit (A (a,m)):=vectorProfileEnergyHessian_isUnit s₀ s₁ β t hβ
    (vectorProfileCellOverlap a.1) (k+2) a.2.1 a.2.2 m hm
  obtain ⟨u,he⟩:=hu
  have hInverse : ContDiffAt ℝ ∞ Ring.inverse (A (a,m)) := by
    rw [←he]
    exact contDiffAt_ringInverse ℝ u
  exact ContDiffAt.comp (f := A) (g := Ring.inverse) (a,m) hInverse
    (contDiffAt_vectorProfileCellEnergyHessian s₀ s₁ β t hβ ht i hi a hq hθ m hm)

theorem hasDerivAt_vectorProfileCellPhysicalHessian_profile (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ)
    (a : VectorProfileCellParameter n) (hθ : a.2.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun θ=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (a.1,θ,a.2.2) m)
      (-(vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)*
        vectorProfileCellB s₀ s₁ β t i a m*
        vectorProfileCellPhysicalHessian s₀ s₁ β t i a m) a.2.1 :=
  hasDerivAt_vectorProfilePhysicalHessian_B s₀ s₁ β t hβ ht.le (vectorProfileCellOverlap a.1)
    (k+2) le_rfl a.2.1 hθ a.2.2 m hm

theorem hasDerivAt_deriv_vectorProfileCellPhysicalHessian_profile (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ)
    (a : VectorProfileCellParameter n) (hθ : a.2.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (deriv (fun θ=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (a.1,θ,a.2.2) m))
      ((2 : ℝ) • (vectorProfileCellPhysicalHessian s₀ s₁ β t i a m*
        vectorProfileCellB s₀ s₁ β t i a m*
        vectorProfileCellPhysicalHessian s₀ s₁ β t i a m*
        vectorProfileCellB s₀ s₁ β t i a m*
        vectorProfileCellPhysicalHessian s₀ s₁ β t i a m)-
        vectorProfileCellPhysicalHessian s₀ s₁ β t i a m*
        hessianOperator (vectorProfileCellSecondVariation s₀ s₁ β t i a) m*
        vectorProfileCellPhysicalHessian s₀ s₁ β t i a m) a.2.1 :=
  hasDerivAt_deriv_vectorProfilePhysicalHessian_B_z s₀ s₁ β t hβ ht.le
    (vectorProfileCellOverlap a.1) (k+2) le_rfl a.2.1 hθ a.2.2 m hm

theorem vectorProfileCellSecondVariation_time_commute (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun r=>vectorProfileCellSecondVariation s₀ s₁ β t i (r,a.2) m) a.1=
      deriv (deriv (fun θ=>deriv (fun r=>vectorProfileCellEnergyLegendrePotential
        s₀ s₁ β t i ((r,θ,a.2.2),m)) a.1)) a.2.1 := by
  have hPhi:=contDiffAt_vectorProfileCellEnergyLegendrePotential s₀ s₁ β t hβ ht i hi a hq hθ m hm
  have hU : ContDiffAt ℝ ∞ (fun z : ℝ×ℝ=>vectorProfileCellEnergyLegendrePotential
      s₀ s₁ β t i ((z.1,z.2,a.2.2),m)) (a.1,a.2.1):=
    ContDiffAt.comp (f := fun z : ℝ×ℝ=>((z.1,z.2,a.2.2),m))
      (g := vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i) (a.1,a.2.1) hPhi (by fun_prop)
  exact deriv_real_parameters_commute_third _ a.1 a.2.1 hU

end QuantitativePaper
