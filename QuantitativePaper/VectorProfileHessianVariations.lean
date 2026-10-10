module
public import QuantitativePaper.VectorProfileLegendrePotential
public import FourPapersCommon.PartialFDerivSmooth
public import FourPapersCommon.InverseVariationCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Actual first and second profile variations of the inverse Legendre
Hessian. The matrix factors keep their noncommutative order. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileEnergyHessian (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n) : Field n→L[ℝ]Field n:=
  hessianOperator (vectorProfileEnergyLegendrePotential s₀ s₁ β t q j θ p) m

def vectorProfilePhysicalHessian (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n) : Field n→L[ℝ]Field n:=
  Ring.inverse (vectorProfileEnergyHessian s₀ s₁ β t q j θ p m)

theorem vectorProfilePhysicalHessian_eq (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β ≠ 0)
    (q : Paper.Overlap) (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n)
    (hm : m∈vectorOpenSpinCube n) :
    vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m=
      β • vectorFieldHessian (vectorProfileInverseScheme s₀ s₁ q θ) β t p j
        (vectorProfileLegendreField s₀ s₁ β t q j θ p m) :=
  inverse_hessian_vectorEnergyLegendrePotential _ β t hβ p j m hm

theorem vectorProfileEnergyHessian_isUnit (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β ≠ 0)
    (q : Paper.Overlap) (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n)
    (hm : m∈vectorOpenSpinCube n) :
    IsUnit (vectorProfileEnergyHessian s₀ s₁ β t q j θ p m) := by
  change IsUnit (hessianOperator
    (vectorEnergyLegendrePotential (vectorProfileInverseScheme s₀ s₁ q θ) β t p j) m)
  rw [hessian_vectorEnergyLegendrePotential _ β t p j m hm]
  let e:=vectorFieldHessianEquiv (vectorProfileInverseScheme s₀ s₁ q θ) β t p j
    (vectorLegendreField (vectorProfileInverseScheme s₀ s₁ q θ) β t p j m)
  let u : (Field n→L[ℝ]Field n)ˣ:={
    val:=β⁻¹ • (e.symm : Field n→L[ℝ]Field n)
    inv:=β • (e : Field n→L[ℝ]Field n)
    val_inv:=by
      ext w
      simp [ContinuousLinearMap.mul_apply,map_smul,smul_smul,hβ]
    inv_val:=by
      ext w
      simp [ContinuousLinearMap.mul_apply,map_smul,smul_smul,hβ] }
  exact ⟨u,rfl⟩

theorem contDiffAt_vectorProfileEnergyHessian_joint (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (a : VectorProfileParameter n) (hθ : a.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileParameter n×Field n=>
      vectorProfileEnergyHessian s₀ s₁ β t q j z.1.1 z.1.2 z.2) (a,m) :=
  contDiffAt_partial_hessian _ (a,m)
    (contDiffAt_vectorProfileEnergyLegendrePotential_joint s₀ s₁ β t ht q j hj a hθ m hm)

theorem contDiffAt_vectorProfilePhysicalHessian_joint (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (a : VectorProfileParameter n) (hθ : a.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileParameter n×Field n=>
      vectorProfilePhysicalHessian s₀ s₁ β t q j z.1.1 z.1.2 z.2) (a,m) := by
  let A : VectorProfileParameter n×Field n→(Field n→L[ℝ]Field n):=
    fun z=>vectorProfileEnergyHessian s₀ s₁ β t q j z.1.1 z.1.2 z.2
  have hu:=vectorProfileEnergyHessian_isUnit s₀ s₁ β t hβ q j a.1 a.2 m hm
  obtain ⟨u,he⟩:=hu
  have hi : ContDiffAt ℝ ∞ Ring.inverse (A (a,m)) := by
    change ContDiffAt ℝ ∞ Ring.inverse (vectorProfileEnergyHessian s₀ s₁ β t q j a.1 a.2 m)
    rw [←he]
    exact contDiffAt_ringInverse ℝ u
  exact ContDiffAt.comp (f := A) (g := Ring.inverse) (a,m) hi
    (contDiffAt_vectorProfileEnergyHessian_joint s₀ s₁ β t ht q j hj a hθ m hm)

theorem hasDerivAt_vectorProfilePhysicalHessian_parameter (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0 : ℝ) 1) (p : Couplings n×ℝ)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (fun α=>vectorProfilePhysicalHessian s₀ s₁ β t q j α p m)
      (-(vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m)*
        deriv (fun α=>vectorProfileEnergyHessian s₀ s₁ β t q j α p m) θ*
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m) θ := by
  have hPair : ContDiffAt ℝ ∞ (fun α : ℝ=>((α,p),m)) θ:=by fun_prop
  have hA : ContDiffAt ℝ ∞ (fun α=>vectorProfileEnergyHessian s₀ s₁ β t q j α p m) θ:=
    ContDiffAt.comp (f := fun α : ℝ=>((α,p),m))
      (g := fun z : VectorProfileParameter n×Field n=>
        vectorProfileEnergyHessian s₀ s₁ β t q j z.1.1 z.1.2 z.2) θ
      (contDiffAt_vectorProfileEnergyHessian_joint s₀ s₁ β t ht q j hj (θ,p) hθ m hm) hPair
  exact hasDerivAt_ringInverse_comp _ _ θ
    (hA.differentiableAt (by simp)).hasDerivAt
    (vectorProfileEnergyHessian_isUnit s₀ s₁ β t hβ q j θ p m hm)

theorem hasDerivAt_deriv_vectorProfilePhysicalHessian_parameter (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (θ : ℝ) (hθ : θ∈Ioo (0 : ℝ) 1) (p : Couplings n×ℝ)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasDerivAt (deriv (fun α=>vectorProfilePhysicalHessian s₀ s₁ β t q j α p m))
      ((2 : ℝ) • (vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m*
        deriv (fun α=>vectorProfileEnergyHessian s₀ s₁ β t q j α p m) θ*
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m*
        deriv (fun α=>vectorProfileEnergyHessian s₀ s₁ β t q j α p m) θ*
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m)-
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m*
        deriv (deriv (fun α=>vectorProfileEnergyHessian s₀ s₁ β t q j α p m)) θ*
        vectorProfilePhysicalHessian s₀ s₁ β t q j θ p m) θ := by
  let A : ℝ→(Field n→L[ℝ]Field n):=
    fun α=>vectorProfileEnergyHessian s₀ s₁ β t q j α p m
  have hPair : ContDiffAt ℝ ∞ (fun α : ℝ=>((α,p),m)) θ:=by fun_prop
  have hA : ContDiffAt ℝ ∞ A θ:=
    ContDiffAt.comp (f := fun α : ℝ=>((α,p),m))
      (g := fun z : VectorProfileParameter n×Field n=>
        vectorProfileEnergyHessian s₀ s₁ β t q j z.1.1 z.1.2 z.2) θ
      (contDiffAt_vectorProfileEnergyHessian_joint s₀ s₁ β t ht q j hj (θ,p) hθ m hm) hPair
  have hn : ∀ᶠα in 𝓝 θ,α∈Ioo (0 : ℝ) 1:=isOpen_Ioo.mem_nhds hθ
  have hd : ∀ᶠα in 𝓝 θ,HasDerivAt A (deriv A α) α := by
    filter_upwards [hn] with α hα
    have hh:=contDiffAt_vectorProfileEnergyHessian_joint s₀ s₁ β t ht q j hj (α,p) hα m hm
    have hc : ContDiffAt ℝ ∞ A α:=ContDiffAt.comp
      (f := fun α : ℝ=>((α,p),m))
      (g := fun z : VectorProfileParameter n×Field n=>
        vectorProfileEnergyHessian s₀ s₁ β t q j z.1.1 z.1.2 z.2) α hh (by fun_prop)
    exact (hc.differentiableAt (by simp)).hasDerivAt
  have hu : ∀ᶠα in 𝓝 θ,IsUnit (A α) := Eventually.of_forall
    (fun α=>vectorProfileEnergyHessian_isUnit s₀ s₁ β t hβ q j α p m hm)
  have hD : ContDiffAt ℝ ∞ (deriv A) θ:=hA.derivWithin (by simp)
  exact hasDerivAt_deriv_ringInverse_comp A (deriv A) (deriv (deriv A) θ) θ hd
    (hD.differentiableAt (by simp)).hasDerivAt hu

end QuantitativePaper
