module
public import QuantitativePaper.VectorProfileCellVariations
public import FourPapersCommon.AffineSecondDerivative

@[expose] public section

/-! Exact endpoint values of the actual second Legendre profile variation. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellEnergyLegendrePotential_initial_zero (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (i : ℕ) (θ : ℝ) (hθ : θ∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ) :
    vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((0,θ,p),0)=
      -vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0/β := by
  have hq : (0 : ℝ)∈Icc (0 : ℝ) 1:=⟨le_rfl,zero_le_one⟩
  have he:=congrFun (vectorProfileJointPotential_eq_inverseScheme s₀ s₁ β t
    (vectorProfileCellOverlap 0) (k+2) le_rfl θ hθ p) (0 : Field n)
  change vectorProfileTailRecursion s₀ s₁ β t (vectorProfileCellOverlap 0) θ p (k+2) 0=_ at he
  simp only [vectorProfileCellOverlap,projIcc_of_mem zero_le_one hq] at he
  rw [vectorProfileTailRecursion_eq_scheme s₀ s₁ β t 0 θ hθ p,
    vectorTailRecursion_zero _ β t p le_rfl,←vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ p] at he
  change vectorLegendrePotential (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap 0) θ)
    β t p (k+2) 0/β=_
  rw [vectorLegendrePotential_zero]
  simp only [vectorProfileCellOverlap,projIcc_of_mem zero_le_one hq]
  rw [←he]

theorem vectorProfileCellSecondVariation_initial_zero (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (i : ℕ) (θ : ℝ) (hθ : θ∈Ioo (0 : ℝ) 1)
    (p : Couplings n×ℝ) :
    vectorProfileCellSecondVariation s₀ s₁ β t i (0,θ,p) 0=
      -deriv (deriv (fun α=>vectorProfileRecursion s₀ s₁ β t α p (k+2) 0)) θ/β := by
  let f : ℝ→ℝ:=fun α=>vectorProfileRecursion s₀ s₁ β t α p (k+2) 0
  have hf : ContDiffAt ℝ ∞ f θ:=ContDiffAt.comp
    (f := fun α : ℝ=>(α,(p,(0 : Field n))))
    (g := vectorProfileJointFunction s₀ s₁ β t (k+2)) θ
    (contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht (k+2) (θ,p,0) hθ) (by fun_prop)
  have he : (fun α=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((0,α,p),0))=ᶠ[𝓝 θ]
      (fun α=>-f α/β):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with α hα
    exact vectorProfileCellEnergyLegendrePotential_initial_zero s₀ s₁ β t i α
      ⟨hα.1.le,hα.2.le⟩ p
  unfold vectorProfileCellSecondVariation
  rw [he.deriv.deriv_eq]
  have heq : (fun α=>-f α/β)=(fun α=>(-β⁻¹)*f α+0*α+0):=by
    funext α
    simp [div_eq_mul_inv,mul_comm]
  rw [heq,deriv_deriv_affine_add f θ (-β⁻¹) 0 0 hf]
  simp [f,div_eq_mul_inv,mul_comm]

theorem vectorProfileCellEnergyLegendrePotential_terminal (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (i : ℕ) (θ : ℝ) (hθ : θ∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((1,θ,p),m)=
      vectorEnergyLegendrePotential s₀ β t p 0 m := by
  let S:=vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap 1) θ
  have hq : (1 : ℝ)∈Icc (0 : ℝ) 1:=⟨zero_le_one,le_rfl⟩
  have he : vectorRecursion S β t p (k+2)=vectorTerminalPotential n β t p:=by
    rw [←vectorProfileJointPotential_eq_inverseScheme s₀ s₁ β t
      (vectorProfileCellOverlap 1) (k+2) le_rfl θ hθ p]
    change vectorProfileTailRecursion s₀ s₁ β t (vectorProfileCellOverlap 1) θ p (k+2)=_
    simp only [vectorProfileCellOverlap,projIcc_of_mem zero_le_one hq]
    rw [vectorProfileTailRecursion_eq_scheme s₀ s₁ β t 1 θ hθ p,vectorTailRecursion_one _ β t p le_rfl]
  change vectorLegendrePotential S β t p (k+2) m/β=vectorLegendrePotential s₀ β t p 0 m/β
  rw [←vectorLegendreSup_eq_potential S β t p (k+2) m hm,
    ←vectorLegendreSup_eq_potential s₀ β t p 0 m hm]
  unfold vectorLegendreSup
  rw [he]
  rfl

theorem vectorProfileCellSecondVariation_terminal (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (i : ℕ) (θ : ℝ) (hθ : θ∈Ioo (0 : ℝ) 1) (p : Couplings n×ℝ)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    vectorProfileCellSecondVariation s₀ s₁ β t i (1,θ,p) m=0 := by
  have he : (fun α=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((1,α,p),m))=ᶠ[𝓝 θ]
      (fun _=>vectorEnergyLegendrePotential s₀ β t p 0 m):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with α hα
    exact vectorProfileCellEnergyLegendrePotential_terminal s₀ s₁ β t i α
      ⟨hα.1.le,hα.2.le⟩ p m hm
  unfold vectorProfileCellSecondVariation
  rw [he.deriv.deriv_eq]
  simp

end QuantitativePaper
