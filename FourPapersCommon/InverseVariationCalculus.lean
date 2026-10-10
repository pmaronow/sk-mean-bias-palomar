module
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-! Genuine first and second variations of inversion in a Banach algebra.
The formulas preserve the order of all operator factors. -/
noncomputable section
open Filter
open scoped Topology
namespace FourPapersCommon
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    [HasSummableGeomSeries R]

theorem hasDerivAt_ringInverse_comp (A : ℝ→R) (A₁ : R) (a : ℝ)
    (hA : HasDerivAt A A₁ a) (hu : IsUnit (A a)) :
    HasDerivAt (fun θ=>Ring.inverse (A θ))
      (-(Ring.inverse (A a))*A₁*Ring.inverse (A a)) a := by
  obtain ⟨u,he⟩:=hu
  have hf:HasFDerivAt (Ring.inverse : R→R)
      (-ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse (A a)) (Ring.inverse (A a))) (A a) := by
    rw [←he,Ring.inverse_unit]
    exact hasFDerivAt_ringInverse u
  convert hf.comp_hasDerivAt a hA using 1 <;> first | rfl |
    simp only [Function.comp_apply,neg_apply,
      ContinuousLinearMap.mulLeftRight_apply,neg_mul,mul_neg]

theorem hasDerivAt_inverse_firstVariation (A A₁ : ℝ→R) (A₂ : R) (a : ℝ)
    (hA : HasDerivAt A (A₁ a) a) (hA₁ : HasDerivAt A₁ A₂ a) (hu : IsUnit (A a)) :
    HasDerivAt (fun θ=>-(Ring.inverse (A θ))*A₁ θ*Ring.inverse (A θ))
      ((2 : ℝ) • (Ring.inverse (A a)*A₁ a*Ring.inverse (A a)*A₁ a*Ring.inverse (A a))-
        Ring.inverse (A a)*A₂*Ring.inverse (A a)) a := by
  have hH:=hasDerivAt_ringInverse_comp A (A₁ a) a hA hu
  convert (hH.neg.mul hA₁).mul hH using 1
  simp only [Pi.neg_apply, Pi.mul_apply, two_smul, neg_mul, mul_neg]
  noncomm_ring

theorem hasDerivAt_deriv_ringInverse_comp (A A₁ : ℝ→R) (A₂ : R) (a : ℝ)
    (hA : ∀ᶠ θ in 𝓝 a,HasDerivAt A (A₁ θ) θ)
    (hA₁ : HasDerivAt A₁ A₂ a) (hu : ∀ᶠ θ in 𝓝 a,IsUnit (A θ)) :
    HasDerivAt (deriv (fun θ=>Ring.inverse (A θ)))
      ((2 : ℝ) • (Ring.inverse (A a)*A₁ a*Ring.inverse (A a)*A₁ a*Ring.inverse (A a))-
        Ring.inverse (A a)*A₂*Ring.inverse (A a)) a := by
  have hd:=hasDerivAt_inverse_firstVariation A A₁ A₂ a
    hA.self_of_nhds hA₁ hu.self_of_nhds
  apply hd.congr_of_eventuallyEq
  filter_upwards [hA,hu] with θ hθ huθ
  exact (hasDerivAt_ringInverse_comp A (A₁ θ) θ hθ huθ).deriv

end FourPapersCommon
