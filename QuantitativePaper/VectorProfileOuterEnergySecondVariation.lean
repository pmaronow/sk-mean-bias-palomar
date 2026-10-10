module
public import QuantitativePaper.VectorProfileOuterSecondVariation

@[expose] public section

/-! Exact energy-unit normalization of the actual outer profile variation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1600000
variable {n k : ℕ}

def vectorProfileOuterEnergy (s₀ s₁ : RSBScheme k) (β t lam θ : ℝ) : ℝ:=
  vectorProfileOuterNormalized (n:=n) s₀ s₁ β t (lam/β) θ/((n:ℝ)*β)

theorem vectorProfileOuterEnergy_second_variation (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t≤1) (hn : 0<n)
    (lam θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    iteratedDeriv 2 (vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam) θ=
      (∫p : Couplings n×ℝ,vectorProfileOuterDerivative s₀ s₁ β t 2 θ p
        ∂vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t (lam/β))/((n:ℝ)*β)+
      (lam/(n:ℝ))*variance (fun p : Couplings n×ℝ=>
        vectorProfileOuterDerivative s₀ s₁ β t 1 θ p/β)
        (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t (lam/β)) := by
  have hn0 : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  change iteratedDeriv 2 (fun y=>vectorProfileOuterNormalized (n:=n) s₀ s₁ β t (lam/β) y/((n:ℝ)*β)) θ=_
  rw [iteratedDeriv_div_const,vectorProfileOuterNormalized_second_variation s₀ s₁ β t ht (lam/β) θ hθ]
  have he : (fun p : Couplings n×ℝ=>vectorProfileOuterDerivative s₀ s₁ β t 1 θ p/β)=
      (fun p=>β⁻¹*vectorProfileOuterDerivative s₀ s₁ β t 1 θ p):=by
    funext p
    ring
  rw [he,variance_const_mul]
  field_simp [hn0,hβ]
  <;>ring

end QuantitativePaper
