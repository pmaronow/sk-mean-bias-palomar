module
public import QuantitativePaper.VectorProfileOuterMoments

@[expose] public section

/-! Weighted Gaussian integrability follows from the actual normalized tilt. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1800000
variable {n k : ℕ}

theorem integrable_vectorOuterWeighted_of_integrable (s : RSBScheme k) (β t outer : ℝ)
    (F : Couplings n×ℝ→ℝ) (hF : Integrable F (vectorOuterLaw s β t outer)) :
    Integrable (fun p=>Real.exp (outer*vectorRecursion s β t p (k+2) 0)*F p) (completionLaw n) := by
  have hp : ∀p : Couplings n×ℝ,0≤vectorOuterWeight s β t outer p:=
    fun _=>div_nonneg (Real.exp_pos _).le (vectorOuterPartition_pos s β t outer).le
  rw [vectorOuterLaw] at hF
  have hi:=(integrable_withDensity_iff_integrable_smul'
    (measurable_vectorOuterWeight s β t outer).ennreal_ofReal
    (.of_forall fun _=>ENNReal.ofReal_lt_top)).mp hF
  simp_rw [ENNReal.toReal_ofReal (hp _)] at hi
  have hmul:=hi.const_mul (vectorOuterPartition (n:=n) s β t outer)
  convert hmul using 1
  funext p
  simp only [smul_eq_mul,vectorOuterWeight]
  field_simp [(vectorOuterPartition_pos (n:=n) s β t outer).ne']

theorem integrable_vectorProfileOuterWeightedDerivative_pow (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (outer : ℝ) (r m : ℕ)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    Integrable (fun p : Couplings n×ℝ=>
      Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)*
        (vectorProfileOuterDerivative s₀ s₁ β t r θ p)^m) (completionLaw n) := by
  have hi:=integrable_vectorOuterWeighted_of_integrable
    (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer _
    (integrable_vectorProfileOuterDerivative_pow (n:=n) s₀ s₁ β t ht outer r m θ hθ)
  simp only [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ ⟨hθ.1.le,hθ.2.le⟩]
  exact hi

end QuantitativePaper
