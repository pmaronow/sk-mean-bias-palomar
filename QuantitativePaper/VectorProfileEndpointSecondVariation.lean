module
public import QuantitativePaper.VectorProfileEndpointOuterRegularity
public import FourPapersCommon.NormalizedCGF

@[expose] public section

/-! The actual fractional outer second profile variation, including the
ordinary-expectation branch, with its true tilted variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileOuterNormalized_second_variation_closed (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (outer θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    iteratedDeriv 2 (vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer) θ=
      (∫p : Couplings n×ℝ,vectorProfileOuterDerivative s₀ s₁ β t 2 θ p
        ∂vectorOuterLaw (vectorProfileScheme s₀ s₁ θ hθ) β t outer)+
      outer*variance (vectorProfileOuterDerivative (n:=n) s₀ s₁ β t 1 θ)
        (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ hθ) β t outer) := by
  let a:=θ-1
  let b:=θ+1
  have hx : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith
  let s:=vectorProfileScheme s₀ s₁ θ hθ
  let T:=vectorOuterLaw (n:=n) s β t outer
  let F₁:=vectorProfileOuterDerivative (n:=n) s₀ s₁ β t 1 θ
  let F₂:=vectorProfileOuterDerivative (n:=n) s₀ s₁ β t 2 θ
  by_cases ho : outer=0
  · subst outer
    rw [vectorOuterLaw_zero,zero_mul,add_zero]
    have he : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t 0=ᶠ[𝓝 θ]
        (fun y=>∫p : Couplings n×ℝ,vectorProfileRecursion s₀ s₁ β t y p (k+2) 0 ∂completionLaw n):=
      .of_forall (vectorProfileOuterNormalized_zero_all_theta s₀ s₁ β t)
    rw [he.iteratedDeriv_eq 2]
    exact (vectorProfileOuter_dominatedJets_all_theta (n:=n) s₀ s₁ β t 2 (k+2) a b).iteratedDeriv_integral
      isOpen_Ioo (le_refl _) hx
  · have hT : IsProbabilityMeasure T:=vectorOuterLaw_probability s β t outer
    letI:=hT
    have hL2 : MemLp F₁ 2 T:=by
      apply (memLp_two_iff_integrable_sq
        (continuous_vectorProfileOuterDerivative_all_theta (n:=n) s₀ s₁ β t 1 θ).aestronglyMeasurable).mpr
      exact integrable_vectorProfileOuterDerivative_pow_closed (n:=n) s₀ s₁ β t outer 1 2 θ hθ
    have hvar : variance F₁ T=(∫p,(F₁ p)^2 ∂T)-(∫p,F₁ p ∂T)^2:=variance_eq_sub hL2
    have heq : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer=
        fun y=>Real.log (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer y)/outer:=by
      funext y
      exact vectorProfileOuterNormalized_of_ne s₀ s₁ β t outer y ho
    rw [heq,iteratedDeriv_div_const]
    have hZ : ContDiffOn ℝ 2 (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer) (Ioo a b):=
      (vectorProfileOuter_exponential_dominatedJets_all_theta (n:=n) s₀ s₁ β t outer 2 (k+2)
        a b).contDiffOn isOpen_Ioo
    have hpos : ∀y∈Ioo a b,0<vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer y:=
      fun y _=>vectorProfileOuterPartition_pos_all_theta s₀ s₁ β t outer y
    rw [iteratedDeriv_two_log_on_open _ (Ioo a b) isOpen_Ioo hZ hpos hx,
      iteratedDeriv_two_vectorProfileOuterPartition_closed s₀ s₁ β t outer θ hθ,
      (hasDerivAt_vectorProfileOuterPartition_all_theta s₀ s₁ β t outer θ).deriv]
    change _=(∫p,F₂ p ∂T)+outer*variance F₁ T
    rw [hvar,integral_vectorOuterLaw s β t outer F₂,
      integral_vectorOuterLaw s β t outer (fun p=>(F₁ p)^2),integral_vectorOuterLaw s β t outer F₁]
    simp only [s,F₁,F₂,vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ,
      vectorProfileOuterPartition_eq s₀ s₁ β t outer θ hθ]
    field_simp [ho,(vectorOuterPartition_pos (n:=n) s β t outer).ne']
    <;>ring

end QuantitativePaper
