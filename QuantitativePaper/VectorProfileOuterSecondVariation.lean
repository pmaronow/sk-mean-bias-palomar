module
public import QuantitativePaper.VectorProfileOuterPartitionDerivatives
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

def vectorProfileOuterNormalized (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) : ℝ:=
  normalizedCGF (completionLaw n)
    (fun p=>vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0) outer

theorem vectorProfileOuterNormalized_of_ne (s₀ s₁ : RSBScheme k)
    (β t outer θ : ℝ) (houter : outer≠0) :
    vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer θ=
      Real.log (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer θ)/outer := by
  rw [vectorProfileOuterNormalized,normalizedCGF_of_ne _ _ houter]
  rfl

theorem vectorProfileOuterNormalized_second_variation (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (outer θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    iteratedDeriv 2 (vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer) θ=
      (∫p : Couplings n×ℝ,vectorProfileOuterDerivative s₀ s₁ β t 2 θ p
        ∂vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer)+
      outer*variance (vectorProfileOuterDerivative (n:=n) s₀ s₁ β t 1 θ)
        (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer) := by
  let a:=θ/2
  let b:=(θ+1)/2
  have ha : 0<a:=by dsimp [a];linarith [hθ.1]
  have hb : b<1:=by dsimp [b];linarith [hθ.2]
  have hx : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith [hθ.1,hθ.2]
  have hphys (y : ℝ) (hy : y∈Ioo a b) : y∈Icc (0:ℝ) 1:=
    ⟨(ha.trans hy.1).le,(hy.2.trans hb).le⟩
  let s:=vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩
  let T:=vectorOuterLaw (n:=n) s β t outer
  let F₁:=vectorProfileOuterDerivative (n:=n) s₀ s₁ β t 1 θ
  let F₂:=vectorProfileOuterDerivative (n:=n) s₀ s₁ β t 2 θ
  by_cases ho : outer=0
  · subst outer
    rw [vectorOuterLaw_zero,zero_mul,add_zero]
    have he : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t 0=ᶠ[𝓝 θ]
        (fun y=>∫p : Couplings n×ℝ,vectorProfileRecursion s₀ s₁ β t y p (k+2) 0 ∂completionLaw n):=by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      have hE : integrableExpSet (fun p : Couplings n×ℝ=>vectorProfileRecursion s₀ s₁ β t y p (k+2) 0)
          (completionLaw n)=univ:=by
        apply Set.eq_univ_iff_forall.mpr
        intro u
        change Integrable (fun p : Couplings n×ℝ=>Real.exp
          (u*vectorProfileRecursion s₀ s₁ β t y p (k+2) 0)) (completionLaw n)
        simp only [vectorProfileRecursion_eq_scheme s₀ s₁ β t y (hphys y hy)]
        exact integrable_exp_vectorRecursion _ β t u (k+2) 0
      exact normalizedCGF_zero _ _ (by rw [hE,interior_univ];trivial)
    rw [he.iteratedDeriv_eq 2]
    exact (vectorProfileOuter_dominatedJets (n:=n) s₀ s₁ β t ht 2 (k+2) a b ha hb).iteratedDeriv_integral
      isOpen_Ioo (le_refl _) hx
  · have hT : IsProbabilityMeasure T:=vectorOuterLaw_probability s β t outer
    letI:=hT
    have hL2 : MemLp F₁ 2 T:=by
      apply (memLp_two_iff_integrable_sq
        (continuous_vectorProfileOuterDerivative (n:=n) s₀ s₁ β t ht 1 θ hθ).aestronglyMeasurable).mpr
      exact integrable_vectorProfileOuterDerivative_pow (n:=n) s₀ s₁ β t ht outer 1 2 θ hθ
    have hvar : variance F₁ T=(∫p,(F₁ p)^2 ∂T)-(∫p,F₁ p ∂T)^2:=variance_eq_sub hL2
    have heq : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer=
        fun y=>Real.log (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer y)/outer:=by
      funext y
      exact vectorProfileOuterNormalized_of_ne s₀ s₁ β t outer y ho
    rw [heq,iteratedDeriv_div_const]
    have hZ : ContDiffOn ℝ 2 (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer) (Ioo a b):=
      (vectorProfileOuter_exponential_dominatedJets (n:=n) s₀ s₁ β t ht outer 2 (k+2)
        a b ha hb).contDiffOn isOpen_Ioo
    have hpos : ∀y∈Ioo a b,0<vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer y:=by
      intro y hy
      rw [vectorProfileOuterPartition_eq s₀ s₁ β t outer y (hphys y hy)]
      exact vectorOuterPartition_pos _ β t outer
    rw [iteratedDeriv_two_log_on_open _ (Ioo a b) isOpen_Ioo hZ hpos hx,
      iteratedDeriv_two_vectorProfileOuterPartition s₀ s₁ β t ht outer θ hθ,
      (hasDerivAt_vectorProfileOuterPartition s₀ s₁ β t ht outer θ hθ).deriv]
    change _=(∫p,F₂ p ∂T)+outer*variance F₁ T
    rw [hvar,integral_vectorOuterLaw s β t outer F₂,
      integral_vectorOuterLaw s β t outer (fun p=>(F₁ p)^2),integral_vectorOuterLaw s β t outer F₁]
    simp only [s,F₁,F₂,vectorProfileRecursion_eq_scheme s₀ s₁ β t θ ⟨hθ.1.le,hθ.2.le⟩,
      vectorProfileOuterPartition_eq s₀ s₁ β t outer θ ⟨hθ.1.le,hθ.2.le⟩]
    field_simp [ho,(vectorOuterPartition_pos (n:=n) s β t outer).ne']
    <;>ring

end QuantitativePaper
