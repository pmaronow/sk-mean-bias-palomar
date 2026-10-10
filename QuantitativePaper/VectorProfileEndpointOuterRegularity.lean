module
public import QuantitativePaper.VectorProfileEndpointPartition
public import QuantitativePaper.VectorProfileOuterRegularity

@[expose] public section

/-! The outer Gaussian integral is genuinely smooth on a neighbourhood of
both physical endpoints. The mass-zero branch is the actual Gaussian mean. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2200000
variable {n k : ℕ}

theorem integrable_exp_vectorProfileRecursion_all_theta (s₀ s₁ : RSBScheme k)
    (β t outer θ : ℝ) (j : ℕ) :
    Integrable (fun p : Couplings n×ℝ=>Real.exp
      (outer*vectorProfileRecursion s₀ s₁ β t θ p j 0)) (completionLaw n) := by
  have hi := (vectorProfileOuter_exponential_dominatedJets_all_theta (n:=n)
    s₀ s₁ β t outer 0 j (θ-1) (θ+1)).integrable_iteratedDeriv
    (r:=0) le_rfl (by constructor <;> linarith)
  simpa only [iteratedDeriv_zero] using hi

theorem vectorProfileOuterPartition_pos_all_theta (s₀ s₁ : RSBScheme k)
    (β t outer θ : ℝ) :
    0<vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer θ := by
  apply (integral_pos_iff_support_of_nonneg (fun _=>(Real.exp_pos _).le)
    (integrable_exp_vectorProfileRecursion_all_theta s₀ s₁ β t outer θ (k+2))).mpr
  have hs : Function.support (fun p : Couplings n×ℝ=>
      Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0))=univ := by
    ext p
    simp [Function.mem_support,Real.exp_ne_zero]
  rw [hs]
  simp

theorem vectorProfileOuterNormalized_zero_all_theta (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) :
    vectorProfileOuterNormalized (n:=n) s₀ s₁ β t 0 θ=
      ∫p : Couplings n×ℝ,vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0 ∂completionLaw n := by
  have hE : integrableExpSet (fun p : Couplings n×ℝ=>
      vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0) (completionLaw n)=univ:=by
    apply Set.eq_univ_iff_forall.mpr
    intro u
    exact integrable_exp_vectorProfileRecursion_all_theta s₀ s₁ β t u θ (k+2)
  exact normalizedCGF_zero _ _ (by rw [hE,interior_univ];trivial)

theorem contDiff_vectorProfileOuterPartition_all_theta (s₀ s₁ : RSBScheme k)
    (β t outer : ℝ) :
    ContDiff ℝ ∞ (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  apply contDiffAt_infty.mpr
  intro N
  exact ((vectorProfileOuter_exponential_dominatedJets_all_theta (n:=n)
    s₀ s₁ β t outer N (k+2) (θ-1) (θ+1)).contDiffOn isOpen_Ioo θ
      (by constructor <;> linarith)).contDiffAt
        (isOpen_Ioo.mem_nhds (by constructor <;> linarith))

theorem contDiff_vectorProfileOuterNormalized_all_theta (s₀ s₁ : RSBScheme k)
    (β t outer : ℝ) :
    ContDiff ℝ ∞ (vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  by_cases ho : outer=0
  · subst outer
    have he : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t 0=
      (fun θ=>∫p : Couplings n×ℝ,vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0 ∂completionLaw n):=
        funext fun θ=>vectorProfileOuterNormalized_zero_all_theta s₀ s₁ β t θ
    rw [he]
    apply contDiffAt_infty.mpr
    intro N
    exact ((vectorProfileOuter_dominatedJets_all_theta (n:=n)
      s₀ s₁ β t N (k+2) (θ-1) (θ+1)).contDiffOn isOpen_Ioo θ
        (by constructor <;> linarith)).contDiffAt
          (isOpen_Ioo.mem_nhds (by constructor <;> linarith))
  · have he : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer=
      (fun θ=>Real.log (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer θ)/outer):=
        funext fun θ=>vectorProfileOuterNormalized_of_ne s₀ s₁ β t outer θ ho
    rw [he]
    exact ((contDiff_vectorProfileOuterPartition_all_theta s₀ s₁ β t outer).contDiffAt.log
      (vectorProfileOuterPartition_pos_all_theta s₀ s₁ β t outer θ).ne').div_const outer

end QuantitativePaper
