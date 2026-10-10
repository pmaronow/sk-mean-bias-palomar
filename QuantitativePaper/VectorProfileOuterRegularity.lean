module
public import QuantitativePaper.VectorProfileOuterSecondVariation

@[expose] public section

/-! Actual interior smoothness of the outer normalized Gaussian functional. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
variable {n k : ℕ}

theorem vectorProfileOuterNormalized_zero (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    vectorProfileOuterNormalized (n:=n) s₀ s₁ β t 0 θ=
      ∫p : Couplings n×ℝ,vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0 ∂completionLaw n := by
  have hE : integrableExpSet (fun p : Couplings n×ℝ=>vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)
      (completionLaw n)=univ:=by
    apply Set.eq_univ_iff_forall.mpr
    intro u
    change Integrable (fun p : Couplings n×ℝ=>Real.exp
      (u*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)) (completionLaw n)
    simp only [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ]
    exact integrable_exp_vectorRecursion _ β t u (k+2) 0
  exact normalizedCGF_zero _ _ (by rw [hE,interior_univ];trivial)

theorem contDiffAt_vectorProfileOuterNormalized (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (outer θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer) θ := by
  let a:=θ/2
  let b:=(θ+1)/2
  have ha : 0<a:=by dsimp [a];linarith [hθ.1]
  have hb : b<1:=by dsimp [b];linarith [hθ.2]
  have hx : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith [hθ.1,hθ.2]
  apply contDiffAt_infty.mpr
  intro N
  by_cases ho : outer=0
  · subst outer
    have hs:=(vectorProfileOuter_dominatedJets (n:=n) s₀ s₁ β t ht N (k+2) a b ha hb).contDiffOn
      isOpen_Ioo
    have hh:=(hs θ hx).contDiffAt (isOpen_Ioo.mem_nhds hx)
    apply hh.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact vectorProfileOuterNormalized_zero s₀ s₁ β t y
      ⟨(ha.trans hy.1).le,(hy.2.trans hb).le⟩
  · have he : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer=
        fun y=>Real.log (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer y)/outer:=by
      funext y
      exact vectorProfileOuterNormalized_of_ne s₀ s₁ β t outer y ho
    rw [he]
    have hs:=(vectorProfileOuter_exponential_dominatedJets (n:=n) s₀ s₁ β t ht outer N (k+2) a b ha hb).contDiffOn
      isOpen_Ioo
    have hh:=(hs θ hx).contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hp : 0<vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer θ:=by
      rw [vectorProfileOuterPartition_eq s₀ s₁ β t outer θ ⟨hθ.1.le,hθ.2.le⟩]
      exact vectorOuterPartition_pos _ β t outer
    exact (hh.log hp.ne').div_const outer

end QuantitativePaper
