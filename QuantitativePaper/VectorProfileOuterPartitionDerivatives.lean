module
public import QuantitativePaper.VectorProfileOuterWeightedMoments
public import QuantitativePaper.ScalarLogSecondDerivative

@[expose] public section

/-! Literal first and second derivatives of the actual outer Gaussian
partition. Differentiation and all split integrals are justified internally. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileOuterPartition (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) : ℝ:=
  ∫p : Couplings n×ℝ,Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0) ∂completionLaw n

theorem vectorProfileOuterPartition_eq (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ)
    (hθ : θ∈Icc (0:ℝ) 1) :
    vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer θ=
      vectorOuterPartition (n:=n) (vectorProfileScheme s₀ s₁ θ hθ) β t outer := by
  simp only [vectorProfileOuterPartition,vectorOuterPartition,vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ]

theorem hasDerivAt_vectorProfileOuterPartition (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (outer θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    HasDerivAt (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer)
      (outer*∫p : Couplings n×ℝ,
        Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)*
          vectorProfileOuterDerivative s₀ s₁ β t 1 θ p ∂completionLaw n) θ := by
  let a:=θ/2
  let b:=(θ+1)/2
  have ha : 0<a:=by dsimp [a];linarith [hθ.1]
  have hb : b<1:=by dsimp [b];linarith [hθ.2]
  have hx : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith [hθ.1,hθ.2]
  have hd:=(vectorProfileOuter_exponential_dominatedJets (n:=n) s₀ s₁ β t ht outer 2 (k+2)
    a b ha hb).hasDerivAt_integral isOpen_Ioo (by norm_num) hx
  change HasDerivAt (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer)
    (∫p : Couplings n×ℝ,deriv (fun y=>Real.exp
      (outer*vectorProfileRecursion s₀ s₁ β t y p (k+2) 0)) θ ∂completionLaw n) θ at hd
  convert hd using 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    dsimp only
    have hs : ContDiffAt ℝ ∞ (fun y=>vectorProfileRecursion s₀ s₁ β t y p (k+2) 0) θ:=
      (contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht (k+2) (θ,p,0) hθ).comp θ
        (contDiffAt_id.prodMk contDiffAt_const)
    rw [((hs.differentiableAt (by simp)).hasDerivAt.const_mul outer).exp.deriv]
    simp only [vectorProfileOuterDerivative,iteratedDeriv_one]
    ring

theorem iteratedDeriv_two_vectorProfileOuterPartition (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (outer θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    iteratedDeriv 2 (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer) θ=
      outer*(∫p : Couplings n×ℝ,
        Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)*
          vectorProfileOuterDerivative s₀ s₁ β t 2 θ p ∂completionLaw n)+
      outer^2*(∫p : Couplings n×ℝ,
        Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)*
          (vectorProfileOuterDerivative s₀ s₁ β t 1 θ p)^2 ∂completionLaw n) := by
  let a:=θ/2
  let b:=(θ+1)/2
  have ha : 0<a:=by dsimp [a];linarith [hθ.1]
  have hb : b<1:=by dsimp [b];linarith [hθ.2]
  have hx : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith [hθ.1,hθ.2]
  have hraw:=vectorProfileOuter_dominatedJets (n:=n) s₀ s₁ β t ht 2 (k+2) a b ha hb
  have he:=(vectorProfileOuter_exponential_dominatedJets (n:=n) s₀ s₁ β t ht outer 2 (k+2)
    a b ha hb).iteratedDeriv_integral isOpen_Ioo (le_refl _) hx
  change iteratedDeriv 2 (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer) θ=_ at he
  rw [he]
  let E:=fun p : Couplings n×ℝ=>Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)
  let F₂:=fun p : Couplings n×ℝ=>vectorProfileOuterDerivative s₀ s₁ β t 2 θ p
  let F₁:=fun p : Couplings n×ℝ=>vectorProfileOuterDerivative s₀ s₁ β t 1 θ p
  have hint : (fun p : Couplings n×ℝ=>iteratedDeriv 2
      (fun y=>Real.exp (outer*vectorProfileRecursion s₀ s₁ β t y p (k+2) 0)) θ)=
      fun p=>outer*(E p*F₂ p)+outer^2*(E p*(F₁ p)^2):=by
    funext p
    rw [iteratedDeriv_two_exp_mul_on_open _ outer (Ioo a b) isOpen_Ioo (hraw.smooth p) hx]
    simp only [E,F₂,F₁,vectorProfileOuterDerivative,iteratedDeriv_one]
    ring
  rw [hint]
  have hi₂ : Integrable (fun p=>E p*F₂ p) (completionLaw n):=by
    simpa only [pow_one] using integrable_vectorProfileOuterWeightedDerivative_pow
      (n:=n) s₀ s₁ β t ht outer 2 1 θ hθ
  have hi₁ : Integrable (fun p=>E p*(F₁ p)^2) (completionLaw n):=
    integrable_vectorProfileOuterWeightedDerivative_pow (n:=n) s₀ s₁ β t ht outer 1 2 θ hθ
  rw [integral_add (hi₂.const_mul outer) (hi₁.const_mul (outer^2)),integral_const_mul,integral_const_mul]

end QuantitativePaper
