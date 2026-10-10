module
public import QuantitativePaper.VectorProfileEndpointMoments
public import QuantitativePaper.VectorProfileOuterPartitionDerivatives
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

theorem hasDerivAt_vectorProfileOuterPartition_all_theta (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (outer θ : ℝ) :
    HasDerivAt (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer)
      (outer*∫p : Couplings n×ℝ,
        Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)*
          vectorProfileOuterDerivative s₀ s₁ β t 1 θ p ∂completionLaw n) θ := by
  let a:=θ-1
  let b:=θ+1
  have hx : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith
  have hd:=(vectorProfileOuter_exponential_dominatedJets_all_theta (n:=n) s₀ s₁ β t outer 2 (k+2)
    a b).hasDerivAt_integral isOpen_Ioo (by norm_num) hx
  change HasDerivAt (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer)
    (∫p : Couplings n×ℝ,deriv (fun y=>Real.exp
      (outer*vectorProfileRecursion s₀ s₁ β t y p (k+2) 0)) θ ∂completionLaw n) θ at hd
  convert hd using 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    dsimp only
    have hj : ContDiffAt ℝ ∞ (vectorProfileJointFunction (n:=n) s₀ s₁ β t (k+2)) (θ,p,0):=
      (contDiff_vectorProfileJointFunction_all_theta s₀ s₁ β t (k+2)).contDiffAt
    have hs : ContDiffAt ℝ ∞ (fun y=>vectorProfileRecursion s₀ s₁ β t y p (k+2) 0) θ:=
      hj.comp θ (contDiffAt_id.prodMk contDiffAt_const)
    rw [((hs.differentiableAt (by simp)).hasDerivAt.const_mul outer).exp.deriv]
    simp only [vectorProfileOuterDerivative,iteratedDeriv_one]
    ring

theorem iteratedDeriv_two_vectorProfileOuterPartition_closed (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (outer θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    iteratedDeriv 2 (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer) θ=
      outer*(∫p : Couplings n×ℝ,
        Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)*
          vectorProfileOuterDerivative s₀ s₁ β t 2 θ p ∂completionLaw n)+
      outer^2*(∫p : Couplings n×ℝ,
        Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)*
          (vectorProfileOuterDerivative s₀ s₁ β t 1 θ p)^2 ∂completionLaw n) := by
  let a:=θ-1
  let b:=θ+1
  have hx : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith
  have hraw:=vectorProfileOuter_dominatedJets_all_theta (n:=n) s₀ s₁ β t 2 (k+2) a b
  have he:=(vectorProfileOuter_exponential_dominatedJets_all_theta (n:=n) s₀ s₁ β t outer 2 (k+2)
    a b).iteratedDeriv_integral isOpen_Ioo (le_refl _) hx
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
    simpa only [pow_one] using integrable_vectorProfileOuterWeightedDerivative_pow_closed
      (n:=n) s₀ s₁ β t outer 2 1 θ hθ
  have hi₁ : Integrable (fun p=>E p*(F₁ p)^2) (completionLaw n):=
    integrable_vectorProfileOuterWeightedDerivative_pow_closed (n:=n) s₀ s₁ β t outer 1 2 θ hθ
  rw [integral_add (hi₂.const_mul outer) (hi₁.const_mul (outer^2)),integral_const_mul,integral_const_mul]

end QuantitativePaper
