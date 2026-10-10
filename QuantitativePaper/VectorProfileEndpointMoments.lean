module
public import QuantitativePaper.VectorProfileEndpointJetInputs
public import QuantitativePaper.VectorProfileOuterWeightedMoments
public import QuantitativePaper.VectorActualExponentialTime
public import QuantitativePaper.VectorFinitePathLaw
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! Actual tilted moments of profile derivatives, with genuine Gaussian
domination for every selected derivative order and power. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem continuous_vectorProfileOuterDerivative_all_theta (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (r : ℕ) (θ : ℝ) :
    Continuous (vectorProfileOuterDerivative (n:=n) s₀ s₁ β t r θ) := by
  have hs : ∀z : ℝ×VectorParameter n,z.1∈Ioo (θ-1) (θ+1) → ContDiffAt ℝ ∞
      (vectorProfileJointFunction s₀ s₁ β t (k+2)) z:=
    fun z _=>(contDiff_vectorProfileJointFunction_all_theta s₀ s₁ β t (k+2)).contDiffAt
  have hc:=continuous_iteratedFDeriv_scalarParameterSlice
    (vectorProfileJointFunction (n:=n) s₀ s₁ β t (k+2)) (θ-1) (θ+1) hs θ (by constructor <;> linarith) r
  have hcomp:=hc.comp (show Continuous (fun p : Couplings n×ℝ=>(p,(0:Field n))) from
    continuous_id.prodMk continuous_const)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r=>ℝ) ℝ
    (fun _ : Fin r=>(1:ℝ))).continuous.comp hcomp

theorem vectorProfileOuterDerivative_exp_bound_all_theta (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (r : ℕ) (θ : ℝ) :
    ∃C R : ℝ,0≤C ∧ 0≤R ∧ ∀p : Couplings n×ℝ,
      ‖vectorProfileOuterDerivative s₀ s₁ β t r θ p‖≤C*Real.exp (R*‖p‖) := by
  let a:=θ-1
  let b:=θ+1
  have hcrop : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith
  obtain ⟨C,D,hC,hD,hj⟩:=exists_vectorProfileJointFunction_common_exp_jets_all_theta
    (n:=n) s₀ s₁ β t r (k+2) a b
  refine ⟨C*Real.exp (D*|θ|),D,mul_nonneg (zero_le_one.trans hC) (Real.exp_pos _).le,hD,?_⟩
  intro p
  have hs : ∀z : ℝ×VectorParameter n,z.1∈Ioo a b → ContDiffAt ℝ ∞
      (vectorProfileJointFunction s₀ s₁ β t (k+2)) z:=
    fun z _=>(contDiff_vectorProfileJointFunction_all_theta s₀ s₁ β t (k+2)).contDiffAt
  have hn : ‖(θ,(p,(0:Field n)))‖≤|θ|+‖p‖:=by
    change max |θ| (max ‖p‖ ‖(0:Field n)‖)≤_
    rw [norm_zero,max_eq_left (norm_nonneg _)]
    exact max_le (by linarith [norm_nonneg p]) (by linarith [abs_nonneg θ])
  have hslice:=norm_iteratedFDeriv_scalarParameterSlice_le
    (vectorProfileJointFunction s₀ s₁ β t (k+2)) a b hs θ hcrop (p,0) r
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hslice
  apply hslice.trans ((hj r le_rfl (θ,p,0) hcrop).trans ?_)
  calc
    C*Real.exp (D*‖(θ,p,(0:Field n))‖)≤C*Real.exp (D*(|θ|+‖p‖)):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hn hD)) (zero_le_one.trans hC)
    _=(C*Real.exp (D*|θ|))*Real.exp (D*‖p‖):=by rw [mul_add,Real.exp_add];ring

theorem integrable_vectorProfileOuterDerivative_pow_closed (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (outer : ℝ) (r m : ℕ)
    (θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    Integrable (fun p : Couplings n×ℝ=>(vectorProfileOuterDerivative s₀ s₁ β t r θ p)^m)
      (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ hθ) β t outer) := by
  obtain ⟨C,R,hC,hR,hb⟩:=vectorProfileOuterDerivative_exp_bound_all_theta (n:=n) s₀ s₁ β t r θ
  have hc:=continuous_vectorProfileOuterDerivative_all_theta (n:=n) s₀ s₁ β t r θ
  apply ((integrable_exp_vectorOuterLaw_norm
    (vectorProfileScheme s₀ s₁ θ hθ) β t outer ((m:ℝ)*R)).const_mul (C^m)).mono'
    (hc.pow m).aestronglyMeasurable
  exact .of_forall fun p=>by
    simp only [Pi.pow_apply]
    rw [norm_pow]
    apply (pow_le_pow_left₀ (norm_nonneg _) (hb p) m).trans_eq
    rw [mul_pow,←Real.exp_nat_mul]
    congr 1
    ring

theorem integrable_vectorProfileOuterWeightedDerivative_pow_closed (s₀ s₁ : RSBScheme k)
    (β t outer : ℝ) (r m : ℕ) (θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    Integrable (fun p : Couplings n×ℝ=>
      Real.exp (outer*vectorProfileRecursion s₀ s₁ β t θ p (k+2) 0)*
        (vectorProfileOuterDerivative s₀ s₁ β t r θ p)^m) (completionLaw n) := by
  have hi:=integrable_vectorOuterWeighted_of_integrable
    (vectorProfileScheme s₀ s₁ θ hθ) β t outer _
    (integrable_vectorProfileOuterDerivative_pow_closed (n:=n) s₀ s₁ β t outer r m θ hθ)
  simp only [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ]
  exact hi

end QuantitativePaper
