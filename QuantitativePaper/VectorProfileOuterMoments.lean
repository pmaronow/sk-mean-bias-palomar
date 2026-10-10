module
public import QuantitativePaper.VectorProfileOuterJetInputs
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

def vectorProfileOuterDerivative (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (r : ℕ) (θ : ℝ) (p : Couplings n×ℝ) : ℝ:=
  iteratedDeriv r (fun y=>vectorProfileRecursion s₀ s₁ β t y p (k+2) 0) θ

theorem continuous_vectorProfileOuterDerivative (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (r : ℕ) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    Continuous (vectorProfileOuterDerivative (n:=n) s₀ s₁ β t r θ) := by
  have hs : ∀z : ℝ×VectorParameter n,z.1∈Ioo (0:ℝ) 1 → ContDiffAt ℝ ∞
      (vectorProfileJointFunction s₀ s₁ β t (k+2)) z:=
    fun z hz=>contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht (k+2) z hz
  have hc:=continuous_iteratedFDeriv_scalarParameterSlice
    (vectorProfileJointFunction (n:=n) s₀ s₁ β t (k+2)) 0 1 hs θ hθ r
  have hcomp:=hc.comp (show Continuous (fun p : Couplings n×ℝ=>(p,(0:Field n))) from
    continuous_id.prodMk continuous_const)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r=>ℝ) ℝ
    (fun _ : Fin r=>(1:ℝ))).continuous.comp hcomp

theorem vectorProfileOuterDerivative_exp_bound (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (r : ℕ) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ∃C R : ℝ,0≤C ∧ 0≤R ∧ ∀p : Couplings n×ℝ,
      ‖vectorProfileOuterDerivative s₀ s₁ β t r θ p‖≤C*Real.exp (R*‖p‖) := by
  let a:=θ/2
  let b:=(θ+1)/2
  have ha : 0<a:=by dsimp [a];linarith [hθ.1]
  have hb : b<1:=by dsimp [b];linarith [hθ.2]
  have hcrop : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith [hθ.1,hθ.2]
  obtain ⟨C,D,hC,hD,hj⟩:=exists_vectorProfileJointFunction_common_exp_jets
    (n:=n) s₀ s₁ β t ht r (k+2) a b ha hb
  refine ⟨C*Real.exp D,D,mul_nonneg (zero_le_one.trans hC) (Real.exp_pos _).le,hD,?_⟩
  intro p
  have hs : ∀z : ℝ×VectorParameter n,z.1∈Ioo a b → ContDiffAt ℝ ∞
      (vectorProfileJointFunction s₀ s₁ β t (k+2)) z:=
    fun z hz=>contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht (k+2) z
      ⟨ha.trans hz.1,hz.2.trans hb⟩
  have hn : ‖(θ,(p,(0:Field n)))‖≤1+‖p‖:=by
    change max |θ| (max ‖p‖ ‖(0:Field n)‖)≤_
    rw [abs_of_pos hθ.1,norm_zero,max_eq_left (norm_nonneg _)]
    exact max_le (by linarith [hθ.2,norm_nonneg p]) (by linarith)
  have hslice:=norm_iteratedFDeriv_scalarParameterSlice_le
    (vectorProfileJointFunction s₀ s₁ β t (k+2)) a b hs θ hcrop (p,0) r
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hslice
  apply hslice.trans ((hj r le_rfl (θ,p,0) hcrop).trans ?_)
  calc
    C*Real.exp (D*‖(θ,p,(0:Field n))‖)≤C*Real.exp (D*(1+‖p‖)):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hn hD)) (zero_le_one.trans hC)
    _=(C*Real.exp D)*Real.exp (D*‖p‖):=by rw [mul_add,mul_one,Real.exp_add];ring

theorem integrable_vectorProfileOuterDerivative_pow (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (outer : ℝ) (r m : ℕ)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    Integrable (fun p : Couplings n×ℝ=>(vectorProfileOuterDerivative s₀ s₁ β t r θ p)^m)
      (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer) := by
  obtain ⟨C,R,hC,hR,hb⟩:=vectorProfileOuterDerivative_exp_bound (n:=n) s₀ s₁ β t ht r θ hθ
  have hc:=continuous_vectorProfileOuterDerivative (n:=n) s₀ s₁ β t ht r θ hθ
  apply ((integrable_exp_vectorOuterLaw_norm
    (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer ((m:ℝ)*R)).const_mul (C^m)).mono'
    (hc.pow m).aestronglyMeasurable
  exact .of_forall fun p=>by
    simp only [Pi.pow_apply]
    rw [norm_pow]
    apply (pow_le_pow_left₀ (norm_nonneg _) (hb p) m).trans_eq
    rw [mul_pow,←Real.exp_nat_mul]
    congr 1
    ring

theorem integral_vectorOuterLaw (s : RSBScheme k) (β t outer : ℝ)
    (F : Couplings n×ℝ→ℝ) :
    (∫p,F p ∂vectorOuterLaw s β t outer)=
      (∫p,Real.exp (outer*vectorRecursion s β t p (k+2) 0)*F p ∂completionLaw n)/
        vectorOuterPartition (n:=n) s β t outer := by
  have hp : ∀p : Couplings n×ℝ,0≤vectorOuterWeight s β t outer p:=
    fun _=>div_nonneg (Real.exp_pos _).le (vectorOuterPartition_pos s β t outer).le
  rw [vectorOuterLaw,integral_withDensity_eq_integral_toReal_smul
    (measurable_vectorOuterWeight s β t outer).ennreal_ofReal
    (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hp _)]
  simp only [smul_eq_mul,vectorOuterWeight]
  have he : (fun p : Couplings n×ℝ=>
      Real.exp (outer*vectorRecursion s β t p (k+2) 0)/vectorOuterPartition (n:=n) s β t outer*F p)=
    fun p=>(Real.exp (outer*vectorRecursion s β t p (k+2) 0)*F p)/vectorOuterPartition (n:=n) s β t outer:=by
    funext p
    ring
  rw [he,integral_div]

end QuantitativePaper
