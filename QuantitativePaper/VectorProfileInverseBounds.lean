module
public import QuantitativePaper.VectorFiniteHessianLower
public import QuantitativePaper.VectorProfileRecursion
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Uniform localization constants for every overlap and every member of an
actual affine finite-profile segment. The positive lower constants are
continuous on a compact parameter square, including endpoint zero masses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem continuous_vectorGaussianNormLaplace (n : ℕ) :
    Continuous (vectorGaussianNormLaplace n) := by
  exact continuous_mgf (fun a=>SYK.integrable_exp_mul_norm (ι := Fin n) a)

theorem continuous_vectorFiniteHessianLowerConstant_family {A : Type*} [TopologicalSpace A]
    (n k : ℕ) (s : A→RSBScheme k) (β t : ℝ)
    (hm : ∀i,Continuous (fun a=> (s a).m i))
    (hq : ∀i,Continuous (fun a=> (s a).q i)) (j : ℕ) :
    Continuous (fun a=>vectorFiniteHessianLowerConstant n (s a) β t j) := by
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
    apply ih.mul
    unfold vectorGaussianLowerCoefficient
    apply Continuous.div
    · apply (continuous_vectorGaussianNormLaplace n).comp
      apply Continuous.neg
      apply Continuous.mul
      · exact ((hm _).abs.mul continuous_const).add continuous_const
      · exact Real.continuous_sqrt.comp
          (continuous_const.mul (continuous_const.mul ((hq _).sub (hq _))))
    · apply (continuous_vectorGaussianNormLaplace n).comp
      exact ((hm _).abs.mul continuous_const).mul
        (Real.continuous_sqrt.comp
          (continuous_const.mul (continuous_const.mul ((hq _).sub (hq _)))))
    · intro a
      exact (vectorGaussianNormLaplace_pos _ _).ne'

def vectorProfileClampedScheme {k : ℕ} (s₀ s₁ : RSBScheme k)
    (z : Paper.Overlap×Paper.Overlap) : RSBScheme (k+1) :=
  vectorClampedScheme (vectorProfileScheme s₀ s₁ z.1 z.1.property) z.2 z.2.property

theorem continuous_vectorProfileClampedScheme_mass {k : ℕ} (s₀ s₁ : RSBScheme k) (i : ℕ) :
    Continuous (fun z=> (vectorProfileClampedScheme s₀ s₁ z).m i) := by
  change Continuous (fun z : Paper.Overlap×Paper.Overlap=>
    if i=0 then 0 else (1-(z.1 : ℝ))*s₀.m (i-1)+(z.1 : ℝ)*s₁.m (i-1))
  by_cases hi:i=0
  · simp only [hi,ite_true];exact continuous_const
  · simp only [ite_eq_right hi];fun_prop

theorem continuous_vectorProfileClampedScheme_overlap {k : ℕ} (s₀ s₁ : RSBScheme k) (i : ℕ) :
    Continuous (fun z=> (vectorProfileClampedScheme s₀ s₁ z).q i) := by
  change Continuous (fun z : Paper.Overlap×Paper.Overlap=>
    if i=0 then 0 else max (z.2 : ℝ) (s₀.q (i-1)))
  by_cases hi:i=0
  · simp only [hi,ite_true];exact continuous_const
  · simp only [ite_eq_right hi];fun_prop

theorem exists_uniform_vectorProfile_inverse_bound {n k : ℕ} (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (j : ℕ) (hj : j≤k+2) :
    ∃D : ℝ,0<D ∧ ∀(θ q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n),
      ‖Ring.inverse (QuantitativeFollowup.hessianOperator
        (vectorProfileTailRecursion s₀ s₁ β t q θ p j) x)‖ ≤
        D*Real.exp (2*(vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖x‖)) := by
  let S:=vectorProfileClampedScheme s₀ s₁
  let C:=fun z : Paper.Overlap×Paper.Overlap=>vectorFiniteHessianLowerConstant n (S z) β t j
  have hC : Continuous C:=continuous_vectorFiniteHessianLowerConstant_family n (k+1) S β t
    (continuous_vectorProfileClampedScheme_mass s₀ s₁)
    (continuous_vectorProfileClampedScheme_overlap s₀ s₁) j
  obtain ⟨z₀,_,hmin⟩:=isCompact_univ.exists_isMinOn
    (univ_nonempty : (univ : Set (Paper.Overlap×Paper.Overlap)).Nonempty) hC.continuousOn
  have hpos : 0<C z₀:=vectorFiniteHessianLowerConstant_pos hn (S z₀) β t j
  refine ⟨(C z₀)⁻¹,inv_pos.mpr hpos,?_⟩
  intro θ q p x
  have heq : vectorProfileTailRecursion s₀ s₁ β t q θ p j=vectorRecursion (S (θ,q)) β t p j :=
    (vectorProfileTailRecursion_eq_scheme s₀ s₁ β t q θ θ.property p j).trans
      (vectorTailRecursion_eq_clamped _ β t q q.property p hj)
  rw [heq]
  change ‖Ring.inverse (vectorFieldHessian (S (θ,q)) β t p j x)‖≤_
  have hi : (C (θ,q))⁻¹≤(C z₀)⁻¹:=by
    simpa only [one_div] using one_div_le_one_div_of_le hpos (hmin (mem_univ (θ,q)))
  exact (norm_inverse_vectorFiniteHessian_le hn (S (θ,q)) β t p j x).trans
    (mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le)

end QuantitativePaper
