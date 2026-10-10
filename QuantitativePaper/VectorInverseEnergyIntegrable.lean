module
public import QuantitativePaper.VectorJointBL
public import QuantitativePaper.VectorPosteriorMetric

@[expose] public section

/-! Integrability of the literal inverse-Hessian energy, proved from the
actual posterior coercivity and actual bounded observable jets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

theorem integrable_vectorSpinPosterior_inverse_energy {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1) (σ : Configuration n)
    (f : VectorGaussianSpace n k → ℝ) (hf : BoundedJets f) :
    Integrable (fun x => inner ℝ (gradient f x)
      ((Ring.inverse (hessianOperator (vectorPosteriorPotential s β t a σ) x)) (gradient f x)))
      (vectorSpinPosteriorLaw s β t a σ) := by
  letI := vectorSpinPosteriorLaw_probability s β t a hq σ
  let V := vectorPosteriorPotential (n := n) s β t a σ
  let A := hessianOperator V
  let b := gradient f
  have hA : ContDiff ℝ 2 A := contDiff_hessianOperator V
    ((contDiff_vectorPosteriorPotential s β t a σ).of_le (by simp))
  have hb : ContDiff ℝ 2 b := contDiff_gradient_two f (hf.1.of_le (by simp))
  have hunit : ∀ x,IsUnit (A x) := vectorPosteriorPotential_hessian_isUnit s β t a ha σ
  have hv := contDiff_inverseFamily A b hA hb hunit
  have he : (fun x => inner ℝ (gradient f x)
      ((Ring.inverse (hessianOperator V x)) (gradient f x)))=
      fun x => inner ℝ (b x) (inverseFamily A b x) := rfl
  rw [he]
  obtain ⟨B,hB,hBound⟩ := hf.2 1
  have hbb : ∀ x,‖b x‖ ≤ B := gradient_norm_bound f B hBound
  have hI (x : VectorGaussianSpace n k) : ‖Ring.inverse (A x)‖ ≤ 1 := by
    have hh := norm_ringInverse_le_of_coercive (A x) 1 (by norm_num) (fun z => by
      rw [one_mul,real_inner_comm,inner_hessianOperator]
      exact vectorPosteriorPotential_hessian_lower s β t a ha σ x z)
    simpa only [inv_one] using hh
  have hvb (x : VectorGaussianSpace n k) : ‖inverseFamily A b x‖ ≤ B := by
    simpa only [one_mul] using inverseFamily_norm_le A b 1 B zero_le_one hI hbb x
  apply Integrable.mono' (integrable_const (B*B))
    ((hb.continuous.inner hv.continuous).aestronglyMeasurable)
  exact .of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hbb x) (hvb x) (norm_nonneg _) hB)

end QuantitativePaper
