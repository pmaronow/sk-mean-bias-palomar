module
public import QuantitativeFollowup.AnisotropicSelfOverlapScore
public import QuantitativeFollowup.AnisotropicPosteriorMetric

@[expose] public section

/-! Integrability of the literal inverse-Hessian energy, proved from the
actual posterior coercivity and actual bounded observable jets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets QuantitativePaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

theorem integrable_anisotropicSpinPosterior_inverse_energy {n k : ℕ} [Nonempty (Fin n)] (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1) (σ : Configuration n)
    (f : AnisotropicGaussianSpace n k → ℝ) (hf : BoundedJets f) :
    Integrable (fun x => inner ℝ (gradient f x)
      ((Ring.inverse (hessianOperator (anisotropicPosteriorPotential D s a σ) x)) (gradient f x)))
      (anisotropicSpinPosteriorLaw D s a σ) := by
  letI := anisotropicSpinPosteriorLaw_probability D s a hq σ
  let V := anisotropicPosteriorPotential (n := n) D s a σ
  let A := hessianOperator V
  let b := gradient f
  have hA : ContDiff ℝ 2 A := contDiff_hessianOperator V
    ((contDiff_anisotropicPosteriorPotential D s a σ).of_le (by simp))
  have hb : ContDiff ℝ 2 b := contDiff_gradient_two f (hf.1.of_le (by simp))
  have hunit : ∀ x,IsUnit (A x) := anisotropicPosteriorPotential_hessian_isUnit D s a ha σ
  have hv := contDiff_inverseFamily A b hA hb hunit
  have he : (fun x => inner ℝ (gradient f x)
      ((Ring.inverse (hessianOperator V x)) (gradient f x)))=
      fun x => inner ℝ (b x) (inverseFamily A b x) := rfl
  rw [he]
  obtain ⟨B,hB,hBound⟩ := hf.2 1
  have hbb : ∀ x,‖b x‖ ≤ B := gradient_norm_bound f B hBound
  have hI (x : AnisotropicGaussianSpace n k) : ‖Ring.inverse (A x)‖ ≤ 1 := by
    have hh := norm_ringInverse_le_of_coercive (A x) 1 (by norm_num) (fun z => by
      rw [one_mul,real_inner_comm,inner_hessianOperator]
      exact anisotropicPosteriorPotential_hessian_lower D s a ha σ x z)
    simpa only [inv_one] using hh
  have hvb (x : AnisotropicGaussianSpace n k) : ‖inverseFamily A b x‖ ≤ B := by
    simpa only [one_mul] using inverseFamily_norm_le A b 1 B zero_le_one hI hbb x
  apply Integrable.mono' (integrable_const (B*B))
    ((hb.continuous.inner hv.continuous).aestronglyMeasurable)
  exact .of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hbb x) (hvb x) (norm_nonneg _) hB)

end QuantitativeFollowup
