module
public import QuantitativeFollowup.AnisotropicSpinPosterior
public import QuantitativeFollowup.AnisotropicPosteriorJets
public import QuantitativePaper.VectorPosteriorBL

@[expose] public section

/-! Genuine Brascamp--Lieb under the actual anisotropic spin posterior.
Its probability law, smooth jets, and Hessian coercivity are derived from
its Gaussian recursion, including arbitrary signed coupling scales. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ} [Nonempty (Fin n)]

theorem anisotropicSpinPosterior_brascamp_lieb (s : RSBScheme k)
    (D : AnisotropicSpinModel n) (a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1) (σ : Configuration n)
    (f : AnisotropicGaussianSpace n k → ℝ) (hf : BoundedJets f) :
    variance f (anisotropicSpinPosteriorLaw D s a σ) ≤
      ∫ x, inner ℝ (gradient f x)
        ((Ring.inverse (hessianOperator (anisotropicPosteriorPotential D s a σ) x))
          (gradient f x)) ∂anisotropicSpinPosteriorLaw D s a σ := by
  let V := anisotropicPosteriorPotential (n := n) D s a σ
  let VN := normalizedPosteriorPotential V
  have hV : ContDiff ℝ ∞ V := contDiff_anisotropicPosteriorPotential D s a σ
  haveI : Nonempty (AnisotropicGaussianIndex n k) := inferInstance
  haveI : IsProbabilityMeasure (posteriorDensityMeasure VN) :=
    anisotropicSpinPosteriorLaw_probability D s a hq σ
  obtain ⟨A₁,hA₁,ha₁⟩ := exists_anisotropicPosteriorPotential_jet_bound D s a σ (j := 3) (by omega)
  obtain ⟨A₂,hA₂,ha₂⟩ := exists_anisotropicPosteriorPotential_jet_bound D s a σ (j := 4) (by omega)
  obtain ⟨Kf,hKf,hfb⟩ := hf.2 0
  obtain ⟨B₀,hB₀,hb₀⟩ := hf.2 1
  obtain ⟨B₁,hB₁,hb₁⟩ := hf.2 2
  obtain ⟨B₂,hB₂,hb₂⟩ := hf.2 3
  have hhc (x z : AnisotropicGaussianSpace n k) :
      directionalHessian VN x z=directionalHessian V x z := by
    unfold directionalHessian
    have hd : fderiv ℝ VN=fderiv ℝ V := by
      funext y
      exact fderiv_add_const _
    rw [hd]
  have hh := posterior_brascamp_lieb_canonical_of_jet_bounds_finite VN f
    ((hV.add contDiff_const).of_le (by simp)) (hf.1.of_le (by simp))
    1 A₁ A₂ B₀ B₁ B₂ Kf (by norm_num)
    (fun x z => by rw [one_mul,hhc]; exact anisotropicPosteriorPotential_hessian_lower D s a ha σ x z)
    (fun x => by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hfb x)
    (fun x => by rw [iteratedFDeriv_normalizedPosteriorPotential V hV (by omega)]; exact ha₁ x)
    (fun x => by rw [iteratedFDeriv_normalizedPosteriorPotential V hV (by omega)]; exact ha₂ x)
    hb₀ hb₁ hb₂
  simpa only [VN,V,hessianOperator_normalizedPosteriorPotential,
    anisotropicSpinPosteriorLaw,normalizedPosteriorMeasure] using hh

end QuantitativeFollowup
