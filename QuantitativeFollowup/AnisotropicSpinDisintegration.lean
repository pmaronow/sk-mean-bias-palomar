module
public import QuantitativeFollowup.AnisotropicFiniteGauge

@[expose] public section

/-! Finite-spin disintegration of the actual Gaussian-coordinate joint law.
The equal-mean consequence of actual gauge symmetry removes the spin-mixture
term from the variance, rather than postulating its vanishing. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem integral_anisotropicEuclideanJointLaw_spin {n k : ℕ} [Nonempty (Fin n)] (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (f : Configuration n → AnisotropicGaussianSpace n k → ℝ)
    (hi : ∀σ,Integrable (f σ) (anisotropicSpinPosteriorLaw D s a σ)) :
    (∫p,f p.2 p.1 ∂anisotropicEuclideanJointLaw D s a)=
      ∑σ : Configuration n,anisotropicSpinPosteriorMass D s a σ*
        ∫z,f σ z ∂anisotropicSpinPosteriorLaw D s a σ := by
  rw [anisotropicEuclideanJointLaw_eq_spin_mixture D s a hq]
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro σ _
    rw [integral_smul_measure,ENNReal.toReal_ofReal (anisotropicSpinPosteriorMass_pos D s a hq σ).le]
    have he : MeasurableEmbedding (fun z : AnisotropicGaussianSpace n k => (z,σ)) :=
      MeasurableEmbedding.id.prodMk_right σ
    rw [he.integral_map]
    rfl
  · intro σ _
    have he : MeasurableEmbedding (fun z : AnisotropicGaussianSpace n k => (z,σ)) :=
      MeasurableEmbedding.id.prodMk_right σ
    have himap : Integrable (fun p : AnisotropicGaussianSpace n k × Configuration n => f p.2 p.1)
        ((anisotropicSpinPosteriorLaw D s a σ).map (fun z => (z,σ))) :=
      he.integrable_map_iff.mpr (hi σ)
    exact himap.smul_measure ENNReal.ofReal_ne_top

theorem integral_anisotropicEuclideanJointLaw_invariant {n k : ℕ} [Nonempty (Fin n)] (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (f : Configuration n → AnisotropicGaussianSpace n k → ℝ)
    (hi : ∀σ,Integrable (f σ) (anisotropicSpinPosteriorLaw D s a σ))
    (hf : ∀η σ z,f σ (anisotropicGaussianGauge η z)=f (spinGauge η σ) z)
    (σ : Configuration n) :
    (∫p,f p.2 p.1 ∂anisotropicEuclideanJointLaw D s a)=
      ∫z,f σ z ∂anisotropicSpinPosteriorLaw D s a σ := by
  rw [integral_anisotropicEuclideanJointLaw_spin D s a hq f hi]
  have he (τ : Configuration n) : (∫z,f τ z ∂anisotropicSpinPosteriorLaw D s a τ)=
      ∫z,f σ z ∂anisotropicSpinPosteriorLaw D s a σ :=
    anisotropicSpinPosterior_invariant_means D s a f hf τ σ
  simp_rw [he]
  rw [←Finset.sum_mul,anisotropicSpinPosteriorMass_sum D s a hq,one_mul]

/-- For a bounded continuous gauge-covariant observable the full actual joint
variance is exactly the variance in any normalized spin slice. -/
theorem variance_anisotropicEuclideanJointLaw_invariant {n k : ℕ} [Nonempty (Fin n)] (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (f : Configuration n → AnisotropicGaussianSpace n k → ℝ)
    (hc : ∀σ,Continuous (f σ)) (K : ℝ) (hb : ∀σ z,|f σ z| ≤ K)
    (hf : ∀η σ z,f σ (anisotropicGaussianGauge η z)=f (spinGauge η σ) z)
    (σ : Configuration n) :
    variance (fun p => f p.2 p.1) (anisotropicEuclideanJointLaw D s a)=
      variance (f σ) (anisotropicSpinPosteriorLaw D s a σ) := by
  have hi (ρ : Configuration n) : Integrable (f ρ) (anisotropicSpinPosteriorLaw D s a ρ) := by
    letI := anisotropicSpinPosteriorLaw_probability D s a hq ρ
    apply memLp_one_iff_integrable.mp
    exact MemLp.of_bound (hc ρ).aestronglyMeasurable K
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb ρ z)
  let c := ∫z,f σ z ∂anisotropicSpinPosteriorLaw D s a σ
  have hisq (ρ : Configuration n) :
      Integrable (fun z => (f ρ z-c)^2) (anisotropicSpinPosteriorLaw D s a ρ) := by
    letI := anisotropicSpinPosteriorLaw_probability D s a hq ρ
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound ((hc ρ).sub continuous_const |>.pow 2).aestronglyMeasurable ((K+|c|)^2)
    exact .of_forall fun z => by
      change ‖(f ρ z-c)^2‖ ≤ (K+|c|)^2
      rw [Real.norm_eq_abs,abs_pow]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (abs_sub _ _).trans (add_le_add (hb ρ z) le_rfl)
  have hm : Measurable (fun p : AnisotropicGaussianSpace n k × Configuration n => f p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro ρ
    exact (hc ρ).measurable
  rw [variance_eq_integral hm.aemeasurable,
    integral_anisotropicEuclideanJointLaw_invariant D s a hq f hi hf σ,
    variance_eq_integral (hc σ).measurable.aemeasurable]
  exact integral_anisotropicEuclideanJointLaw_invariant D s a hq
    (fun ρ z => (f ρ z-c)^2) hisq (fun η ρ z => by rw [hf]) σ

end QuantitativeFollowup
