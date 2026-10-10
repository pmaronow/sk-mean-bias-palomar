module
public import QuantitativePaper.VectorGauge

@[expose] public section

/-! Finite-spin disintegration of the actual Gaussian-coordinate joint law.
The equal-mean consequence of actual gauge symmetry removes the spin-mixture
term from the variance, rather than postulating its vanishing. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem integral_vectorEuclideanJointLaw_spin {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0)
    (f : Configuration n → VectorGaussianSpace n k → ℝ)
    (hi : ∀σ,Integrable (f σ) (vectorSpinPosteriorLaw s β t a σ)) :
    (∫p,f p.2 p.1 ∂vectorEuclideanJointLaw s β t a)=
      ∑σ : Configuration n,vectorSpinPosteriorMass s β t a σ*
        ∫z,f σ z ∂vectorSpinPosteriorLaw s β t a σ := by
  rw [vectorEuclideanJointLaw_eq_spin_mixture s β t a hq]
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro σ _
    rw [integral_smul_measure,ENNReal.toReal_ofReal (vectorSpinPosteriorMass_pos s β t a hq σ).le]
    have he : MeasurableEmbedding (fun z : VectorGaussianSpace n k => (z,σ)) :=
      MeasurableEmbedding.id.prodMk_right σ
    rw [he.integral_map]
    rfl
  · intro σ _
    have he : MeasurableEmbedding (fun z : VectorGaussianSpace n k => (z,σ)) :=
      MeasurableEmbedding.id.prodMk_right σ
    have himap : Integrable (fun p : VectorGaussianSpace n k × Configuration n => f p.2 p.1)
        ((vectorSpinPosteriorLaw s β t a σ).map (fun z => (z,σ))) :=
      he.integrable_map_iff.mpr (hi σ)
    exact himap.smul_measure ENNReal.ofReal_ne_top

theorem integral_vectorEuclideanJointLaw_invariant {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0)
    (f : Configuration n → VectorGaussianSpace n k → ℝ)
    (hi : ∀σ,Integrable (f σ) (vectorSpinPosteriorLaw s β t a σ))
    (hf : ∀η σ z,f σ (vectorGaussianGauge η z)=f (spinGauge η σ) z)
    (σ : Configuration n) :
    (∫p,f p.2 p.1 ∂vectorEuclideanJointLaw s β t a)=
      ∫z,f σ z ∂vectorSpinPosteriorLaw s β t a σ := by
  rw [integral_vectorEuclideanJointLaw_spin s β t a hq f hi]
  have he (τ : Configuration n) : (∫z,f τ z ∂vectorSpinPosteriorLaw s β t a τ)=
      ∫z,f σ z ∂vectorSpinPosteriorLaw s β t a σ :=
    vectorSpinPosterior_invariant_means s β t a f hf τ σ
  simp_rw [he]
  rw [←Finset.sum_mul,vectorSpinPosteriorMass_sum s β t a hq,one_mul]

/-- For a bounded continuous gauge-covariant observable the full actual joint
variance is exactly the variance in any normalized spin slice. -/
theorem variance_vectorEuclideanJointLaw_invariant {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0)
    (f : Configuration n → VectorGaussianSpace n k → ℝ)
    (hc : ∀σ,Continuous (f σ)) (K : ℝ) (hb : ∀σ z,|f σ z| ≤ K)
    (hf : ∀η σ z,f σ (vectorGaussianGauge η z)=f (spinGauge η σ) z)
    (σ : Configuration n) :
    variance (fun p => f p.2 p.1) (vectorEuclideanJointLaw s β t a)=
      variance (f σ) (vectorSpinPosteriorLaw s β t a σ) := by
  have hi (ρ : Configuration n) : Integrable (f ρ) (vectorSpinPosteriorLaw s β t a ρ) := by
    letI := vectorSpinPosteriorLaw_probability s β t a hq ρ
    apply memLp_one_iff_integrable.mp
    exact MemLp.of_bound (hc ρ).aestronglyMeasurable K
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb ρ z)
  let c := ∫z,f σ z ∂vectorSpinPosteriorLaw s β t a σ
  have hisq (ρ : Configuration n) :
      Integrable (fun z => (f ρ z-c)^2) (vectorSpinPosteriorLaw s β t a ρ) := by
    letI := vectorSpinPosteriorLaw_probability s β t a hq ρ
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound ((hc ρ).sub continuous_const |>.pow 2).aestronglyMeasurable ((K+|c|)^2)
    exact .of_forall fun z => by
      change ‖(f ρ z-c)^2‖ ≤ (K+|c|)^2
      rw [Real.norm_eq_abs,abs_pow]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (abs_sub _ _).trans (add_le_add (hb ρ z) le_rfl)
  have hm : Measurable (fun p : VectorGaussianSpace n k × Configuration n => f p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro ρ
    exact (hc ρ).measurable
  rw [variance_eq_integral hm.aemeasurable,
    integral_vectorEuclideanJointLaw_invariant s β t a hq f hi hf σ,
    variance_eq_integral (hc σ).measurable.aemeasurable]
  exact integral_vectorEuclideanJointLaw_invariant s β t a hq
    (fun ρ z => (f ρ z-c)^2) hisq (fun η ρ z => by rw [hf]) σ

end QuantitativePaper
