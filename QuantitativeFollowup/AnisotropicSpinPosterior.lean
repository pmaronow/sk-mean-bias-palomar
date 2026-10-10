module
public import QuantitativeFollowup.AnisotropicPosterior
public import QuantitativeFollowup.FinitePosteriorNormalization

@[expose] public section

/-! Actual positive normalized spin-posterior slices of the anisotropic
joint law. Integrability and normalization are consequences of that law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem anisotropicEuclideanJointLaw_eq_Lebesgue_posterior (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) : anisotropicEuclideanJointLaw D s a =
      ((volume : Measure (AnisotropicGaussianSpace n k)).prod
        (Measure.count : Measure (Configuration n))).withDensity
        (fun p => ENNReal.ofReal (Real.exp (-anisotropicPosteriorPotential D s a p.2 p.1))) := by
  have hg : Measurable (fun z : AnisotropicGaussianSpace n k =>
      ENNReal.ofReal (Real.exp (-standardGaussianPotential z))) :=
    (Real.continuous_exp.comp contDiff_standardGaussianPotential.continuous.neg).measurable.ennreal_ofReal
  have hg' : Measurable (fun p : AnisotropicGaussianSpace n k×Configuration n =>
      ENNReal.ofReal (Real.exp (-standardGaussianPotential p.1))) := hg.comp measurable_fst
  have hG : stdGaussian (AnisotropicGaussianSpace n k) =
      volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-standardGaussianPotential z))) := by
    simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] using
      (standardGaussianEuclidean_eq_expDensity (ι := AnisotropicGaussianIndex n k))
  rw [anisotropicEuclideanJointLaw,hG,prod_withDensity_left hg,
    ←withDensity_mul _ hg' (measurable_anisotropicEuclideanDensity D s a)]
  apply withDensity_congr_ae
  exact .of_forall fun ⟨z,σ⟩ => by
    simp only [Pi.mul_apply]
    rw [anisotropicEuclideanDensity_eq_posterior D s a hq,
      ←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
    congr 2
    ring

theorem measurable_anisotropicPosteriorWeight (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : Measurable (fun p : AnisotropicGaussianSpace n k×Configuration n =>
      Real.exp (-anisotropicPosteriorPotential D s a p.2 p.1)) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact (Real.continuous_exp.comp (contDiff_anisotropicPosteriorPotential D s a σ).continuous.neg).measurable

theorem lintegral_anisotropicPosteriorWeight_sum (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) :
    (∑σ : Configuration n,∫⁻z,ENNReal.ofReal (Real.exp (-anisotropicPosteriorPotential D s a σ z)))=1 := by
  have hp := measure_univ (μ := anisotropicEuclideanJointLaw D s a)
  rw [anisotropicEuclideanJointLaw_eq_Lebesgue_posterior D s a hq,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_prod_symm' _ (measurable_anisotropicPosteriorWeight D s a).ennreal_ofReal,
    lintegral_count,tsum_fintype] at hp
  exact hp

theorem integrable_anisotropicPosteriorWeight (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (σ : Configuration n) :
    Integrable (fun z => Real.exp (-anisotropicPosteriorPotential D s a σ z)) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (Real.continuous_exp.comp (contDiff_anisotropicPosteriorPotential D s a σ).continuous.neg).aestronglyMeasurable
    (.of_forall fun z => (Real.exp_pos _).le)).mp
  have hs := lintegral_anisotropicPosteriorWeight_sum D s a hq
  have hb := Finset.single_le_sum (s := (Finset.univ : Finset (Configuration n)))
    (f := fun σ => ∫⁻z,ENNReal.ofReal (Real.exp (-anisotropicPosteriorPotential D s a σ z)))
    (fun σ _ => bot_le) (Finset.mem_univ σ)
  rw [hs] at hb
  exact ne_of_lt (hb.trans_lt ENNReal.one_lt_top)

instance anisotropicGaussianIndex_nonempty [Nonempty (Fin n)] :
    Nonempty (AnisotropicGaussianIndex n k) := ⟨.inr (0,Classical.choice inferInstance)⟩

def anisotropicSpinPosteriorMass (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (σ : Configuration n) : ℝ := posteriorNormalizer (anisotropicPosteriorPotential D s a σ)

def anisotropicSpinPosteriorLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (σ : Configuration n) : Measure (AnisotropicGaussianSpace n k) :=
  normalizedPosteriorMeasure (anisotropicPosteriorPotential D s a σ)

variable [Nonempty (Fin n)]

theorem anisotropicSpinPosteriorMass_pos (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (hq : s.q 1=0) (σ : Configuration n) : 0 < anisotropicSpinPosteriorMass D s a σ :=
  posteriorNormalizer_pos_finite _ (integrable_anisotropicPosteriorWeight D s a hq σ)

theorem anisotropicSpinPosteriorLaw_probability (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (hq : s.q 1=0) (σ : Configuration n) :
    IsProbabilityMeasure (anisotropicSpinPosteriorLaw D s a σ) :=
  normalizedPosteriorMeasure_probability_finite _ (integrable_anisotropicPosteriorWeight D s a hq σ)

theorem anisotropicSpinPosteriorMass_sum (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (hq : s.q 1=0) : (∑σ : Configuration n,anisotropicSpinPosteriorMass D s a σ)=1 := by
  have hs := lintegral_anisotropicPosteriorWeight_sum D s a hq
  have he (σ : Configuration n) : ENNReal.ofReal (anisotropicSpinPosteriorMass D s a σ) =
      ∫⁻z,ENNReal.ofReal (Real.exp (-anisotropicPosteriorPotential D s a σ z)) :=
    ofReal_integral_eq_lintegral_ofReal (integrable_anisotropicPosteriorWeight D s a hq σ)
      (.of_forall fun z => (Real.exp_pos _).le)
  have hn (σ : Configuration n) := (anisotropicSpinPosteriorMass_pos D s a hq σ).le
  apply (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun σ _ => hn σ) zero_le_one).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ => hn σ)]
  simpa only [he,ENNReal.ofReal_one] using hs

theorem posteriorDensityMeasure_anisotropic_eq_mass_smul (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (σ : Configuration n) :
    posteriorDensityMeasure (anisotropicPosteriorPotential D s a σ) =
      ENNReal.ofReal (anisotropicSpinPosteriorMass D s a σ) • anisotropicSpinPosteriorLaw D s a σ := by
  let V := anisotropicPosteriorPotential D s a σ
  have hZ : 0 < posteriorNormalizer V := anisotropicSpinPosteriorMass_pos D s a hq σ
  change volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-V z))) =
    ENNReal.ofReal (posteriorNormalizer V) •
      volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-normalizedPosteriorPotential V z)))
  rw [←withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  exact .of_forall fun z => by
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [exp_neg_normalizedPosteriorPotential V hZ,←ENNReal.ofReal_mul hZ.le]
    congr 1
    field_simp

theorem anisotropicEuclideanJointLaw_eq_spin_mixture (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) : anisotropicEuclideanJointLaw D s a =
      ∑σ : Configuration n,ENNReal.ofReal (anisotropicSpinPosteriorMass D s a σ) •
        (anisotropicSpinPosteriorLaw D s a σ).map (fun z => (z,σ)) := by
  rw [anisotropicEuclideanJointLaw_eq_Lebesgue_posterior D s a hq,
    Measure.count,Measure.prod_sum_right,withDensity_sum,Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Measure.prod_dirac]
  have hm := map_withDensity_pullback (volume : Measure (AnisotropicGaussianSpace n k))
    (fun z => (z,σ)) measurable_prodMk_right
    (fun p => ENNReal.ofReal (Real.exp (-anisotropicPosteriorPotential D s a p.2 p.1)))
    (measurable_anisotropicPosteriorWeight D s a).ennreal_ofReal
  rw [←hm]
  change (posteriorDensityMeasure (anisotropicPosteriorPotential D s a σ)).map (fun z => (z,σ))=_
  rw [posteriorDensityMeasure_anisotropic_eq_mass_smul D s a hq σ,
    Measure.map_smul _ measurable_prodMk_right.aemeasurable]

end QuantitativeFollowup
