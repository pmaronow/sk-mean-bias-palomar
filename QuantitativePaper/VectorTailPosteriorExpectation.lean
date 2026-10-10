module
public import QuantitativePaper.VectorTailLogDensity
public import QuantitativePaper.VectorTailTranslation
public import QuantitativePaper.FieldSliceJetContinuity
public import QuantitativePaper.VectorGradientBounds
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public section

/-! Actual normalized exponential expectation of the finite tail gradient.
The Gaussian reference law is fixed as the initial field varies; its density
is normalized by the genuine posterior probability construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem contDiff_vectorTailHistoryPotential_initial_noise (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j i : ℕ) :
    ContDiff ℝ ∞ (fun z : Field n × (Fin j → Field n) =>
      vectorTailHistoryPotential s β t p z.1 j i z.2) := by
  unfold vectorTailHistoryPotential historyExtended
  exact (contDiff_vectorRecursion_field s β t p (j-i)).comp
    (contDiff_snd.comp ((contDiff_apply ℝ (VectorState n) _).comp
      (contDiff_vectorHistoryFrom_initial_noise s β t _ p j)))

theorem contDiff_vectorTailPosteriorLogDensity_initial_noise (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (σ : Configuration n) :
    ContDiff ℝ ∞ (fun z : Field n × (Fin j → Field n) =>
      vectorTailPosteriorLogDensity s β t p z.1 j (z.2,σ)) := by
  have hh := contDiff_snd.comp ((contDiff_apply ℝ (VectorState n) (Fin.last j)).comp
    (contDiff_vectorHistoryFrom_initial_noise s β t (k+2-j) p j))
  have hT : ContDiff ℝ ∞ (fun x : Field n => vectorTerminalExponent n β t p x σ) := by
    unfold vectorTerminalExponent fieldDot
    fun_prop
  exact ((hT.comp hh).sub (contDiff_vectorTailHistoryPotential_initial_noise s β t p j j)).add
    (ContDiff.sum fun i _ =>
      contDiff_const.mul ((contDiff_vectorTailHistoryPotential_initial_noise s β t p j (i+1)).sub
        (contDiff_vectorTailHistoryPotential_initial_noise s β t p j i)))

theorem measurable_vectorTailPosteriorLogDensity (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    Measurable (vectorTailPosteriorLogDensity s β t p x j) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact ((contDiff_vectorTailPosteriorLogDensity_initial_noise s β t p j σ).comp
    (contDiff_const.prodMk contDiff_id)).continuous.measurable

theorem vectorTailGaussianPosterior_eq_exp_density (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (hj : j ≤ k+2) :
    vectorTailGaussianPosterior s β t p x j=
      (vectorTailGaussianBase n j).withDensity
        (fun z => ENNReal.ofReal (Real.exp (vectorTailPosteriorLogDensity s β t p x j z))) := by
  unfold vectorTailGaussianPosterior
  congr 1
  exact funext (vectorTailJointDensity_eq_exp_log s β t p x j hj)

theorem lintegral_vectorTailPosterior_exp (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (hj : j ≤ k+2) :
    (∫⁻z,ENNReal.ofReal (Real.exp (vectorTailPosteriorLogDensity s β t p x j z))
      ∂vectorTailGaussianBase n j)=1 := by
  have hh := measure_univ (μ := vectorTailGaussianPosterior s β t p x j)
  rw [vectorTailGaussianPosterior_eq_exp_density s β t p x j hj,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  exact hh

theorem integrable_vectorTailPosterior_exp (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (hj : j ≤ k+2) :
    Integrable (fun z => Real.exp (vectorTailPosteriorLogDensity s β t p x j z))
      (vectorTailGaussianBase n j) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_vectorTailPosteriorLogDensity s β t p x j).exp.aestronglyMeasurable)
    (Eventually.of_forall (fun z => (Real.exp_pos _).le))).mp
  rw [lintegral_vectorTailPosterior_exp s β t p x j hj]
  exact ENNReal.one_ne_top

theorem integral_vectorTailPosterior_exp (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (hj : j ≤ k+2) :
    (∫z,Real.exp (vectorTailPosteriorLogDensity s β t p x j z)
      ∂vectorTailGaussianBase n j)=1 := by
  have hh := ofReal_integral_eq_lintegral_ofReal
    (integrable_vectorTailPosterior_exp s β t p x j hj)
    (Eventually.of_forall (fun z => (Real.exp_pos _).le))
  rw [lintegral_vectorTailPosterior_exp s β t p x j hj] at hh
  have hn := integral_nonneg (μ := vectorTailGaussianBase n j)
    (f := fun z => Real.exp (vectorTailPosteriorLogDensity s β t p x j z)) (fun z => (Real.exp_pos
    (vectorTailPosteriorLogDensity s β t p x j z)).le)
  have h := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal hn,ENNReal.toReal_one] using h

theorem integral_vectorTailPosterior_exp_spin (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (hj : j ≤ k+2)
    (d : Configuration n → ℝ) :
    (∫z,Real.exp (vectorTailPosteriorLogDensity s β t p x j z)*d z.2
      ∂vectorTailGaussianBase n j)=vectorConditionalMean s β t p (fun _ => 0) d j 0 x := by
  have hh := integral_vectorTailPosteriorLaw_spin s β t p x j hj d
  rw [←vectorTailGaussianPosterior_map s β t p x j,
    integral_map (f := fun z : FiniteHistory (VectorState n) j × Configuration n => d z.2)
      (measurable_vectorTailCoordinateJointMap s β t p x j).aemeasurable
      ((measurable_of_finite d).comp measurable_snd).aestronglyMeasurable,
    vectorTailGaussianPosterior_eq_exp_density s β t p x j hj,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_vectorTailPosteriorLogDensity s β t p x j).exp.ennreal_ofReal)
      (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))] at hh
  simpa only [vectorTailCoordinateJointMap,ENNReal.toReal_ofReal (Real.exp_pos _).le,
    smul_eq_mul] using hh

theorem integral_vectorTailPosterior_exp_spinVector (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (hj : j ≤ k+2) :
    (∫z,Real.exp (vectorTailPosteriorLogDensity s β t p x j z) • spinVector z.2
      ∂vectorTailGaussianBase n j)=vectorMagnetization s β t p j x := by
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp]
  · simp only [PiLp.smul_apply,spinVector,smul_eq_mul]
    rw [integral_vectorTailPosterior_exp_spin s β t p x j hj (fun σ => Paper.spinSign (σ i)),
      vectorConditionalMean_zero_eq_response]
    rfl
  · intro l
    apply Integrable.mono' (integrable_vectorTailPosterior_exp s β t p x j hj)
    · exact (((measurable_vectorTailPosteriorLogDensity s β t p x j).exp).mul
        ((measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ l))).comp
          measurable_snd)).aestronglyMeasurable
    · exact Eventually.of_forall (fun z => by
        simp only [PiLp.smul_apply,spinVector,smul_eq_mul,Real.norm_eq_abs,
          abs_mul,abs_of_pos (Real.exp_pos _),Paper.abs_spinSign,mul_one]
        exact le_rfl)

end QuantitativePaper
