module
public import QuantitativeFollowup.AnisotropicFiniteCovariance
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

@[expose] public section

/-! Actual terminal covariance energies are continuous and uniformly bounded.
The resulting field Hessian bound is independent of the finite profile. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

theorem anisotropicSpinCovarianceEnergy_nonneg (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (w : Field n) :
    0 ≤ anisotropicSpinCovarianceEnergy D s j P w := variance_nonneg _ _

theorem anisotropicSpinCovarianceEnergy_le (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (w : Field n) :
    anisotropicSpinCovarianceEnergy D s j P w ≤ (n : ℝ)*‖w‖^2 := by
  have hm : AEStronglyMeasurable (fun σ : Configuration n => fieldDot w σ)
      (anisotropicFiniteSpinKernel D s j P) := (measurable_of_finite _).aestronglyMeasurable
  apply (variance_le_expectation_sq hm).trans
  have hi : Integrable (fun σ : Configuration n => (fieldDot w σ)^2)
      (anisotropicFiniteSpinKernel D s j P) := Integrable.of_finite
  calc
    _ ≤ ∫ _ : Configuration n,(n : ℝ)*‖w‖^2 ∂anisotropicFiniteSpinKernel D s j P :=
      integral_mono hi (integrable_const _) (fun σ => by
        have hb := pow_le_pow_left₀ (abs_nonneg _) (abs_fieldDot w σ) 2
        simpa only [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] using hb)
    _ = _ := by simp

theorem continuous_anisotropicSpinCovarianceEnergy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) :
    Continuous (fun p : AnisotropicParameter n×Field n => anisotropicSpinCovarianceEnergy D s j p.1 p.2) := by
  let F := finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0) (anisotropicSchemeMass s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
  let K := fun p : AnisotropicParameter n×Field n => anisotropicEnergyMap D (anisotropicFieldInjection n p.2)
  have hK : Continuous K := (anisotropicEnergyMap D).continuous.comp
    ((anisotropicFieldInjection n).continuous.comp continuous_snd)
  have hKK : Continuous (fun p => finiteStatePointwiseProduct (K p) (K p)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Configuration n => ℝ)).comp
    apply continuous_pi
    intro σ
    exact ((EuclideanSpace.proj σ).continuous.comp hK).mul ((EuclideanSpace.proj σ).continuous.comp hK)
  have hDF := (contDiff_one_finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j).continuous_fderiv (by norm_num)
  have hp : Continuous (fun p : AnisotropicParameter n×Field n => anisotropicEnergyMap D p.1) :=
    (anisotropicEnergyMap D).continuous.comp continuous_fst
  have hd := hDF.comp hp
  have he : (fun p : AnisotropicParameter n×Field n => anisotropicSpinCovarianceEnergy D s j p.1 p.2)=
      fun p => fderiv ℝ F (anisotropicEnergyMap D p.1) (finiteStatePointwiseProduct (K p) (K p))-
        (fderiv ℝ F (anisotropicEnergyMap D p.1) (K p))^2 := by
    funext p
    exact anisotropicSpinCovarianceEnergy_eq_cascade D s j p.1 p.2
  rw [he]
  exact (hd.clm_apply hKK).sub ((hd.clm_apply hK).pow 2)

theorem continuous_anisotropicSelfOverlapCovarianceEnergy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) :
    Continuous (anisotropicSelfOverlapCovarianceEnergy D s J i) := by
  have hp := (anisotropicEuclideanStateLinear D s i).continuous
  have hw : Continuous (fun z : AnisotropicGaussianSpace n k =>
      anisotropicSelectedInsertion J (anisotropicSelectedMagnetization D s J i z)) :=
    (anisotropicSelectedInsertion J).continuous.comp (contDiff_anisotropicSelectedMagnetization D s J i).continuous
  change Continuous (fun z => anisotropicSpinCovarianceEnergy D s (k+2-i)
    (anisotropicEuclideanStateLinear D s i z)
    (anisotropicSelectedInsertion J (anisotropicSelectedMagnetization D s J i z)))
  have hc := (continuous_anisotropicSpinCovarianceEnergy D s (k+2-i)).comp (hp.prodMk hw)
  simpa only [Function.comp_def] using hc

theorem anisotropicSelfOverlapCovarianceEnergy_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) (z : AnisotropicGaussianSpace n k) :
    |anisotropicSelfOverlapCovarianceEnergy D s J i z| ≤
      (n : ℝ)*(‖anisotropicSelectedInsertion J‖*Real.sqrt (J.card : ℝ))^2 := by
  unfold anisotropicSelfOverlapCovarianceEnergy
  rw [abs_of_nonneg (anisotropicSpinCovarianceEnergy_nonneg _ _ _ _ _)]
  apply (anisotropicSpinCovarianceEnergy_le D s _ _ _).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact ((anisotropicSelectedInsertion J).le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (norm_anisotropicSelectedMagnetization_le_sqrt D s J i z) (norm_nonneg _))

theorem anisotropicFieldHessian_isSymmetric (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) : (anisotropicFieldHessian D s j P).IsSymmetric := by
  intro u v
  change inner ℝ (anisotropicFieldHessian D s j P u) v=inner ℝ u (anisotropicFieldHessian D s j P v)
  rw [anisotropicFieldHessian,inner_hessianOperator]
  conv_rhs => rw [real_inner_comm]
  rw [inner_hessianOperator]
  exact ((contDiff_anisotropicTranslatedFieldPotential D s j P).contDiffAt.isSymmSndFDerivAt (by simp)).eq u v

theorem anisotropicFieldHessian_quadratic_bound (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (w : Field n) :
    |inner ℝ (anisotropicFieldHessian D s j P w) w| ≤ (n : ℝ)*‖w‖^2 := by
  rw [real_inner_comm,abs_of_nonneg (anisotropicFieldHessian_quadratic_nonneg D s j P w)]
  exact (anisotropicFieldHessian_covariance_bounds D s j P w).2.trans
    (anisotropicSpinCovarianceEnergy_le D s j P w)

theorem norm_anisotropicFieldHessian_le (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) : ‖anisotropicFieldHessian D s j P‖ ≤ (n : ℝ) := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ (anisotropicFieldHessian_isSymmetric D s j P)]
  apply ciSup_le
  intro w
  simp only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real,abs_div,abs_sq]
  have hh := anisotropicFieldHessian_quadratic_bound D s j P w
  by_cases hw : w=0
  · simp [hw]
  · exact (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw))).mpr hh

end QuantitativeFollowup
