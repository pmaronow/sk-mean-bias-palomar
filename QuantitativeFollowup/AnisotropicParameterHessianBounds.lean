module
public import QuantitativeFollowup.AnisotropicCovarianceRegularity
public import QuantitativeFollowup.AnisotropicFiniteConvexity
public import QuantitativeFollowup.CanonicalJetBounds

@[expose] public section

/-! A genuine profile-independent bound on the complete disorder/field
Hessian, obtained from the actual terminal-spin covariance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

theorem anisotropicParameterCovariance_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P v : AnisotropicParameter n) :
    variance (fun σ => anisotropicTerminalLinear D σ v) (anisotropicFiniteSpinKernel D s j P) ≤
      ‖anisotropicEnergyMap D‖^2*‖v‖^2 := by
  have hm : AEStronglyMeasurable (fun σ : Configuration n => anisotropicTerminalLinear D σ v)
      (anisotropicFiniteSpinKernel D s j P) := (measurable_of_finite _).aestronglyMeasurable
  apply (variance_le_expectation_sq hm).trans
  calc
    _ ≤ ∫ _ : Configuration n,‖anisotropicEnergyMap D‖^2*‖v‖^2
        ∂anisotropicFiniteSpinKernel D s j P := by
      apply integral_mono (Integrable.of_finite) (integrable_const _)
      intro σ
      have hb : |anisotropicTerminalLinear D σ v| ≤ ‖anisotropicEnergyMap D‖*‖v‖ := by
        rw [←anisotropicEnergyMap_apply]
        exact (PiLp.norm_apply_le (anisotropicEnergyMap D v) σ).trans
          ((anisotropicEnergyMap D).le_opNorm v)
      simpa only [sq_abs,mul_pow,Pi.pow_apply] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by simp

theorem anisotropicParameterHessian_quadratic_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P v : AnisotropicParameter n) :
    |inner ℝ (hessianOperator (anisotropicFinitePotential D s j) P v) v| ≤
      ‖anisotropicEnergyMap D‖^2*‖v‖^2 := by
  rw [inner_hessianOperator,abs_of_nonneg (anisotropicFinitePotential_hessian_nonneg D s j P v)]
  change directionalHessian (anisotropicFinitePotential D s j) P v ≤ _
  rw [anisotropicFinitePotential_hessian_eq_cascade]
  apply (finiteStateCascadeHessian_covariance_bounds (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (anisotropicSchemeMass_le_one s)
    (anisotropicSchemeMass_antitone_step s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
    (anisotropicEnergyMap D P) (anisotropicEnergyMap D v)).2.trans
  rw [finiteStateCascadeObservableVariance_eq_variance _ _ (anisotropicSchemeMass_nonneg s)]
  simpa only [anisotropicFiniteSpinKernel,Kernel.comap_apply,anisotropicEnergyMap_apply] using
    anisotropicParameterCovariance_bound D s j P v

theorem anisotropicParameterHessian_isSymmetric (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    (hessianOperator (anisotropicFinitePotential D s j) P).IsSymmetric := by
  intro u v
  change inner ℝ (hessianOperator (anisotropicFinitePotential D s j) P u) v=
    inner ℝ u (hessianOperator (anisotropicFinitePotential D s j) P v)
  rw [inner_hessianOperator]
  conv_rhs => rw [real_inner_comm]
  rw [inner_hessianOperator]
  exact ((contDiff_anisotropicFinitePotential D s j).contDiffAt.isSymmSndFDerivAt (by simp)).eq u v

theorem norm_anisotropicParameterHessian_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    ‖hessianOperator (anisotropicFinitePotential D s j) P‖ ≤ ‖anisotropicEnergyMap D‖^2 := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ (anisotropicParameterHessian_isSymmetric D s j P)]
  apply ciSup_le
  intro v
  simp only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real,abs_div,abs_sq]
  have hh := anisotropicParameterHessian_quadratic_bound D s j P v
  by_cases hv : v=0
  · simp [hv]
  · exact (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).mpr hh

theorem norm_anisotropicFinitePotential_secondJet_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    ‖iteratedFDeriv ℝ 2 (anisotropicFinitePotential D s j) P‖ ≤ ‖anisotropicEnergyMap D‖^2 := by
  have he := norm_iteratedFDeriv_hessianOperator (anisotropicFinitePotential D s j)
    ((contDiff_anisotropicFinitePotential D s j).of_le (by simp)) 0 (by omega) P
  simp only [norm_iteratedFDeriv_zero,zero_add] at he
  rw [←he]
  exact norm_anisotropicParameterHessian_le D s j P

theorem anisotropicFinitePotential_fderiv_lipschitz (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) :
    LipschitzWith (‖anisotropicEnergyMap D‖₊^2) (fderiv ℝ (anisotropicFinitePotential D s j)) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_anisotropicFinitePotential D s j).fderiv_right (by simp)).differentiable_one
  intro P
  rw [←NNReal.coe_le_coe,coe_nnnorm,NNReal.coe_pow,coe_nnnorm,
    ←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact norm_anisotropicFinitePotential_secondJet_le D s j P

end QuantitativeFollowup
