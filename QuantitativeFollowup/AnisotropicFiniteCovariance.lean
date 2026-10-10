module
public import QuantitativeFollowup.AnisotropicEnergyRegularity
public import FourPapersCommon.FiniteStateCascadeCovarianceComparison

@[expose] public section

/-! Actual anisotropic terminal-spin covariance and its two-sided comparison
with the field Hessian, for every finite profile and arbitrary Gaussian
coupling scales. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

theorem anisotropicSchemeMass_le_one (s : RSBScheme k) (j : ℕ) :
    anisotropicSchemeMass s j ≤ 1 := s.m_le_one (Nat.sub_le _ _)

theorem anisotropicSchemeMass_antitone_step (s : RSBScheme k) (j : ℕ) :
    anisotropicSchemeMass s (j+1) ≤ anisotropicSchemeMass s j :=
  s.m_mono' (k+1-j) (Nat.sub_le _ _) (k+1-(j+1)) (by omega)

theorem anisotropicEnergyMap_field (D : AnisotropicSpinModel n) (w : Field n)
    (σ : Configuration n) :
    anisotropicEnergyMap D (anisotropicFieldInjection n w) σ=fieldDot w σ := by
  rw [anisotropicEnergyMap_apply,anisotropicFieldInjection_apply,anisotropicTerminalLinear_apply]
  simp [anisotropicHamiltonian]

theorem anisotropicFinitePotential_hessian_eq_cascade (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P v : AnisotropicParameter n) :
    directionalHessian (anisotropicFinitePotential D s j) P v=
      fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
        (anisotropicSchemeMass s) (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j))
        (anisotropicEnergyMap D P) (anisotropicEnergyMap D v) (anisotropicEnergyMap D v) := by
  let F := finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
  have hF := (finiteStateGaussianTerminalCascade_C2_bounds (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j).1
  have he : (fun r : ℝ => anisotropicFinitePotential D s j (P+r • v))=
      fun r => F (anisotropicEnergyMap D P+r • anisotropicEnergyMap D v) := by
    funext r; simp only [anisotropicFinitePotential,map_add,map_smul]; rfl
  rw [directionalHessian_eq_secondDeriv_line _ ((contDiff_anisotropicFinitePotential D s j).of_le (by simp)),he,
    ←directionalHessian_eq_secondDeriv_line F hF]
  rfl

def anisotropicSpinCovarianceEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (w : Field n) : ℝ :=
  variance (fun σ : Configuration n => fieldDot w σ) (anisotropicFiniteSpinKernel D s j P)

theorem anisotropicSpinCovarianceEnergy_eq_cascade (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (w : Field n) :
    anisotropicSpinCovarianceEnergy D s j P w=
      finiteStateCascadeObservableVariance (fun _ : Configuration n => 0) (anisotropicSchemeMass s)
        (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
        (anisotropicEnergyMap D P) (anisotropicEnergyMap D (anisotropicFieldInjection n w)) := by
  rw [finiteStateCascadeObservableVariance_eq_variance _ _ (anisotropicSchemeMass_nonneg s)]
  simp only [anisotropicSpinCovarianceEnergy,anisotropicFiniteSpinKernel,Kernel.comap_apply,
    anisotropicEnergyMap_field]

theorem anisotropicFieldHessian_covariance_bounds (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (w : Field n) :
    finiteStateCascadeDepthMass (anisotropicSchemeMass s) j*anisotropicSpinCovarianceEnergy D s j P w ≤
      inner ℝ w (anisotropicFieldHessian D s j P w) ∧
    inner ℝ w (anisotropicFieldHessian D s j P w) ≤ anisotropicSpinCovarianceEnergy D s j P w := by
  rw [anisotropicFieldHessian_quadratic_eq_parameter,anisotropicFinitePotential_hessian_eq_cascade,
    anisotropicSpinCovarianceEnergy_eq_cascade]
  exact finiteStateCascadeHessian_covariance_bounds _ _ (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_le_one s) (anisotropicSchemeMass_antitone_step s) _ _ _ _

def anisotropicSelfOverlapCovarianceEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) (z : AnisotropicGaussianSpace n k) : ℝ :=
  anisotropicSpinCovarianceEnergy D s (k+2-i) (anisotropicEuclideanStateLinear D s i z)
    (anisotropicSelectedMean D s J i z)

theorem anisotropicSelfOverlapEnergy_le_covariance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) (z : AnisotropicGaussianSpace n k) :
    anisotropicSelfOverlapEnergy D s J i z ≤ anisotropicSelfOverlapCovarianceEnergy D s J i z :=
  (anisotropicFieldHessian_covariance_bounds D s (k+2-i)
    (anisotropicEuclideanStateLinear D s i z) (anisotropicSelectedMean D s J i z)).2

end QuantitativeFollowup
