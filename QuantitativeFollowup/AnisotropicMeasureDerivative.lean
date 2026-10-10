module
public import QuantitativeFollowup.AnisotropicDyadicLimit
public import QuantitativeFollowup.AnisotropicParameterHessianBounds
public import FourPapersCommon.UniformDerivativeLimit

@[expose] public section

/-! The constructed arbitrary-profile potential has its genuine continuous
first differential. The finite differentials converge uniformly, using the
profile-independent terminal covariance bound rather than a derivative limit
as a premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000

theorem anisotropicMeasurePotential_derivative_limit (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformly (fun j => fderiv ℝ (anisotropicDyadicPotential D μ j))
      (fderiv ℝ (anisotropicMeasurePotential D μ)) atTop ∧
    ContDiff ℝ 1 (anisotropicMeasurePotential D μ) := by
  obtain ⟨g',hu,hd,hc⟩ := exists_uniform_derivative_limit (anisotropicDyadicPotential D μ)
    (anisotropicMeasurePotential D μ)
    (fun j => (contDiff_anisotropicFinitePotential D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (vectorDyadicIndex j+3)).of_le (by simp))
    (‖anisotropicEnergyMap D‖₊^2)
    (fun j => anisotropicFinitePotential_fderiv_lipschitz D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (vectorDyadicIndex j+3))
    (tendstoUniformly_anisotropicDyadicPotential D μ)
  have he : g'=fderiv ℝ (anisotropicMeasurePotential D μ) := funext fun P => (hd P).fderiv.symm
  rw [he] at hu hc
  exact ⟨hu,contDiff_one_iff_fderiv.mpr ⟨fun P => (hd P).differentiableAt,hc⟩⟩

theorem tendstoUniformly_anisotropicDyadicDifferential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformly (fun j => fderiv ℝ (anisotropicDyadicPotential D μ j))
      (fderiv ℝ (anisotropicMeasurePotential D μ)) atTop :=
  (anisotropicMeasurePotential_derivative_limit D μ).1

theorem contDiff_one_anisotropicMeasurePotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) : ContDiff ℝ 1 (anisotropicMeasurePotential D μ) :=
  (anisotropicMeasurePotential_derivative_limit D μ).2

theorem anisotropicMeasurePotential_fderiv_lipschitz (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    LipschitzWith (‖anisotropicEnergyMap D‖₊^2) (fderiv ℝ (anisotropicMeasurePotential D μ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro P Q
  apply le_of_tendsto (((tendstoUniformly_anisotropicDyadicDifferential D μ).tendsto_at P).dist
    ((tendstoUniformly_anisotropicDyadicDifferential D μ).tendsto_at Q))
  exact Eventually.of_forall fun j =>
    (anisotropicFinitePotential_fderiv_lipschitz D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (vectorDyadicIndex j+3)).dist_le_mul P Q

def anisotropicResponseMap (n : ℕ) : StrongDual ℝ (AnisotropicParameter n) →L[ℝ] Field n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun d => WithLp.toLp 2 (fun i => d (anisotropicCoordinateDirection n i))
      map_add' := by intro d e; ext i; simp
      map_smul' := by intro c d; ext i; simp }

def anisotropicMeasureMagnetization (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (P : AnisotropicParameter n) : Field n :=
  anisotropicResponseMap n (fderiv ℝ (anisotropicMeasurePotential D μ) P)

theorem anisotropicResponseMap_finiteDifferential (D : AnisotropicSpinModel n)
    {k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    anisotropicResponseMap n (fderiv ℝ (anisotropicFinitePotential D s j) P)=
      anisotropicMagnetization D s j P := rfl

theorem tendstoUniformly_anisotropicDyadicMagnetization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformly (fun j => anisotropicMagnetization D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (vectorDyadicIndex j+3))
      (anisotropicMeasureMagnetization D μ) atTop :=
  (anisotropicResponseMap n).uniformContinuous.comp_tendstoUniformly
    (tendstoUniformly_anisotropicDyadicDifferential D μ)

theorem anisotropicMeasureMagnetization_component_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (i : Fin n) :
    |anisotropicMeasureMagnetization D μ P i| ≤ 1 := by
  apply le_of_tendsto
    ((((EuclideanSpace.proj i).continuous.tendsto _).comp
      ((tendstoUniformly_anisotropicDyadicMagnetization D μ).tendsto_at P)).abs)
  exact Eventually.of_forall fun j => anisotropicMagnetization_component_bound D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (vectorDyadicIndex j+3) P i

theorem continuous_anisotropicMeasureMagnetization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) : Continuous (anisotropicMeasureMagnetization D μ) :=
  (anisotropicResponseMap n).continuous.comp
    ((contDiff_one_anisotropicMeasurePotential D μ).continuous_fderiv (by norm_num))

end QuantitativeFollowup
