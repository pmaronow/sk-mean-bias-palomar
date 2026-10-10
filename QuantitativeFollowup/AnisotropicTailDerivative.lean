module
public import QuantitativeFollowup.AnisotropicTailMeasurability
public import QuantitativeFollowup.AnisotropicMeasureDerivative
public import FourPapersCommon.UniformDerivativeFamily

@[expose] public section

/-! Genuine continuous spatial differentials of the arbitrary-profile tail,
and convergence uniform simultaneously in overlap and disorder/field. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem contDiff_anisotropicDyadicTailPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (j : ℕ) :
    ContDiff ℝ ∞ (anisotropicDyadicTailPotential D μ q j) := by
  unfold anisotropicDyadicTailPotential
  rw [anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
  exact contDiff_anisotropicFinitePotential D _ _

theorem anisotropicDyadicTailPotential_fderiv_lipschitz (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (j : ℕ) :
    LipschitzWith (‖anisotropicEnergyMap D‖₊^2) (fderiv ℝ (anisotropicDyadicTailPotential D μ q j)) := by
  unfold anisotropicDyadicTailPotential
  rw [anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
  exact anisotropicFinitePotential_fderiv_lipschitz D _ _

theorem anisotropicMeasureTailPotential_derivative_limit (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    TendstoUniformly (fun j => fderiv ℝ (anisotropicDyadicTailPotential D μ q j))
      (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) atTop ∧
    ContDiff ℝ 1 (anisotropicMeasureTailPotential D μ q) := by
  obtain ⟨g',hu,hd,hc⟩ := exists_uniform_derivative_limit (fun j => anisotropicDyadicTailPotential D μ q j)
    (anisotropicMeasureTailPotential D μ q)
    (fun j => (contDiff_anisotropicDyadicTailPotential D μ q j).of_le (by simp))
    (‖anisotropicEnergyMap D‖₊^2) (fun j => anisotropicDyadicTailPotential_fderiv_lipschitz D μ q j)
    ((tendstoUniformly_anisotropicDyadicTailPotential D μ).comp (fun P => (q,P)))
  have he : g'=fderiv ℝ (anisotropicMeasureTailPotential D μ q) := funext fun P => (hd P).fderiv.symm
  rw [he] at hu hc
  exact ⟨hu,contDiff_one_iff_fderiv.mpr ⟨fun P => (hd P).differentiableAt,hc⟩⟩

theorem tendstoUniformly_anisotropicDyadicTailDifferential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformly (fun j => fun z : Paper.Overlap×AnisotropicParameter n =>
      fderiv ℝ (anisotropicDyadicTailPotential D μ z.1 j) z.2)
      (fun z => fderiv ℝ (anisotropicMeasureTailPotential D μ z.1) z.2) atTop := by
  apply tendstoUniformly_fderiv_family (fun j q => anisotropicDyadicTailPotential D μ q j)
    (fun z => fderiv ℝ (anisotropicMeasureTailPotential D μ z.1) z.2)
    (fun j q => (contDiff_anisotropicDyadicTailPotential D μ q j).differentiable (by simp))
    (‖anisotropicEnergyMap D‖₊^2) (fun j q => anisotropicDyadicTailPotential_fderiv_lipschitz D μ q j)
    ((tendstoUniformlyOn_univ.mpr (tendstoUniformly_anisotropicDyadicTailPotential D μ)).uniformCauchySeqOn)
  intro z
  exact (anisotropicMeasureTailPotential_derivative_limit D μ z.1).1.tendsto_at z.2

def anisotropicMeasureTailMagnetization (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) : Field n :=
  anisotropicResponseMap n (fderiv ℝ (anisotropicMeasureTailPotential D μ q) P)

theorem tendstoUniformly_anisotropicDyadicTailResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformly (fun j => fun z : Paper.Overlap×AnisotropicParameter n =>
      anisotropicResponseMap n (fderiv ℝ (anisotropicDyadicTailPotential D μ z.1 j) z.2))
      (fun z => anisotropicMeasureTailMagnetization D μ z.1 z.2) atTop :=
  (anisotropicResponseMap n).uniformContinuous.comp_tendstoUniformly
    (tendstoUniformly_anisotropicDyadicTailDifferential D μ)

theorem anisotropicMeasureTailMagnetization_component_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    |anisotropicMeasureTailMagnetization D μ q P i| ≤ 1 := by
  apply le_of_tendsto
    ((((EuclideanSpace.proj i).continuous.tendsto _).comp
      ((tendstoUniformly_anisotropicDyadicTailResponse D μ).tendsto_at (q,P))).abs)
  apply Eventually.of_forall
  intro j
  change |anisotropicResponseMap n (fderiv ℝ (anisotropicDyadicTailPotential D μ q j) P) i| ≤ 1
  unfold anisotropicDyadicTailPotential
  rw [anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
  exact anisotropicMagnetization_component_bound D _ _ P i

theorem norm_anisotropicMeasureTailMagnetization_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖anisotropicMeasureTailMagnetization D μ q P‖ ≤ Real.sqrt (n : ℝ) := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ _ : Fin n,(1 : ℝ) := Finset.sum_le_sum fun i _ => by
      have hb := anisotropicMeasureTailMagnetization_component_bound D μ q P i
      simpa only [Real.norm_eq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by simp

end QuantitativeFollowup
