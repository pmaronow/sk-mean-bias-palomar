module
public import QuantitativeFollowup.AnisotropicTailResponseMeasurable
public import FourPapersCommon.DerivativeInterpolation

@[expose] public section

/-! CDF-L1 distance controls the genuine arbitrary-profile tail gradient,
uniformly in the restart time and in every disorder/field parameter. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 250000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem norm_anisotropicMeasureTailDifferential_profile_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (anisotropicMeasureTailPotential D μ q) P-
      fderiv ℝ (anisotropicMeasureTailPotential D ν q) P‖≤
      2*(anisotropicProfileStabilityConstant D+‖anisotropicEnergyMap D‖^2)*
        Real.sqrt (Paper.parisiCDFDistance μ ν) := by
  have hb (Q : AnisotropicParameter n) :
      ‖anisotropicMeasureTailPotential D μ q Q-anisotropicMeasureTailPotential D ν q Q‖≤
        anisotropicProfileStabilityConstant D*Paper.parisiCDFDistance μ ν := by
    simpa only [Real.norm_eq_abs] using anisotropicMeasureTailPotential_CDFDistance_abs_sub_le D μ ν q Q
  simpa only [NNReal.coe_pow,coe_nnnorm] using norm_fderiv_sub_le_sqrt_Banach
    (anisotropicMeasureTailPotential D μ q) (anisotropicMeasureTailPotential D ν q)
    (anisotropicMeasureTailPotential_derivative_limit D μ q).2.differentiable_one
    (anisotropicMeasureTailPotential_derivative_limit D ν q).2.differentiable_one
    (‖anisotropicEnergyMap D‖₊^2)
    (anisotropicMeasureTailDifferential_lipschitz D μ q)
    (anisotropicMeasureTailDifferential_lipschitz D ν q)
    (anisotropicProfileStabilityConstant D) (Paper.parisiCDFDistance μ ν)
    (anisotropicProfileStabilityConstant_nonneg D) (Paper.parisiCDFDistance_nonneg μ ν) hb P

def anisotropicProfileGradientError (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) : ℝ :=
  ‖anisotropicResponseMap n‖*
    (2*(anisotropicProfileStabilityConstant D+‖anisotropicEnergyMap D‖^2))*
      Real.sqrt (Paper.parisiCDFDistance μ ν)

theorem anisotropicProfileGradientError_nonneg (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) : 0≤anisotropicProfileGradientError D μ ν := by
  unfold anisotropicProfileGradientError
  positivity [anisotropicProfileStabilityConstant_nonneg D]

theorem norm_anisotropicMeasureTailMagnetization_profile_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    ‖anisotropicMeasureTailMagnetization D μ q P-anisotropicMeasureTailMagnetization D ν q P‖≤
      anisotropicProfileGradientError D μ ν := by
  unfold anisotropicMeasureTailMagnetization
  rw [←map_sub]
  exact ((anisotropicResponseMap n).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (norm_anisotropicMeasureTailDifferential_profile_sub_le D μ ν q P)
      (norm_nonneg _)).trans_eq (by simp only [anisotropicProfileGradientError];ring))

theorem tendsto_anisotropicProfileGradientError {L : Type*} {l : Filter L}
    (D : AnisotropicSpinModel n) (μ : L→Paper.ParisiMeasure) (ν : Paper.ParisiMeasure)
    (hμ : Tendsto (fun j=>Paper.parisiCDFDistance (μ j) ν) l (𝓝 0)) :
    Tendsto (fun j=>anisotropicProfileGradientError D (μ j) ν) l (𝓝 0) := by
  simpa only [anisotropicProfileGradientError,Real.sqrt_zero,mul_zero,Function.comp_def] using
    (Real.continuous_sqrt.tendsto (0:ℝ) |>.comp hμ).const_mul
      (‖anisotropicResponseMap n‖*(2*(anisotropicProfileStabilityConstant D+‖anisotropicEnergyMap D‖^2)))

end QuantitativeFollowup
