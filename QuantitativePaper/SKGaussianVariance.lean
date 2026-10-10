module
public import QuantitativePaper.SKGaussianLipschitz
public import QuantitativePaper.GaussianNormalizedCumulantBound

@[expose] public section

/-! The actual finite-SK Gaussian variance bound in the paper's energy
normalization, including its exact independent half-variance completion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper
open QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1000000

theorem energyFreeEnergy_variance_le (n : ℕ) (hn : 0<n) (β : ℝ) (hβ : 0<β) :
    variance (energyFreeEnergy n β) (couplingLaw n)≤((n:ℝ)-1)/2:=by
  let F:=fun z : SKGaussianSpace n=>energyFreeEnergy n β (skGaussianDisorderLinear n z)
  let L:=Real.sqrt (((n:ℝ)-1)/2)
  have hL : 0≤L:=Real.sqrt_nonneg _
  have hJets : BoundedPositiveJets F:=by
    simpa only [F,energyFreeEnergy,div_eq_mul_inv,mul_comm] using
      (boundedPositiveJets_logPartition_gaussian n β).const_mul β⁻¹
  have hconv : ConvexOn ℝ univ F:=by
    simpa only [F,energyFreeEnergy,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      (convexOn_logPartition_gaussian n β).smul (inv_nonneg.mpr hβ.le)
  have hExp (a : ℝ) : Integrable (fun z=>Real.exp (a*F z)) (stdGaussian (SKGaussianSpace n)):=
    (hasLaw_skGaussianDisorder n).integrable_comp (integrable_exp_energyFreeEnergy n β a)
  have hh:=gaussian_normalizedCGF_deriv_le_half_finite F hJets hconv L hL
    (lipschitz_energyFreeEnergy_gaussian n hn β hβ) hExp 0
  have he : normalizedCGF (stdGaussian (SKGaussianSpace n)) F=normalizedEnergyMoment n β:=
    normalizedCGF_comp_hasLaw (hasLaw_skGaussianDisorder n) _
      ((continuous_logPartition n β).measurable.div_const β)
  rw [he,(hasDerivAt_normalizedEnergyMoment_zero n β).deriv] at hh
  have hnr : (1:ℝ)≤n:=by exact_mod_cast hn
  rw [Real.sq_sqrt (by positivity : 0≤((n:ℝ)-1)/2)] at hh
  linarith

theorem energyCompletedVariance_density_le (n : ℕ) (hn : 0<n) (β : ℝ) (hβ : 0<β) :
    0<(variance (energyFreeEnergy n β) (couplingLaw n)+1/2)/(n:ℝ) ∧
      (variance (energyFreeEnergy n β) (couplingLaw n)+1/2)/(n:ℝ)≤1/2:=by
  have hnr : 0<(n:ℝ):=by exact_mod_cast hn
  refine ⟨div_pos (by positivity [variance_nonneg (energyFreeEnergy n β) (couplingLaw n)]) hnr,?_⟩
  apply (div_le_iff₀ hnr).mpr
  linarith [energyFreeEnergy_variance_le n hn β hβ]

end QuantitativePaper
