module
public import QuantitativeFollowup.NativeCenteredEnergyMomentBounds
public import QuantitativePaper.SKGaussianLipschitz

@[expose] public section

/-! The actual finite-SK centered CGF has its sharp Gaussian Lipschitz bound
at every real tilt; no concentration premise is supplied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem native_centered_energy_cgf_gaussian_bound (n : ℕ) (hn : 2≤n)
    (β : ℝ) (hβ : 0<β) (s : ℝ) :
    centeredEnergyCGF n β s≤(n:ℝ)*s^2/4 := by
  let F:=fun z : SKGaussianSpace n=>energyFreeEnergy n β (skGaussianDisorderLinear n z)
  let L:=Real.sqrt (((n:ℝ)-1)/2)
  have hn0 : 0<n:=by omega
  have hnR : (2:ℝ)≤n:=by exact_mod_cast hn
  have hL : 0<L:=Real.sqrt_pos.mpr (by linarith)
  have hLip:=lipschitz_energyFreeEnergy_gaussian n hn0 β hβ
  have hh:=SYK.product_standardGaussian_mgf_le F L hL hLip s
  have hP : SYK.standardGaussianMeasureOnEuclidean (Edge n)=stdGaussian (SKGaussianSpace n):=
    map_pi_eq_stdGaussian
  rw [hP] at hh
  have hXm : Measurable (energyFreeEnergy n β):=(continuous_logPartition n β).measurable.div_const β
  have hMean : (∫z,F z ∂stdGaussian (SKGaussianSpace n))=
      (∫g,energyFreeEnergy n β g ∂couplingLaw n):=
    (hasLaw_skGaussianDisorder n).integral_comp hXm.aestronglyMeasurable
  have hMom : mgf (fun z=>F z-(∫z,F z ∂stdGaussian (SKGaussianSpace n)))
      (stdGaussian (SKGaussianSpace n)) s=
      mgf (fun g=>energyFreeEnergy n β g-(∫g,energyFreeEnergy n β g ∂couplingLaw n))
        (couplingLaw n) s:=by
    unfold mgf
    rw [hMean]
    exact (hasLaw_skGaussianDisorder n).integral_comp
      (((hXm.sub measurable_const).const_mul s).exp.aestronglyMeasurable)
  rw [hMom] at hh
  have hc:=Real.log_le_log (mgf_pos (integrable_exp_meanCenteredEnergy n β s)) hh
  rw [Real.log_exp] at hc
  have hLsq : L^2=((n:ℝ)-1)/2:=Real.sq_sqrt (by linarith)
  rw [hLsq] at hc
  exact hc.trans (by nlinarith [sq_nonneg s])

end QuantitativeFollowup
