module
public import QuantitativeFollowup.ConcentratingEnergyRoom

@[expose] public section

/-! Literal affine segment and endpoint preservation in the energy
normalization, with the actual free-measure change included. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB QuantitativePaper
open scoped Topology ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem concentratingEnergyMeasure_affine (μ : Paper.ParisiMeasure)
    (beta a ell kappa tau theta : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32)) (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) :
    concentratingEnergyMeasure μ beta a ell kappa (theta*tau) hbeta ha he hell hkappa
      (concentrating_parameter_product_mem ell kappa tau theta htau htheta) hdensity =
      parisiMix μ (concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity) theta := by
  apply eq_of_parisiCDF_ae_eq
  apply Filter.Eventually.of_forall
  intro x
  have h1 := concentratingEnergyMeasure_profile μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity x
  have h2 := concentratingEnergyMeasure_profile μ beta a ell kappa (theta*tau) hbeta ha he hell hkappa
    (concentrating_parameter_product_mem ell kappa tau theta htau htheta) hdensity x
  rw [parisiCDF_mix _ _ theta x htheta]
  have h3 := congrArg (fun z : ℝ => theta*z) h1
  nlinarith

theorem concentrating_room_full (μ : Paper.ParisiMeasure)
    (beta a ell kappa tau s : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))
    (hs : s ∈ Icc (0 : ℝ) 1) (hfloor : μ ∈ scalarFloor s) :
    ∃ ν : Paper.ParisiMeasure, ν ∈ scalarFloor s ∧
      (∀x, beta*parisiCDF ν x = beta*parisiCDF μ x-tau*concentratingIntervalIncrement a ell x) ∧
      beta*parisiCDF ν 0 = beta*parisiCDF μ 0 ∧
      beta*parisiCDF ν 1 = beta*parisiCDF μ 1 ∧
      beta • ((parisiFreeMeasure ν s).map Subtype.val).toSignedMeasure =
        beta • ((parisiFreeMeasure μ s).map Subtype.val).toSignedMeasure -
          tau • volume.withDensityᵥ (deriv (concentratingIntervalIncrement a ell)) ∧
      ∀theta, ∀htheta : theta ∈ Icc (0 : ℝ) 1,
        concentratingEnergyMeasure μ beta a ell kappa (theta*tau) hbeta ha he hell hkappa
          (concentrating_parameter_product_mem ell kappa tau theta htau htheta) hdensity =
        parisiMix μ ν theta := by
  let ν := concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity
  have hp := concentratingEnergyMeasure_profile μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity
  refine ⟨ν, concentratingEnergyMeasure_preserves_floor μ beta a ell kappa tau s hbeta ha he hell hkappa htau hdensity hfloor,
    hp, ?_, ?_, concentratingEnergyMeasure_free_signed_density μ beta a ell kappa tau s hbeta ha he hell hkappa htau hdensity hs hfloor, ?_⟩
  · rw [hp 0, concentratingIntervalIncrement_zero_outside a ell 0 hell (fun h => by linarith [h.1]),
      mul_zero, sub_zero]
  · rw [hp 1, concentratingIntervalIncrement_zero_outside a ell 1 hell (fun h => by linarith [h.2]),
      mul_zero, sub_zero]
  · intro theta htheta
    exact concentratingEnergyMeasure_affine μ beta a ell kappa tau theta hbeta ha he hell hkappa htau htheta hdensity

end QuantitativeFollowup
